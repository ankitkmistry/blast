use std::{
    cell::{Ref, RefCell},
    collections::{HashMap, HashSet},
    rc::Rc,
    sync::atomic::AtomicU64,
};

use indexmap::IndexMap;
use num_bigint::ToBigInt;
use num_traits::cast::ToPrimitive;

use crate::{
    ast,
 common::{CompileError, CompileResult, HasLineInfo, Layout, LineInfo, Settings, fuzzy_search_best, get_plural},
 context::{self, Context},
 lexer::{Token, TokenKind, TokenValue},
 printer, scope::{self, HasSrcInfo, Payload, State}
};

// TODO: Counters should not be global
// It should be a member of scope
static UNIQUE_COUNTER: AtomicU64 = AtomicU64::new(0);
static BLOCK_COUNTER: AtomicU64 = AtomicU64::new(0);
static LOOP_COUNTER: AtomicU64 = AtomicU64::new(0);

pub struct SemResult<'a> {
    pub roots: HashMap<String, Rc<RefCell<scope::Scope<'a>>>>,
    pub warnings: Vec<CompileError>,
}

pub struct Analyzer<'a> {
    roots: HashMap<String, Rc<RefCell<scope::Scope<'a>>>>,
    cur_scope: Rc<RefCell<scope::Scope<'a>>>,
    settings: Settings,
    type_int: context::Type<'a>,
    type_uint: context::Type<'a>,
    type_isize: context::Type<'a>,
    type_usize: context::Type<'a>,
    saved_errs: Vec<CompileError>,
    warnings: Vec<CompileError>,
}

impl<'a> Analyzer<'a> {
    pub fn new(settings: Settings, file_path: &str, name: &str, root: &'a ast::Object) -> Self {
        let scope = scope::Scope::new_root(file_path, root);
        let mut roots = HashMap::new();
        roots.insert(name.to_owned(), Rc::clone(&scope));
        let (type_int, type_uint) = match settings.register_size {
            1 => (context::Type::Int8, context::Type::Uint8),
            2 => (context::Type::Int16, context::Type::Uint16),
            4 => (context::Type::Int32, context::Type::Uint32),
            8 => (context::Type::Int64, context::Type::Uint64),
            16 => (context::Type::Int128, context::Type::Uint128),
            _ => panic!("invalid register size"),
        };
        let (type_isize, type_usize) = match settings.pointer_size {
            1 => (context::Type::Int8, context::Type::Uint8),
            2 => (context::Type::Int16, context::Type::Uint16),
            4 => (context::Type::Int32, context::Type::Uint32),
            8 => (context::Type::Int64, context::Type::Uint64),
            16 => (context::Type::Int128, context::Type::Uint128),
            _ => panic!("invalid register size"),
        };
        Self {
            roots,
            cur_scope: scope,
            settings,
            type_int,
            type_uint,
            type_isize,
            type_usize,
            saved_errs: Vec::new(),
            warnings: Vec::new(),
        }
    }

    pub fn analyze(mut self) -> CompileResult<SemResult<'a>> {
        let result = self.sem_analysis();
        if let Err(err) = result {
            // If there are any accumulated errors return them
            Err(CompileError::Errors(self.saved_errs)
                .chain(err)
                .chain(CompileError::Errors(self.warnings)))
        } else {
            let sem_result = SemResult {
                roots: self.roots,
                warnings: self.warnings,
            };
            Ok(sem_result)
        }
    }

    fn sem_analysis(&mut self) -> CompileResult<()> {
        let mut final_decls = Vec::new();
        // Accumulate top level decls from all roots
        for root_rc in self.roots.values() {
            let mut root = root_rc.borrow_mut();
            match &root.state {
                State::NotVisited(scope_node) => match scope_node {
                    scope::ScopeNode::Object(object) => match object {
                        ast::Object::Module { line_info: _, decls } => {
                            for decl in decls {
                                final_decls.push(decl);
                            }
                            root.state = State::Visited(Context::from_module(root_rc));
                        }
                        _ => unreachable!("not supposed to happen"),
                    },
                    _ => unreachable!("not supposed to happen"),
                },
                _ => unreachable!("not supposed to happen"),
            }
        }
        // Generate all modules
        for decl in &final_decls {
            if let ast::Decl::Decl {
                name: _,
                taipe: _,
                eq_token: _,
                object: Some(object),
            } = decl
            {
                match object {
                    ast::Object::ExternModule { line_info, value } => {
                        todo!("extern modules are not supported yet")
                    }
                    ast::Object::Module { line_info: _, decls: _ } => {
                        self.visit_decl(decl, false)?;
                    }
                    _ => {}
                }
            }
        }
        // Accumulate errors from predeclaring decls
        let mut errs = Vec::new();
        for decl in &final_decls {
            if let Err(err) = self.pre_declare_decl(decl) {
                errs.push(err);
            }
        }
        // Return errors if any
        if !errs.is_empty() {
            return Err(CompileError::Errors(errs));
        }
        // Finally visit them
        for decl in final_decls {
            self.visit_decl(&decl, true)?;
        }
        Ok(())
    }

    fn pre_declare_decl(&mut self, decl: &'a ast::Decl) -> CompileResult<()> {
        match decl {
            ast::Decl::Decl {
                name,
                taipe: _,
                eq_token: _,
                object,
            } => {
                if let Some(object) = object {
                    self.declare_sym_with_value(decl, &name, object)?
                } else {
                    self.declare_sym(decl, &name)?
                }
            }
            ast::Decl::Using { line_info: _, items: _ } => todo!("import statements are not yet supported"),
        };
        Ok(())
    }

    fn pre_declare_decls(&mut self, decls: &'a [ast::Decl]) -> CompileResult<()> {
        // Pre declare all the symbols without visiting
        // So that symbols that are declared later
        // are also accessible before they are introduced.
        //
        // We also accumalate the errors.
        let mut errs = Vec::new();
        for decl in decls {
            if let Err(err) = self.pre_declare_decl(decl) {
                errs.push(err);
            }
        }
        if !errs.is_empty() {
            return Err(CompileError::Errors(errs));
        }
        Ok(())
    }

    fn declare_sym(&mut self, node: &'a ast::Decl, name: &Token) -> CompileResult<Rc<RefCell<scope::Scope<'a>>>> {
        // Check for redeclaration
        // Except for '_' declarations
        if name.kind != TokenKind::Underscore
            && let Some(prev_scope_ref) = self.get_cur_scope().children.get(&name.text)
        {
            // No module then error
            return Err(self
                .make_err("redeclaration of symbol", name)
                .chain(self.make_note("already declared here", &prev_scope_ref.borrow())));
        }

        let sym_name = if name.kind == TokenKind::Underscore {
            format!(
                "unnamed{}$",
                UNIQUE_COUNTER.fetch_add(1, std::sync::atomic::Ordering::SeqCst)
            )
        } else {
            name.text.clone()
        };

        Ok(scope::Scope::add_child(
            &self.cur_scope,
            &sym_name,
            scope::State::NotVisited(scope::ScopeNode::Decl(node)),
            name,
        ))
    }

    fn declare_sym_ex(
        &mut self,
        state: scope::State<'a>,
        name: &Token,
    ) -> CompileResult<Rc<RefCell<scope::Scope<'a>>>> {
        // Check for redeclaration
        // Except for '_' declarations
        if name.kind != TokenKind::Underscore
            && let Some(prev_scope_ref) = self.get_cur_scope().children.get(&name.text)
        {
            // No module then error
            return Err(self
                .make_err("redeclaration of symbol", name)
                .chain(self.make_note("already declared here", &prev_scope_ref.borrow())));
        }

        let sym_name = if name.kind == TokenKind::Underscore {
            format!(
                "unnamed{}$",
                UNIQUE_COUNTER.fetch_add(1, std::sync::atomic::Ordering::SeqCst)
            )
        } else {
            name.text.clone()
        };

        Ok(scope::Scope::add_child(&self.cur_scope, &sym_name, state, name))
    }

    fn declare_sym_with_value(
        &mut self,
        node: &'a ast::Decl,
        name: &Token,
        object: &'a ast::Object,
    ) -> CompileResult<Rc<RefCell<scope::Scope<'a>>>> {
        // Check for redeclaration
        // Except for '_' declarations
        if name.kind != TokenKind::Underscore
            && let Some(prev_scope_ref) = self.get_cur_scope().children.get(&name.text)
        {
            let prev_scope = prev_scope_ref.borrow();
            if object.is_module() {
                // Allow merging module declarations
                if let scope::State::Visited(prev_ctx) = &prev_scope.state {
                    if prev_ctx.taipe.is_module() {
                        return Ok(Rc::clone(prev_scope_ref));
                    }
                }
                if let scope::State::NotVisited(prev_decl) = &prev_scope.state
                    && let scope::ScopeNode::Decl(prev_decl) = prev_decl
                    && let ast::Decl::Decl {
                        name: _,
                        taipe: _,
                        eq_token: _,
                        object: prev_object,
                    } = prev_decl
                    && let Some(prev_object) = prev_object
                    && prev_object.is_module()
                {
                    return Ok(Rc::clone(prev_scope_ref));
                }
            }
            // No module then error
            return Err(self
                .make_err("redeclaration of symbol", name)
                .chain(self.make_note("already declared here", &prev_scope)));
        }

        let sym_name = if name.kind == TokenKind::Underscore {
            format!(
                "unnamed{}$",
                UNIQUE_COUNTER.fetch_add(1, std::sync::atomic::Ordering::SeqCst)
            )
        } else {
            name.text.clone()
        };

        Ok(scope::Scope::add_child(
            &self.cur_scope,
            &sym_name,
            scope::State::NotVisited(scope::ScopeNode::Decl(node)),
            name,
        ))
    }

    fn declare_field(&mut self, field: &'a ast::Field, name: &Token) -> CompileResult<Rc<RefCell<scope::Scope<'a>>>> {
        // Check for redeclaration
        // Except for '_' declarations
        if name.kind != TokenKind::Underscore
            && let Some(prev_scope_ref) = self.get_cur_scope().children.get(&name.text)
        {
            // No module then error
            return Err(self
                .make_err("redeclaration of symbol", name)
                .chain(self.make_note("already declared here", &prev_scope_ref.borrow())));
        }

        let sym_name = if name.kind == TokenKind::Underscore {
            format!(
                "unnamed{}$",
                UNIQUE_COUNTER.fetch_add(1, std::sync::atomic::Ordering::SeqCst)
            )
        } else {
            name.text.clone()
        };

        Ok(scope::Scope::add_child(
            &self.cur_scope,
            &sym_name,
            scope::State::NotVisited(scope::ScopeNode::Field(field)),
            field,
        ))
    }

    fn visit_decl(&mut self, node: &'a ast::Decl, should_visit_children: bool) -> CompileResult<Context<'a>> {
        macro_rules! colon_compulsory {
            ($token:expr) => {
                // Check the colon thing
                let Some(eq_token) = $token else {
                    unreachable!("probably some parser bug");
                };
                if eq_token.kind != TokenKind::Colon {
                    self.saved_errs.push(self.make_err("expected ':'", eq_token));
                }
            };
        }

        match node {
            ast::Decl::Decl {
                name,
                taipe,
                eq_token,
                object,
            } => {
                let scope = if let Some(child) = self.get_cur_scope().children.get(&name.text) {
                    Rc::clone(child)
                } else {
                    if let Some(object) = object {
                        self.declare_sym_with_value(node, &name, object)?
                    } else {
                        self.declare_sym(node, &name)?
                    }
                };
                // Set in progress
                {
                    let mut scope_ref = scope.borrow_mut();
                    match &scope_ref.state {
                        State::NotVisited(_) => {
                            scope_ref.state = scope::State::VisitInProg;
                        }
                        State::VisitInProg => unreachable!("probably some analyzer bug"),
                        State::Visited(ctx) => {
                            if !ctx.taipe.is_module() {
                                return Ok(Context::from_scope(&ctx.taipe, &scope));
                            }
                        }
                    }
                }
                // Unwrap the object
                let Some(object) = object else {
                    // Situation
                    // ---------------------------------
                    // name : type;
                    // ---------------------------------
                    let Some(taipe) = taipe else {
                        unreachable!("probably some parser bug");
                    };
                    assert!(eq_token.is_none());
                    let type_ctx = self.visit_type(taipe)?;
                    if type_ctx.is_const() {
                        return Err(self.make_err("value must be specified", node));
                    }
                    let ctx = self.resolve_assign(Some((type_ctx, taipe.get_line_info())), None, None)?;
                    let result = Context::from_scope(&ctx.taipe, &scope);
                    scope.borrow_mut().state = State::Visited(ctx);
                    return Ok(result);
                };
                match object {
                    ast::Object::ExternModule { line_info: _, value } => {
                        colon_compulsory!(eq_token);
                        todo!("extern modules are not supported yet")
                    }
                    ast::Object::Module { line_info: _, decls } => {
                        colon_compulsory!(eq_token);
                        // Visit type
                        if let Some(taipe) = taipe {
                            let taipe = self.visit_type(taipe)?;
                            let context::Type::Module = taipe else {
                                return Err(self.make_err("expected 'module'", node));
                            };
                        }
                        // Begin new scope
                        let old_cur_scope = Rc::clone(&self.cur_scope);
                        self.cur_scope = Rc::clone(&scope);
                        // Mark it evaluated if not already
                        let ctx = if let scope::State::Visited(ctx) = &scope.borrow().state {
                            Context::from_module(&scope)
                        } else {
                            // Predeclare all declarations (only if not already visited)
                            self.pre_declare_decls(decls)?;
                            scope.borrow_mut().state = State::Visited(Context::from_module(&scope));
                            Context::from_module(&scope)
                        };
                        if should_visit_children {
                            // Visit every decl
                            for decl in decls {
                                self.visit_decl(decl, true)?;
                            }
                        } else {
                            // Visit only modules
                            for decl in decls {
                                if let ast::Decl::Decl {
                                    name: _,
                                    taipe: _,
                                    eq_token: _,
                                    object: Some(object),
                                } = decl
                                {
                                    match object {
                                        ast::Object::ExternModule { line_info: _, value } => {
                                            todo!("extern modules are not supported yet")
                                        }
                                        ast::Object::Module { line_info: _, decls: _ } => {
                                            self.visit_decl(decl, false)?;
                                        }
                                        _ => {}
                                    }
                                }
                            }
                        }
                        // Restore old scope
                        self.cur_scope = old_cur_scope;
                        Ok(ctx)
                    }
                    // TODO: type punning syntax
                    // A :: struct {
                    //     foo: i32;
                    // }
                    // B :: struct {
                    //     using A;
                    //     bar: i32;
                    // }
                    ast::Object::Compound { line_info: _, field } => {
                        colon_compulsory!(eq_token);
                        // Visit type
                        if let Some(taipe) = taipe {
                            let taipe = self.visit_type(taipe)?;
                            let context::Type::Typedef = taipe else {
                                return Err(self.make_err("expected 'typedef'", node));
                            };
                        }
                        let ctx = self.visit_compound(scope, field)?;
                        Ok(ctx)
                    }
                    ast::Object::Fun {
                        line_info,
                        params,
                        ret,
                        body,
                    } => {
                        colon_compulsory!(eq_token);
                        // Visit type
                        let lhs = if let Some(taipe) = taipe {
                            Some((self.visit_type(taipe)?, taipe.get_line_info()))
                        } else {
                            None
                        };
                        // --- FUNCTION CODE START
                        // Begin new scope
                        let old_cur_scope = Rc::clone(&self.cur_scope);
                        self.cur_scope = Rc::clone(&scope);
                        // Parameter visitation
                        // INFO: Parameters are iterated twice. In the first iteration we visit
                        // the ast nodes and take the useful information (name and Context).
                        // This prevents default value of a param to refer to its previous
                        // param. The second time we declare the parameter inside the function
                        // scope, once and for all.
                        let mut param_infos = Vec::new();
                        let mut prev_default_param = None;
                        for param in params {
                            let lhs = self.visit_type(&param.taipe)?;
                            let lhs_line_info = param.get_line_info();
                            let (eq_token, rhs) = if let Some(expr) = &param.expr {
                                let Some(eq_token) = param.eq_token.as_ref().clone() else {
                                    unreachable!("probably some parser bug");
                                };
                                let rhs = self.visit_expr(expr)?;
                                let rhs_line_info = expr.get_line_info();
                                (Some(eq_token), Some((rhs, rhs_line_info)))
                            } else {
                                (None, None)
                            };
                            let provided_default = rhs.is_some();
                            if provided_default {
                                prev_default_param = Some(param.get_line_info());
                            } else {
                                if let Some(ref prev_default_param) = prev_default_param {
                                    return Err(self
                                        .make_err("non-default parameter is not allowed here", param)
                                        .chain(
                                            self.make_note("previous default parameter is here", prev_default_param),
                                        ));
                                }
                            }
                            let ctx = self.resolve_assign(Some((lhs, lhs_line_info)), eq_token, rhs)?;
                            param_infos.push((
                                &param.name,
                                scope::ParamInfo {
                                    taipe: ctx.taipe,
                                    default: Some(ctx.value),
                                    line_info: param.get_line_info(),
                                },
                            ));
                        }
                        let mut param_table = IndexMap::new();
                        let mut param_types = Vec::new();
                        for (name, param) in param_infos {
                            // Prepare param_types for creating function type
                            let param_type = param.taipe.clone();
                            param_types.push(context::Param {
                                taipe: param_type.clone(),
                            });
                            // Prepare param_table for function call information
                            param_table.insert(name.text.clone(), param);
                            // Generate the param name in the current scope
                            let param_scope = self.declare_sym_ex(scope::State::VisitInProg, name)?;
                            param_scope.borrow_mut().state =
                                scope::State::Visited(Context::from_scope(&param_type, &param_scope));
                        }
                        // Visit the return type
                        let ret_type = if let Some(ret) = ret {
                            let taipe = self.visit_type(ret)?;
                            self.validate_fun_ret_type(&taipe, ret)?;
                            taipe
                        } else {
                            context::Type::Void
                        };
                        // Create the context
                        let rhs = Context {
                            is_lvalue: true,
                            taipe: context::Type::Function {
                                ret: Box::new(ret_type.clone()),
                                params: param_types,
                            },
                            value: context::Value::Reference(Rc::clone(&scope)),
                        };
                        // Resolve assignment
                        let ctx = self.resolve_assign(lhs, eq_token.as_ref(), Some((rhs, *line_info)))?;
                        let result = Context::from_scope(&ctx.taipe, &scope);
                        // Mark it visited
                        scope.borrow_mut().state = scope::State::Visited(ctx);
                        scope.borrow_mut().payload = scope::Payload::Function(scope::Function {
                            param_infos: param_table,
                            loop_stack: IndexMap::new(),
                            ret_line_info: ret.as_ref().map(|ret| ret.get_line_info()),
                        });
                        if let Some(body) = body {
                            let ctx = self.visit_stmt(body)?;
                            if ret_type.is_void() {
                                if !ctx.taipe.is_void() && !ctx.taipe.is_noreturn() {
                                    return Err(self.make_err(
                                        format!(
                                            "expected value of type '{}' or '{}' but got '{}'",
                                            context::Type::Void.to_string(),
                                            context::Type::Noreturn.to_string(),
                                            ctx.taipe.to_string()
                                        ),
                                        body,
                                    ));
                                }
                            } else if ret_type.is_noreturn() && !ctx.taipe.is_noreturn() {
                                return Err(self.make_err(
                                    format!(
                                        "invalid function returns value: '{}' function can never return",
                                        context::Type::Noreturn.to_string(),
                                    ),
                                    &scope.borrow(),
                                ));
                            } else if !ctx.taipe.is_noreturn() {
                                if ctx.taipe.is_void() {
                                    return Err(self.make_err(
                                        "not all control paths return a value",
                                        &body.get_line_info().end(),
                                    ));
                                }
                                let lhs = ret_type;
                                let lhs_line_info = ret
                                    .as_ref()
                                    .map(|ret| ret.get_line_info())
                                    .unwrap_or_else(|| scope.borrow().get_line_info());
                                let rhs = ctx;
                                let rhs_line_info = body.get_line_info();
                                self.resolve_assign(Some((lhs, lhs_line_info)), None, Some((rhs, rhs_line_info)))?;
                            }
                        }
                        // Restore old scope
                        self.cur_scope = old_cur_scope;
                        Ok(result)
                        // --- FUNCTION CODE END
                    }
                    ast::Object::Typedef(node) => {
                        colon_compulsory!(eq_token);
                        // Visit lhs type
                        if let Some(taipe) = taipe {
                            let taipe = self.visit_type(taipe)?;
                            let context::Type::Typedef = taipe else {
                                return Err(self.make_err("expected 'typedef'", node));
                            };
                        }
                        // Visit rhs type
                        let taipe = self.visit_type(node)?;
                        if let context::Type::Typedef = taipe {
                            // context: type -> typedef, value -> typedef
                            // this cannot happen, there is no type of a type
                            // parser prevents this
                            return Err(self.make_err("invalid type alias", node));
                        }
                        // Complete the visit
                        let ctx = Context::from_type(taipe);
                        scope.borrow_mut().state = scope::State::Visited(ctx);
                        Ok(Context::from_scope(&context::Type::Typedef, &scope))
                    }
                    ast::Object::Expr(expr) => {
                        // Visit type
                        let lhs = if let Some(taipe) = taipe {
                            Some((self.visit_type(taipe)?, taipe.get_line_info()))
                        } else {
                            None
                        };
                        // Visit expr
                        let rhs = self.visit_var(name, expr)?;
                        // Resolve assignment
                        let ctx = self.resolve_assign(lhs, eq_token.as_ref(), Some((rhs, expr.get_line_info())))?;
                        let result = Context::from_scope(&ctx.taipe, &scope);
                        // Complete the visit
                        scope.borrow_mut().state = scope::State::Visited(ctx);
                        Ok(result)
                    }
                }
            }
            ast::Decl::Using { line_info: _, items: _ } => {
                todo!("import statements are not supported yet")
            }
        }
    }

    fn visit_stmt(&mut self, node: &'a ast::Stmt) -> CompileResult<Context<'a>> {
        match node {
            ast::Stmt::If {
                line_info: _,
                expr,
                then_body,
                else_body,
            } => self.visit_if_stmt(expr, then_body, else_body.as_ref().map(|s| &**s)),
            ast::Stmt::While {
                line_info: _,
                label,
                expr,
                then_body,
            } => self.visit_while_stmt(label.as_ref(), expr, then_body),
            ast::Stmt::Block { line_info, stmts } => self.visit_block(*line_info, stmts),
            ast::Stmt::Yield { token: _, expr } => Ok(self.visit_expr(expr)?),
            ast::Stmt::Continue { token, label } => self.use_current_function_data(|data| {
                if data.loop_stack.is_empty() {
                    return Err(self.make_err(format!("'{}' can be used only in a loop", token.text), node));
                }
                if let Some(label) = label {
                    if !data.loop_stack.contains_key(&label.text) {
                        let mut searched_names = HashSet::new();
                        for (name, _) in &data.loop_stack {
                            searched_names.insert(name.clone());
                        }
                        return Err(self
                            .make_err(format!("undefined loop label '{}'", label.text), label)
                            .chain(self.make_did_you_mean_help(&label.text, &searched_names)));
                    }
                }
                Ok(Context::from_noreturn())
            }),
            ast::Stmt::Break { token, label } => self.use_current_function_data(|data| {
                if data.loop_stack.is_empty() {
                    return Err(self.make_err(format!("'{}' can be used only in a loop", token.text), node));
                }
                if let Some(label) = label {
                    if !data.loop_stack.contains_key(&label.text) {
                        let mut searched_names = HashSet::new();
                        for (name, _) in &data.loop_stack {
                            searched_names.insert(name.clone());
                        }
                        return Err(self
                            .make_err(format!("undefined loop label '{}'", label.text), label)
                            .chain(self.make_did_you_mean_help(&label.text, &searched_names)));
                    }
                }
                Ok(Context::from_noreturn())
            }),
            ast::Stmt::Return { token, expr } => self.visit_return(token, expr.as_ref()),
            ast::Stmt::Decl(decl) => {
                self.visit_decl(decl, false)?;
                Ok(Context::from_void())
            }
            ast::Stmt::Expr(expr) => {
                let _ = self.visit_expr(expr)?;
                Ok(Context::from_void())
            }
            ast::Stmt::Nop(_) => Ok(Context::from_void()),
        }
    }

    fn visit_while_stmt(
        &mut self,
        label: Option<&Token>,
        expr: &'a ast::Expr,
        then_body: &'a ast::Stmt,
    ) -> Result<Context<'a>, CompileError> {
        let cond = self.visit_expr(expr)?;
        if !cond.taipe.is_bool() {
            return Err(self.make_err(
                format!(
                    "expected value of type '{}' but got value of type '{}'",
                    context::Type::Bool.to_string(),
                    cond.to_string()
                ),
                expr,
            ));
        }
        self.mut_current_function_data(|data| {
            if let Some(label) = label {
                data.loop_stack.insert(label.text.clone(), scope::LoopInfo {});
            } else {
                data.loop_stack.insert(
                    format!(
                        "loop{}$",
                        LOOP_COUNTER.fetch_add(1, std::sync::atomic::Ordering::SeqCst)
                    ),
                    scope::LoopInfo {},
                );
            }
        });
        let then_body_result = self.visit_stmt(then_body)?;
        self.mut_current_function_data(|data| {
            data.loop_stack.pop();
        });
        if then_body_result.taipe.is_noreturn() {
            Ok(Context::from_noreturn())
        } else if then_body_result.taipe.is_void() {
            Ok(Context::from_void())
        } else {
            Err(self.make_err(
                format!(
                    "expected '{}' but got '{}'",
                    context::Type::Void.to_string(),
                    then_body_result.to_string()
                ),
                then_body,
            ))
        }
    }

    fn visit_if_stmt(
        &mut self,
        expr: &'a ast::Expr,
        then_body: &'a ast::Stmt,
        else_body: Option<&'a ast::Stmt>,
    ) -> Result<Context<'a>, CompileError> {
        let cond = self.visit_expr(expr)?;
        if !cond.taipe.is_bool() {
            return Err(self.make_err(
                format!(
                    "expected value of type '{}' but got value of type '{}'",
                    context::Type::Bool.to_string(),
                    cond.to_string()
                ),
                expr,
            ));
        }
        let then_body_result = self.visit_stmt(then_body)?;
        if let Some(else_body) = else_body {
            let else_body_result = self.visit_stmt(else_body)?;
            if then_body_result.taipe.is_noreturn() {
                Ok(Context {
                    is_lvalue: else_body_result.is_lvalue,
                    taipe: else_body_result.taipe.clone(),
                    value: context::Value::IfElse(
                        Box::new(cond),
                        Box::new(then_body_result),
                        Box::new(else_body_result),
                    ),
                })
            } else if else_body_result.taipe.is_noreturn() {
                Ok(Context {
                    is_lvalue: then_body_result.is_lvalue,
                    taipe: then_body_result.taipe.clone(),
                    value: context::Value::IfElse(
                        Box::new(cond),
                        Box::new(then_body_result),
                        Box::new(else_body_result),
                    ),
                })
            } else if then_body_result.taipe == else_body_result.taipe {
                // TODO: allow mixing of compatible values
                Ok(Context {
                    is_lvalue: then_body_result.is_lvalue && else_body_result.is_lvalue,
                    taipe: then_body_result.taipe.clone(),
                    value: context::Value::IfElse(
                        Box::new(cond),
                        Box::new(then_body_result),
                        Box::new(else_body_result),
                    ),
                })
            } else {
                return Err(self.make_err(
                    format!(
                        "expected '{}' but got '{}'",
                        then_body_result.to_string(),
                        else_body_result.to_string(),
                    ),
                    else_body,
                ));
            }
        } else {
            if then_body_result.taipe.is_noreturn() {
                Ok(Context {
                    is_lvalue: false,
                    taipe: context::Type::Noreturn,
                    value: context::Value::If(Box::new(cond), Box::new(then_body_result)),
                })
            } else if then_body_result.taipe.is_void() {
                Ok(Context {
                    is_lvalue: false,
                    taipe: context::Type::Void,
                    value: context::Value::If(Box::new(cond), Box::new(then_body_result)),
                })
            } else {
                Err(self.make_err(
                    format!(
                        "expected '{}' but got '{}'",
                        context::Type::Void.to_string(),
                        then_body_result.to_string()
                    ),
                    then_body,
                ))
            }
        }
    }

    fn visit_return(&mut self, token: &Token, expr: Option<&'a ast::Expr>) -> CompileResult<Context<'a>> {
        let Some(function) = self.get_current_function() else {
            return Err(self.make_err("'return' is allowed in functions only", token));
        };
        // Get the return type of the function
        let ret = {
            let scope::State::Visited(ref ctx) = function.borrow().state else {
                unreachable!("probably some analyzer bug");
            };
            let context::Type::Function { ref ret, params: _ } = ctx.taipe else {
                unreachable!("probably some analyzer bug");
            };
            ret.clone()
        };
        let scope::Payload::Function(scope::Function {
            param_infos: _,
            loop_stack: _,
            ret_line_info,
        }) = function.borrow().payload
        else {
            unreachable!("probably some analyzer bug");
        };
        let ret_line_info = ret_line_info.unwrap_or_else(|| function.borrow().get_line_info());
        let ret = *ret;
        if ret.is_noreturn() {
            return Err(self.make_err(
                format!(
                    "cannot return from a '{}' function",
                    context::Type::Noreturn.to_string()
                ),
                token,
            ));
        }
        if let Some(expr) = expr {
            if ret.is_void() {
                return Err(self.make_err("invalid expression", expr).chain(self.make_note(
                    format!("function expects return type '{}'", ret.to_string()),
                    &ret_line_info,
                )));
            }
            let rhs = self.visit_expr(expr)?;
            let _ = self.resolve_assign(Some((ret, ret_line_info)), None, Some((rhs, expr.get_line_info())))?;
        } else {
            if !ret.is_void() {
                return Err(self
                    .make_err("expected <expression> for 'return'", token)
                    .chain(self.make_note(
                        format!("function expects return type '{}'", ret.to_string()),
                        &ret_line_info,
                    )));
            }
        }
        Ok(Context::from_noreturn())
    }

    fn visit_block(&mut self, line_info: LineInfo, stmts: &'a [ast::Stmt]) -> CompileResult<Context<'a>> {
        let scope = self.create_block_scope(line_info);
        // Begin new scope
        let old_cur_scope = Rc::clone(&self.cur_scope);
        self.cur_scope = Rc::clone(&scope);
        // Predeclare function, struct and union declarations
        for stmt in stmts.iter() {
            match stmt {
                ast::Stmt::Decl(decl) => match &**decl {
                    ast::Decl::Decl {
                        name: _,
                        taipe: _,
                        eq_token: _,
                        object: Some(object),
                    } => match object {
                        ast::Object::ExternModule { line_info: _, value: _ }
                        | ast::Object::Module { line_info: _, decls: _ } => {
                            return Err(self.make_err("module declarations are not allowed in block scope", decl));
                        }
                        ast::Object::Fun {
                            line_info: _,
                            params: _,
                            ret: _,
                            body: _,
                        }
                        | ast::Object::Compound { line_info: _, field: _ } => {
                            self.pre_declare_decl(decl)?;
                        }
                        _ => {}
                    },
                    _ => {}
                },
                _ => {}
            }
        }
        // Prepare to visit the statements
        // Saves the (last index + 1) of the last stmt visited
        let mut last_stmt_index = 0;
        let mut is_lvalue = false;
        let mut block_ret_type = context::Type::Void;
        let mut items = Vec::new();
        // Visit individual statements
        for (i, stmt) in stmts.iter().enumerate() {
            let ctx = self.visit_stmt(stmt)?;
            is_lvalue = ctx.is_lvalue;
            block_ret_type = ctx.taipe.clone();
            items.push(ctx);
            last_stmt_index = i + 1;
            if block_ret_type.is_noreturn() {
                break;
            }
            if block_ret_type.is_void() {
                continue;
            }
            break;
        }
        if last_stmt_index < stmts.len() {
            // Check them anyway
            for stmt in &stmts[last_stmt_index..] {
                self.visit_stmt(stmt)?;
            }
            // We have unreachable code
            self.warnings
                .push(self.make_warning("unreachable code", &&stmts[last_stmt_index..]));
        }
        let ctx = Context {
            is_lvalue,
            taipe: block_ret_type.clone(),
            value: context::Value::Block(items),
        };
        let result = Context {
            is_lvalue,
            taipe: block_ret_type,
            value: context::Value::Reference(Rc::clone(&scope)),
        };
        scope.borrow_mut().state = scope::State::Visited(ctx);
        // Restore old scope
        self.cur_scope = old_cur_scope;
        Ok(result)
    }

    fn create_block_scope(&mut self, line_info: LineInfo) -> Rc<RefCell<scope::Scope<'a>>> {
        let block_name = format!(
            "block{}$",
            BLOCK_COUNTER.fetch_add(1, std::sync::atomic::Ordering::SeqCst)
        );
        let scope = scope::Scope::add_child(&self.cur_scope, &block_name, scope::State::VisitInProg, &line_info);
        scope.borrow_mut().payload = Payload::Block;
        scope
    }

    fn get_fields(&mut self, field: &'a ast::Field) -> CompileResult<scope::Field<'a>> {
        self.get_fields_ex(field, false)
    }

    fn get_fields_ex(&mut self, field: &'a ast::Field, is_alone: bool) -> CompileResult<scope::Field<'a>> {
        match field {
            ast::Field::Compound {
                line_info: _,
                token,
                fields,
            } => {
                if is_alone {
                    return Err(self.make_err("inner scope shadows outer scope", token));
                }

                let mut vec = Vec::new();
                let is_child_alone = fields.len() == 1;
                for field in fields {
                    vec.push(self.get_fields_ex(field, is_child_alone)?);
                }
                match token.kind {
                    TokenKind::Struct => Ok(scope::Field::Struct(vec)),
                    TokenKind::Union => Ok(scope::Field::Union(vec)),
                    _ => unreachable!("probably some parser bug"),
                }
            }
            ast::Field::Decl {
                name,
                taipe,
                eq_token,
                expr,
            } => {
                let scope = self.declare_field(field, name)?;
                // Set in progress
                scope.borrow_mut().state = scope::State::VisitInProg;
                // Visit type
                let lhs = (self.visit_type(taipe)?, taipe.get_line_info());
                let ctx = if let Some(expr) = expr {
                    // Situation
                    // ---------------------------------
                    // name : type = value;
                    // ---------------------------------
                    // Visit expr
                    let rhs = self.visit_expr(expr)?;
                    // TODO: The value of the field should be evaluated at compile time
                    // If no value is provided then default value should be evaluated
                    // Resolve assignment
                    self.resolve_assign(Some(lhs), eq_token.as_ref(), Some((rhs, expr.get_line_info())))?
                } else {
                    // Situation
                    // ---------------------------------
                    // name : type;
                    // ---------------------------------
                    assert!(eq_token.is_none());
                    self.resolve_assign(Some(lhs), None, None)?
                };
                // Check the type of the fields
                match ctx.taipe {
                    context::Type::Const(_)
                    | context::Type::Module
                    | context::Type::Typedef
                    | context::Type::Noreturn => {
                        return Err(self.make_err(
                            format!("'{}' cannot be used as a type of a field", ctx.taipe.to_string()),
                            taipe,
                        ));
                    }
                    _ => {}
                }
                let field_type = ctx.taipe.clone();
                // Complete the visit
                scope.borrow_mut().state = scope::State::Visited(ctx);
                Ok(scope::Field::Field {
                    file_path: scope.borrow().get_src_path(),
                    line_info: name.get_line_info(),
                    name: scope.borrow().name.clone(),
                    taipe: field_type,
                    scope: Rc::clone(&scope),
                })
            }
        }
    }

    fn visit_compound(
        &mut self,
        scope: Rc<RefCell<scope::Scope<'a>>>,
        field: &'a ast::Field,
    ) -> CompileResult<Context<'a>> {
        // Begin new scope
        let old_cur_scope = Rc::clone(&self.cur_scope);
        self.cur_scope = Rc::clone(&scope);
        // Mark it evaluated
        let ctx = Context {
            is_lvalue: true,
            taipe: context::Type::Typedef,
            value: context::Value::Imm(context::Imm::Type(context::Type::Basic(Rc::clone(&scope)))),
        };
        let result = Context {
            is_lvalue: true,
            taipe: context::Type::Typedef,
            value: context::Value::Imm(context::Imm::Type(context::Type::Basic(Rc::clone(&scope)))),
        };
        scope.borrow_mut().state = State::Visited(ctx);
        // Visit every field
        let field = self.get_fields(field)?;
        // Set the payload
        scope.borrow_mut().payload = Payload::Compound(scope::Compound::new(field));
        // Eval the layout
        let layout = self.resolve_layout_scope(&scope)?;
        // Print the layout
        {
            println!("Memory layout of {}: {:?}", scope.borrow().sym_path.to_string(), layout);
            let scope::Payload::Compound(ref compound) = scope.borrow().payload else {
                unreachable!("not supposed to happen")
            };
            let mut fields = compound.offsets.iter().collect::<Vec<_>>();
            fields.sort_by_key(|&(_, &data)| data.offset);
            for (name, field_data) in fields {
                println!("  offset of {} = {:?}", name, field_data);
            }
            println!();
        }
        // Restore old scope
        self.cur_scope = old_cur_scope;
        Ok(result)
    }

    fn visit_var(&mut self, name: &crate::lexer::Token, expr: &'a ast::Expr) -> CompileResult<Context<'a>> {
        match self.visit_expr(expr) {
            Ok(mut ctx) => {
                if ctx.taipe.is_module() {
                    Err(self.make_err("cannot assign a module to a variable", expr))
                } else {
                    ctx.is_lvalue = true;
                    Ok(ctx)
                }
            }
            Err(CompileError::SemCyclic { file_path, line_info }) => Err(self
                .make_err("inference is ambiguous, encountered cyclic references", name)
                .chain(self.make_note_with_path("another one declared here", file_path, &line_info))),
            Err(err) => Err(err),
        }
    }

    fn visit_type(&mut self, node: &'a ast::Type) -> CompileResult<context::Type<'a>> {
        match node {
            ast::Type::Path { items } => {
                let mut index = 0;
                let mut ctx = self.get_name(&items[index])?;
                index += 1;
                while index < items.len() {
                    let name = &items[index];
                    ctx = match ctx.taipe.remove_const() {
                        context::Type::Module => {
                            let context::Value::Reference(module) = ctx.value else {
                                unreachable!("probably some analyzer bug");
                            };
                            self.get_member(&module, &name)?
                        }
                        // TODO: implement this after struct functions
                        // context::Type::Typedef => todo!(),
                        _ => {
                            return Err(self.make_err(
                                format!("cannot use '.' operator on '{}'", ctx.taipe.to_string()),
                                &items[..index].to_vec(),
                            ));
                        }
                    };
                    index += 1;
                }
                if !ctx.taipe.is_typedef() {
                    return Err(self.make_err(format!("expression is not a type: '{}'", ctx.to_string()), node));
                }
                // Post checks
                let context::Value::Imm(taipe) = ctx.value else {
                    unreachable!("not supposed to happen");
                };
                let context::Imm::Type(taipe) = taipe else {
                    unreachable!("not supposed to happen");
                };
                Ok(taipe)
            }
            ast::Type::Function {
                line_info: _,
                params,
                ret,
            } => {
                let mut ctx_params = Vec::new();
                for param in params {
                    let taipe = self.visit_type(&param)?;
                    match &taipe {
                        context::Type::Module | context::Type::Void => {
                            return Err(
                                self.make_err(format!("'{}' cannot be a parameter type", taipe.to_string()), param)
                            );
                        }
                        context::Type::Typedef => {
                            // TODO: Think about this
                            // FIXME: This parameter has to be comptime
                            return Err(self.make_err("'typedef' cannot be a parameter type", param));
                        }
                        _ => {}
                    }
                    ctx_params.push(context::Param { taipe });
                }
                let ctx_ret = self.visit_type(ret)?;
                self.validate_fun_ret_type(&ctx_ret, ret)?;
                Ok(context::Type::Function {
                    ret: Box::new(ctx_ret),
                    params: ctx_params,
                })
            }
            ast::Type::Const { token, taipe: node } => {
                let taipe = self.visit_type(node)?;
                match &taipe {
                    context::Type::Const(_) => {
                        unreachable!("already handled in the parser");
                    }
                    _ => {
                        if taipe.is_const() {
                            self.warnings.push(
                                self.make_warning(
                                    format!(
                                        "'const' is redundant here, '{}' is always a constant",
                                        taipe.to_string()
                                    ),
                                    token,
                                )
                                .chain(self.make_help("remove const qualifier")),
                            );
                            Ok(taipe)
                        } else {
                            Ok(context::Type::Const(Box::new(taipe)))
                        }
                    }
                }
            }
            ast::Type::Pointer { token: _, taipe: node } => {
                let taipe = self.visit_type(node)?;
                match &taipe {
                    context::Type::Module => {
                        return Err(self.make_err("pointer to 'module' is invalid", node));
                    }
                    context::Type::Typedef => {
                        return Err(self.make_err("pointer to 'typedef' is invalid", node));
                    }
                    _ => Ok(context::Type::Pointer(Box::new(taipe))),
                }
            }
            ast::Type::Array {
                line_info: _,
                taipe,
                expr,
            } => {
                let taipe = self.visit_type(taipe)?;
                let Some(expr) = expr else {
                    return Err(self.make_err("array length must be specified", node));
                };
                let length_ctx = self.visit_expr(expr)?;
                if !length_ctx.taipe.is_unsigned_integer() {
                    return Err(self
                        .make_err("argument of index operator should be an unsigned integer type", expr)
                        .chain(self.make_note(format!("but got '{}'", length_ctx.taipe.to_string()), expr)));
                }
                let context::Value::Imm(length) = length_ctx.value else {
                    return Err(self.make_err("value cannot be evaluated at compile time", expr));
                };
                let length = self.transform_imm_to_usize(&length, expr)?;
                let Some(length) = length.to_usize() else {
                    return Err(self.make_err(
                        format!("'usize' cannot hold this value: '{}'", length.to_string()),
                        expr,
                    ));
                };
                Ok(context::Type::Array {
                    count: length,
                    taipe: Box::new(taipe),
                })
            }
            ast::Type::Fat {
                line_info: _,
                taipe: node,
            } => {
                let taipe = self.visit_type(node)?;
                match &taipe {
                    context::Type::Module | context::Type::Typedef => {
                        return Err(self.make_err(format!("fat pointer to '{}' is invalid", taipe.to_string()), node));
                    }
                    _ => Ok(context::Type::Fat(Box::new(taipe))),
                }
            }
            ast::Type::Paren {
                line_info: _,
                taipe: node,
            } => self.visit_type(node),
            ast::Type::Tuple {
                line_info: _,
                types: nodes,
            } => {
                let mut vec = Vec::new();
                for node in nodes {
                    let taipe = self.visit_type(node)?;
                    match &taipe {
                        context::Type::Module | context::Type::Typedef | context::Type::Void => {
                            return Err(self.make_err(format!("'{}' cannot be a tuple item", taipe.to_string()), node));
                        }
                        _ => vec.push(taipe),
                    }
                }
                Ok(context::Type::Tuple(vec))
            }
            ast::Type::Literal(token) => match token.kind {
                TokenKind::Void => Ok(context::Type::Void),
                TokenKind::Noreturn => Ok(context::Type::Noreturn),
                TokenKind::Typedef => Ok(context::Type::Typedef),
                _ => unreachable!("probably some parser bug"),
            },
        }
    }

    fn validate_fun_ret_type(&mut self, taipe: &context::Type<'a>, line_info: &impl HasLineInfo) -> CompileResult<()> {
        match taipe {
            context::Type::Module => {
                return Err(self.make_err("'module' cannot be a return type", line_info));
            }
            context::Type::Typedef => {
                return Err(self.make_err("'typedef' cannot be a return type", line_info));
            }
            _ => {}
        }
        Ok(())
    }

    fn visit_expr(&mut self, node: &'a ast::Expr) -> CompileResult<Context<'a>> {
        match node {
            ast::Expr::Assign { lhses, op, rhses } => {
                match op.kind {
                    // TODO: implement augmented assignment
                    TokenKind::Equal => {}
                    _ => {
                        return Err(self.make_err(
                            format!(
                                "semantic analyzer does not understand operator '{}': not implemented yet",
                                &op.text
                            ),
                            op,
                        ));
                    }
                }
                for i in 0..rhses.len() {
                    let rhs_node = &rhses[i];
                    let rhs_line_info = rhs_node.get_line_info();
                    let rhs = self.visit_expr(rhs_node)?;
                    let lhs_node = &lhses[i];
                    let lhs_line_info = lhs_node.get_line_info();
                    let lhs = self.visit_expr(lhs_node)?;
                    // do lvalue checking
                    if !lhs.is_lvalue {
                        return Err(self.make_err("cannot assign to a prvalue (pure rvalue)", &lhs_line_info));
                    }
                    let _ = self.resolve_assign(Some((lhs.taipe, lhs_line_info)), None, Some((rhs, rhs_line_info)))?;
                }
                // TODO: record info for IR
                Ok(Context::from_void())
            }
            ast::Expr::Binary { left, op, right } => self.visit_binary(left, op, right),
            ast::Expr::Cast { expr, taipe } => todo!(),
            ast::Expr::Unary { op, expr } => self.visit_unary(op, expr),
            // Postfix dot operator
            //    result = value.name       // name is an identifier
            // Description:
            //    Flips all the bits of an signed or unsigned integer
            // value and result can be:
            //  * value: T               -> result: {type of member}
            //  * value: const T         -> result: const {type of member}
            //  * value: *T              -> result: {type of member}
            //  * value: *const T        -> result: const {type of member}
            //  * value: const *T        -> result: {type of member}
            //  * value: const *const T  -> result: const {type of member}
            // note: T is never a pointer type
            ast::Expr::Member { expr, name } => {
                let ctx = self.visit_expr(expr)?;
                let (keep_const, taipe) = match ctx.taipe.clone() {
                    context::Type::Pointer(taipe) => match *taipe {
                        context::Type::Const(taipe) => (true, *taipe),
                        taipe => (false, taipe),
                    },
                    context::Type::Const(taipe) => match *taipe {
                        context::Type::Pointer(taipe) => match *taipe {
                            context::Type::Const(taipe) => (true, *taipe),
                            taipe => (false, taipe),
                        },
                        taipe => (true, taipe),
                    },
                    taipe => (false, taipe),
                };
                match taipe {
                    context::Type::Basic(scope) => {
                        let mut ctx = self.get_member(&scope, &name)?;
                        assert!(ctx.is_lvalue);
                        if keep_const {
                            ctx.taipe = context::Type::Const(Box::new(ctx.taipe));
                        }
                        Ok(ctx)
                    }
                    // array and fat pointer have two members
                    // count => fn (*const self) -> usize
                    // ptr   => *T
                    context::Type::Array { count, taipe } => todo!(),
                    context::Type::Fat(_) => todo!(),
                    context::Type::Tuple(items) => {
                        if name.kind != TokenKind::IntLit {
                            return Err(self.make_err(format!("expected {}", TokenKind::IntLit.get_repr()), name));
                        }
                        let Some(index) = name.value.clone() else {
                            unreachable!("probably some lexer bug");
                        };
                        let TokenValue::Int(index) = index else {
                            unreachable!("probably some lexer bug");
                        };
                        // comptime: bounds checking
                        if index.num >= items.len().to_bigint().unwrap() {
                            return Err(self.make_err(
                                format!("index out of bounds, tuple length: {}, index: '{}'", items.len(), index),
                                name,
                            ));
                        }
                        // Get the type
                        let mut taipe = items[index.to_usize().expect("dont know what to do in this case")].clone();
                        if keep_const {
                            taipe = taipe.add_const();
                        }
                        // comptime: array indexing
                        let index = Context {
                            is_lvalue: true,
                            taipe: self.type_usize.clone(),
                            value: context::Value::Imm(
                                self.transform_varint_to_usize(&context::Imm::VarInt(index), name)?,
                            ),
                        };
                        Ok(Context {
                            is_lvalue: false,
                            taipe,
                            value: context::Value::Index(Box::new(ctx), Box::new(index)),
                        })
                    }
                    context::Type::Module => {
                        let context::Value::Reference(module) = ctx.value else {
                            unreachable!("probably some analyzer bug");
                        };
                        self.get_member(&module, &name)
                    }
                    // TODO: implement this after struct functions
                    // context::Type::Typedef => todo!(),
                    _ => Err(self.make_err(format!("cannot use '.' operator on '{}'", ctx.taipe.to_string()), expr)),
                }
            }
            ast::Expr::Call {
                line_info: _,
                expr,
                args,
            } => self.visit_call(node, expr, args),
            ast::Expr::Index {
                line_info: _,
                expr,
                items,
            } => {
                if items.len() != 1 {
                    // TODO: to be changed
                    return Err(self.make_err("only 1 argument is allowed in index operator", items));
                }
                let ctx = self.visit_expr(expr)?;
                let index_node = &items[0];
                let index = self.visit_expr(index_node)?;
                if !index.taipe.is_integer() {
                    return Err(self
                        .make_err("argument of index operator should be an integer type", node)
                        .chain(self.make_note(format!("but got '{}'", index.taipe.to_string()), index_node)));
                }
                match ctx.taipe.remove_const() {
                    context::Type::Array { count: _, taipe } => Ok(Context {
                        is_lvalue: false,
                        taipe: *taipe,
                        value: context::Value::Index(Box::new(ctx), Box::new(index)),
                    }),
                    context::Type::Fat(taipe) => Ok(Context {
                        is_lvalue: false,
                        taipe: *taipe,
                        value: context::Value::Index(Box::new(ctx), Box::new(index)),
                    }),
                    _ => {
                        return Err(self.make_err(
                            format!("cannot use index operator on type '{}'", ctx.taipe.to_string()),
                            expr,
                        ));
                    }
                }
            }
            ast::Expr::Literal(token) => match token.kind {
                TokenKind::True => Ok(Context::from_bool(true)),
                TokenKind::False => Ok(Context::from_bool(false)),
                TokenKind::StringLit => {
                    let Some(tok_val) = &token.value else {
                        unreachable!("probably some lexer bug")
                    };
                    let TokenValue::String(str) = tok_val else {
                        unreachable!("probably some lexer bug")
                    };
                    Ok(Context::from_str(str))
                }
                TokenKind::IntLit => {
                    let Some(tok_val) = token.value.as_ref() else {
                        unreachable!("probably some lexer bug");
                    };
                    let TokenValue::Int(tok_val) = tok_val else {
                        unreachable!("probably some lexer bug");
                    };
                    // TODO: check suffix
                    Ok(Context {
                        is_lvalue: false,
                        taipe: context::Type::VarInt,
                        value: context::Value::Imm(context::Imm::VarInt(tok_val.clone())),
                    })
                }
                // TODO: get value from token
                TokenKind::FloatLit => Ok(Context {
                    is_lvalue: false,
                    taipe: context::Type::Float64,
                    value: context::Value::Imm(context::Imm::Float64(0.0)),
                }),
                TokenKind::Ident => self.get_name(&token),
                _ => unreachable!("probably some parser bug"),
            },
            ast::Expr::Paren { line_info: _, expr } => self.visit_expr(expr),
            ast::Expr::Tuple { line_info: _, exprs } => {
                let mut types = Vec::new();
                let mut values = Vec::new();
                for expr in exprs {
                    let mut ctx = self.visit_expr(expr)?;
                    if ctx.taipe.is_varint() {
                        ctx.taipe = self.type_int.clone();
                        let context::Value::Imm(value) = ctx.value else {
                            unreachable!("probably some analyzer bug");
                        };
                        ctx.value = context::Value::Imm(self.transform_varint_to_int(&value, expr)?);
                    }
                    types.push(ctx.taipe);
                    values.push(ctx.value);
                }
                Ok(Context {
                    is_lvalue: false,
                    taipe: context::Type::Tuple(types),
                    value: context::Value::Tuple(values),
                })
            }
            // TODO: implement this
            ast::Expr::ArrayLit { line_info: _, items } => todo!(),
        }
    }

    fn visit_call(
        &mut self,
        node: &'a ast::Expr,
        expr: &'a ast::Expr,
        args: &'a [ast::Arg],
    ) -> CompileResult<Context<'a>> {
        let ctx = self.visit_expr(expr)?;
        if !ctx.taipe.is_function() {
            return Err(self.make_err(
                format!("expected function but got value of type '{}'", ctx.to_string()),
                expr,
            ));
        }
        let mut pos_arg_infos = Vec::new();
        let mut named_arg_infos = IndexMap::new();
        let mut prev_named_arg = None;
        for arg in args {
            let arg_ctx = self.visit_expr(&arg.expr)?;
            if let Some(ref name) = arg.name {
                prev_named_arg = Some(name.get_line_info());
                let result = named_arg_infos.insert(
                    name.text.clone(),
                    (arg_ctx, name.get_line_info(), arg.expr.get_line_info()),
                );
                // Check for duplicate named arguments
                if let Some((_, line_info, _)) = result {
                    return Err(self
                        .make_err("duplicate named argument", name)
                        .chain(self.make_note("previous named argument is here", &line_info)));
                }
            } else {
                if let Some(ref prev_named_arg) = prev_named_arg {
                    return Err(self
                        .make_err("unnamed argument is not allowed here", arg)
                        .chain(self.make_note("previous named argument is here", prev_named_arg)));
                }
                pos_arg_infos.push((arg_ctx, arg.get_line_info()));
            }
        }
        assert!(pos_arg_infos.len() + named_arg_infos.len() == args.len());
        self.resolve_call(ctx, pos_arg_infos, named_arg_infos, node.get_line_info())
    }

    fn resolve_call(
        &mut self,
        fun_ctx: Context<'a>,
        pos_arg_infos: Vec<(Context<'a>, LineInfo)>,
        named_arg_infos: IndexMap<String, (Context<'a>, LineInfo, LineInfo)>,
        call_line_info: LineInfo,
    ) -> CompileResult<Context<'a>> {
        // For better error messages
        let mut errs = CompileError::Errors(Vec::new());
        if let context::Value::Reference(scope_rc) = fun_ctx.value {
            let scope = scope_rc.borrow();
            let scope::Payload::Function(ref data) = scope.payload else {
                unreachable!("probably some analyzer bug");
            };
            // Check argument count
            let arg_count = pos_arg_infos.len() + named_arg_infos.len();
            let total_param_count = data.get_total_param_count();
            if data.has_default_params() {
                let min_param_count = data.get_min_param_count();
                if arg_count < min_param_count || arg_count > total_param_count {
                    errs = errs.chain(self.make_err(
                        format!(
                            "expected '{}' to '{}' argument{} but got '{}'",
                            min_param_count,
                            total_param_count,
                            get_plural(total_param_count),
                            arg_count
                        ),
                        &call_line_info,
                    ));
                }
            } else {
                if arg_count != total_param_count {
                    errs = errs.chain(self.make_err(
                        format!(
                            "expected '{}' argument{} but got '{}'",
                            total_param_count,
                            get_plural(total_param_count),
                            arg_count
                        ),
                        &call_line_info,
                    ));
                }
            }
            // Get the necessary info about params
            let params = &data.param_infos;
            let mut args_info = IndexMap::new();
            // Check positional argument expression types
            for (i, (arg_ctx, arg_line_info)) in pos_arg_infos.into_iter().enumerate() {
                let (param_name, param) = params.get_index(i).unwrap();
                let lhs = param.taipe.clone();
                let lhs_line_info = param.line_info;
                let rhs = arg_ctx;
                let rhs_line_info = arg_line_info;
                let mut ctx = match self.resolve_assign(Some((lhs, lhs_line_info)), None, Some((rhs, rhs_line_info))) {
                    Ok(it) => it,
                    Err(err) => {
                        errs = errs.chain(err);
                        Context {
                            is_lvalue: true,
                            taipe: param.taipe.clone(),
                            value: context::Value::from_nil(),
                        }
                    }
                };
                ctx.is_lvalue = true;
                args_info.insert(param_name.clone(), (ctx, rhs_line_info));
            }
            // Check named argument expression types
            for (name, (arg_ctx, arg_line_info, arg_expr_info)) in named_arg_infos {
                let Some(param) = params.get(&name) else {
                    let searched_names = params.iter().map(|(name, _)| name.clone()).collect::<HashSet<_>>();
                    return Err(self
                        .make_err(format!("unknown argument: '{}'", name), &arg_line_info)
                        .chain(self.make_did_you_mean_help(&name, &searched_names)));
                };
                let lhs = param.taipe.clone();
                let lhs_line_info = param.line_info;
                let rhs = arg_ctx;
                let rhs_line_info = arg_expr_info;
                let mut ctx = match self.resolve_assign(Some((lhs, lhs_line_info)), None, Some((rhs, rhs_line_info))) {
                    Ok(it) => it,
                    Err(err) => {
                        errs = errs.chain(err);
                        Context {
                            is_lvalue: true,
                            taipe: param.taipe.clone(),
                            value: context::Value::from_nil(),
                        }
                    }
                };
                ctx.is_lvalue = true;
                let result = args_info.insert(name.clone(), (ctx, rhs_line_info));
                // Check possible duplicate named and position argument
                if let Some((_, line_info)) = result {
                    errs = errs
                        .chain(self.make_err("duplicate named argument", &arg_line_info))
                        .chain(self.make_note("previous positional argument is here", &line_info));
                }
            }
            let mut args_info = args_info
                .into_iter()
                .map(|(name, (ctx, _))| (name, ctx))
                .collect::<IndexMap<_, _>>();
            // Check if any value is left out
            for (name, param) in params.iter() {
                if !args_info.contains_key(name) {
                    if let Some(value) = &param.default {
                        args_info.insert(
                            name.clone(),
                            Context {
                                is_lvalue: true,
                                taipe: param.taipe.clone(),
                                value: value.clone(),
                            },
                        );
                    } else {
                        errs = errs
                            .chain(
                                self.make_err(format!("value of argument '{}' is not provided", name), &call_line_info),
                            )
                            .chain(self.make_note("declared here", &param.line_info))
                    }
                }
            }
            // Return the accumulated errors
            if !errs.is_empty() {
                return Err(errs);
            }
            println!(
                "Call to function {}: {}",
                scope.sym_path.to_string(),
                fun_ctx.taipe.to_string()
            );
            let line_info = call_line_info.begin();
            println!(
                "    at {}:{}:{}",
                self.get_cur_scope().get_src_path(),
                line_info.line_start,
                line_info.col_start
            );
            for (name, arg_ctx) in args_info.iter() {
                println!("  Argument => {}: {}", name, arg_ctx.to_string())
            }
            println!();
            let context::Type::Function {
                ret: return_type,
                params: _,
            } = fun_ctx.taipe
            else {
                unreachable!("probably some analyzer bug")
            };
            drop(scope);
            Ok(Context {
                is_lvalue: false,
                taipe: (*return_type).clone(),
                value: context::Value::Call(scope_rc, args_info),
            })
        } else {
            todo!()
        }
    }

    // Handles the following thing
    //  * lhs: {integer} rhs: {integer} -> lhs: int  rhs: int
    //  * lhs: {integer} rhs: iX        -> lhs: iX   rhs: iX
    //  * lhs: {integer} rhs: uX        -> lhs: uX   rhs: uX
    //  * lhs: {integer} rhs: fX        -> lhs: fX   rhs: fX
    //  * lhs: iX        rhs: {integer} -> lhs: iX   rhs: iX
    //  * lhs: uX        rhs: {integer} -> lhs: uX   rhs: uX
    //  * lhs: fX        rhs: {integer} -> lhs: fX   rhs: fX
    //
    // In other words handles this, if not matched then flips it and checks again
    //  * lhs: {integer} rhs: {integer} -> lhs: int  rhs: int
    //  * lhs: {integer} rhs: iX        -> lhs: iX   rhs: iX
    //  * lhs: {integer} rhs: uX        -> lhs: uX   rhs: uX
    //  * lhs: {integer} rhs: fX        -> lhs: fX   rhs: fX
    fn resolve_value_promotion(
        &self,
        lhs: &mut Context<'a>,
        left: &'a ast::Expr,
        rhs: &mut Context<'a>,
        right: &'a ast::Expr,
    ) -> CompileResult<()> {
        fn resolve_value_promotion_ex<'a>(
            analyzer: &Analyzer<'a>,
            lhs: &mut Context<'a>,
            left: &'a ast::Expr,
            rhs: &mut Context<'a>,
            right: &'a ast::Expr,
            should_check_another_time: bool,
        ) -> CompileResult<()> {
            if lhs.taipe.is_varint() && rhs.taipe.is_varint() {
                lhs.taipe = analyzer.type_int.clone();
                rhs.taipe = analyzer.type_int.clone();
                let context::Value::Imm(ref lhs_value) = lhs.value else {
                    unreachable!("probably some analyzer bug");
                };
                let context::Value::Imm(ref rhs_value) = rhs.value else {
                    unreachable!("probably some analyzer bug");
                };
                lhs.value = context::Value::Imm(analyzer.transform_varint_to_int(lhs_value, left)?);
                rhs.value = context::Value::Imm(analyzer.transform_varint_to_int(rhs_value, right)?);
                Ok(())
            } else if lhs.taipe.is_varint() {
                if rhs.taipe.is_integer() || rhs.taipe.is_float() {
                    let context::Value::Imm(ref lhs_value) = lhs.value else {
                        unreachable!("probably some analyzer bug");
                    };
                    // Convert varint to respective type if it is worth it
                    lhs.value = context::Value::Imm(analyzer.transform_varint(&rhs.taipe, lhs_value, left, None)?);
                    lhs.taipe = rhs.taipe.clone();
                    return Ok(());
                }
                Ok(())
            } else if should_check_another_time {
                resolve_value_promotion_ex(analyzer, rhs, right, lhs, left, false)
            } else {
                Ok(())
            }
        }
        resolve_value_promotion_ex(self, lhs, left, rhs, right, true)
    }

    fn visit_binary(&mut self, left: &'a ast::Expr, op: &Token, right: &'a ast::Expr) -> CompileResult<Context<'a>> {
        let line_info = LineInfo::from_range(left, right);
        let mut lhs = self.visit_expr(left)?;
        let mut rhs = self.visit_expr(right)?;

        macro_rules! return_err {
            () => {
                return Err(self.make_err(
                    format!(
                        "cannot apply '{}' operator on values of types '{}' and '{}'",
                        &op.text,
                        lhs.taipe.to_string(),
                        rhs.taipe.to_string()
                    ),
                    &line_info,
                ));
            };
            (integer_overflow) => {
                return Err(self.make_err(
                    format!(
                        "detected integer overflow: '{}' {} '{}'",
                        lhs.value.unwrap().to_string(),
                        &op.text,
                        rhs.value.unwrap().to_string()
                    ),
                    &line_info,
                ));
            };
        }

        match op.kind {
            // Binary logical and operator
            //    result = (value1) and (value2)
            // Description:
            //    Returns the result of logical short-circuiting and of two bools
            // value1, value2 and result can be:
            //  * value1: bool      value2: bool      -> result: bool
            // note: value may be const or non-const
            TokenKind::And => {
                if !lhs.taipe.is_bool() || !rhs.taipe.is_bool() {
                    return_err!();
                }
                Ok(Context {
                    is_lvalue: false,
                    taipe: context::Type::Bool,
                    value: context::Value::LogicAnd(Box::new(lhs), Box::new(rhs)),
                })
            }
            // Binary logical and operator
            //    result = (value1) and (value2)
            // Description:
            //    Returns the result of logical short-circuiting and of two bools
            // value1, value2 and result can be:
            //  * value1: bool      value2: bool      -> result: bool
            // note: value may be const or non-const
            TokenKind::Or => {
                if !lhs.taipe.is_bool() || !rhs.taipe.is_bool() {
                    return_err!();
                }
                Ok(Context {
                    is_lvalue: false,
                    taipe: context::Type::Bool,
                    value: context::Value::LogicOr(Box::new(lhs), Box::new(rhs)),
                })
            }
            // Binary relational operators
            //    result = (value1) <  (value2)
            //    result = (value1) <= (value2)
            //    result = (value1) == (value2)
            //    result = (value1) != (value2)
            //    result = (value1) >  (value2)
            //    result = (value1) >= (value2)
            // Description:
            //    Returns the result of comparison of two values
            // value1, value2 and result can be:
            //  * value1: {integer} value2: {integer} -> result: bool
            //  * value1: iX        value2: iX        -> result: bool
            //  * value1: uX        value2: uX        -> result: bool
            //  * value1: fX        value2: fX        -> result: bool
            //  * value1: {integer} value2: iX        -> result: bool
            //  * value1: {integer} value2: uX        -> result: bool
            //  * value1: {integer} value2: fX        -> result: bool
            //  * value1: iX        value2: {integer} -> result: bool
            //  * value1: uX        value2: {integer} -> result: bool
            //  * value1: fX        value2: {integer} -> result: bool
            //
            //  * value1: bool      value2: bool      -> result: bool
            //  * value1: char      value2: char      -> result: bool
            //  * value1: typedef   value2: typedef   -> result: bool
            //  * value1: *T        value2: *T        -> result: bool
            //  * value1: *const T  value2: *const T  -> result: bool
            // note: value may be const or non-const
            TokenKind::LAngle
            | TokenKind::LessEq
            | TokenKind::EqEq
            | TokenKind::NotEq
            | TokenKind::GreaterEq
            | TokenKind::RAngle => {
                self.resolve_value_promotion(&mut lhs, left, &mut rhs, right)?;
                if lhs.taipe.remove_const() != rhs.taipe.remove_const() {
                    return_err!();
                }
                let value = match lhs.taipe.remove_const() {
                    context::Type::Bool
                    | context::Type::Char
                    | context::Type::Pointer(_)
                    | context::Type::Int8
                    | context::Type::Int16
                    | context::Type::Int32
                    | context::Type::Int64
                    | context::Type::Int128
                    | context::Type::Uint8
                    | context::Type::Uint16
                    | context::Type::Uint32
                    | context::Type::Uint64
                    | context::Type::Uint128
                    | context::Type::Float32
                    | context::Type::Float64 => {
                        // Refer to: https://doc.rust-lang.org/std/cmp/trait.PartialOrd.html
                        match op.kind {
                            TokenKind::EqEq => context::Value::Eq(Box::new(lhs), Box::new(rhs)),
                            TokenKind::LAngle => context::Value::Lt(Box::new(lhs), Box::new(rhs)),
                            TokenKind::RAngle => context::Value::Gt(Box::new(lhs), Box::new(rhs)),
                            TokenKind::LessEq => context::Value::Le(Box::new(lhs), Box::new(rhs)),
                            TokenKind::GreaterEq => context::Value::Ge(Box::new(lhs), Box::new(rhs)),
                            TokenKind::NotEq => context::Value::Ne(Box::new(lhs), Box::new(rhs)),
                            _ => unreachable!("probably some analyzer bug"),
                        }
                    }
                    context::Type::Typedef => {
                        let context::Value::Imm(lhs_value) = lhs.value else {
                            unreachable!("probably some analyzer bug");
                        };
                        let context::Imm::Type(lhs_type) = lhs_value else {
                            unreachable!("probably some analyzer bug");
                        };
                        let context::Value::Imm(rhs_value) = rhs.value else {
                            unreachable!("probably some analyzer bug");
                        };
                        let context::Imm::Type(rhs_type) = rhs_value else {
                            unreachable!("probably some analyzer bug");
                        };
                        context::Value::from_bool(lhs_type == rhs_type)
                    }
                    // context::Type::Basic(weak) => todo!(),
                    // context::Type::Array { count, taipe } => todo!(),
                    // context::Type::Fat(_) => todo!(),
                    // context::Type::Tuple(items) => todo!(),
                    _ => {
                        return_err!();
                    }
                };
                Ok(Context {
                    is_lvalue: false,
                    taipe: context::Type::Bool,
                    value,
                })
            }
            // Binary bitwise and operator
            //    result = (value1) & (value2)
            // Description:
            //    Returns the result of bitwise and of two integers
            // value1, value2 and result can be:
            //  * value1: {integer} value2: {integer} -> result: int
            //  * value1: iX        value2: iX        -> result: iX
            //  * value1: uX        value2: uX        -> result: uX
            //  * value1: {integer} value2: iX        -> result: iX
            //  * value1: {integer} value2: uX        -> result: uX
            //  * value1: iX        value2: {integer} -> result: iX
            //  * value1: uX        value2: {integer} -> result: uX
            // note: value may be const or non-const
            TokenKind::Ampersand => {
                if lhs.taipe.is_integer() && rhs.taipe.is_integer() {
                    self.resolve_value_promotion(&mut lhs, left, &mut rhs, right)?;
                    if lhs.taipe.remove_const() != rhs.taipe.remove_const() {
                        return_err!();
                    }
                    Ok(Context {
                        is_lvalue: false,
                        taipe: lhs.taipe.clone().add_const(),
                        value: context::Value::BitAnd(Box::new(lhs), Box::new(rhs)),
                    })
                } else {
                    return_err!();
                }
            }
            // Binary bitwise xor operator
            //    result = (value1) ^ (value2)
            // Description:
            //    Returns the result of bitwise xor of two integers
            // value1, value2 and result can be:
            //  * value1: {integer} value2: {integer} -> result: int
            //  * value1: iX        value2: iX        -> result: iX
            //  * value1: uX        value2: uX        -> result: uX
            //  * value1: {integer} value2: iX        -> result: iX
            //  * value1: {integer} value2: uX        -> result: uX
            //  * value1: iX        value2: {integer} -> result: iX
            //  * value1: uX        value2: {integer} -> result: uX
            // note: value may be const or non-const
            TokenKind::Caret => {
                if lhs.taipe.is_integer() && rhs.taipe.is_integer() {
                    self.resolve_value_promotion(&mut lhs, left, &mut rhs, right)?;
                    if lhs.taipe.remove_const() != rhs.taipe.remove_const() {
                        return_err!();
                    }
                    Ok(Context {
                        is_lvalue: false,
                        taipe: lhs.taipe.clone().add_const(),
                        value: context::Value::BitXor(Box::new(lhs), Box::new(rhs)),
                    })
                } else {
                    return_err!();
                }
            }
            // Binary bitwise or operator
            //    result = (value1) | (value2)
            // Description:
            //    Returns the result of bitwise or of two integers
            // value1, value2 and result can be:
            //  * value1: {integer} value2: {integer} -> result: int
            //  * value1: iX        value2: iX        -> result: iX
            //  * value1: uX        value2: uX        -> result: uX
            //  * value1: {integer} value2: iX        -> result: iX
            //  * value1: {integer} value2: uX        -> result: uX
            //  * value1: iX        value2: {integer} -> result: iX
            //  * value1: uX        value2: {integer} -> result: uX
            // note: value may be const or non-const
            TokenKind::Pipe => {
                if lhs.taipe.is_integer() && rhs.taipe.is_integer() {
                    self.resolve_value_promotion(&mut lhs, left, &mut rhs, right)?;
                    if lhs.taipe.remove_const() != rhs.taipe.remove_const() {
                        return_err!();
                    }
                    Ok(Context {
                        is_lvalue: false,
                        taipe: lhs.taipe.clone().add_const(),
                        value: context::Value::BitOr(Box::new(lhs), Box::new(rhs)),
                    })
                } else {
                    return_err!();
                }
            }
            // Binary bitwise shift left operator
            //    result = (value1) << (value2)
            // Description:
            //    Shifts the bits of an value towards left and fills zero in the right
            //    and returns the value
            // value1, value2 and result can be:
            //  * value1: {integer} value2: {integer} -> result: int
            //  * value1: iX        value2: uX        -> result: iX
            //  * value1: uX        value2: uX        -> result: uX
            //  * value1: {integer} value2: uX        -> result: iX
            //  * value1: {integer} value2: uX        -> result: iX
            //  * value1: iX        value2: {integer} -> result: iX
            //  * value1: uX        value2: {integer} -> result: uX
            // note: value may be const or non-const
            // TODO: due to rust we convert rhs to u32 (which is not the intended behaviour)
            TokenKind::ShiftLeft => {
                if lhs.taipe.is_integer() {
                    if !rhs.taipe.is_varint() && !rhs.taipe.is_unsigned_integer() {
                        return Err(self.make_err(
                            format!("expected unsigned integer but got '{}'", rhs.taipe.to_string()),
                            right,
                        ));
                    }
                    // convert varint -> int
                    if lhs.taipe.is_varint() {
                        let context::Value::Imm(ref lhs_value) = lhs.value else {
                            unreachable!("probably some analyzer bug");
                        };
                        lhs.taipe = self.type_int.clone();
                        lhs.value = context::Value::Imm(self.transform_varint_to_int(lhs_value, right)?);
                    }
                    // implicit cast to u32
                    if rhs.taipe.is_varint() {
                        let context::Value::Imm(ref rhs_value) = rhs.value else {
                            unreachable!("probably some analyzer bug");
                        };
                        rhs.taipe = context::Type::Uint32;
                        rhs.value = context::Value::Imm(self.transform_varint(&rhs.taipe, rhs_value, right, None)?);
                    }
                    Ok(Context {
                        is_lvalue: false,
                        taipe: lhs.taipe.clone().add_const(),
                        value: context::Value::Shl(Box::new(lhs), Box::new(rhs)),
                    })
                } else {
                    return_err!();
                }
            }
            // Binary bitwise shift right operator
            //    result = (value1) >> (value2)
            // Description:
            //    Shifts the bits of an value towards right and fills zero in the right
            //    if the value1 is unsigned and sign extends it if the value is signed
            //    and returns the value
            // value1, value2 and result can be:
            //  * value1: {integer} value2: {integer} -> result: int
            //  * value1: iX        value2: uX        -> result: iX
            //  * value1: uX        value2: uX        -> result: uX
            //  * value1: {integer} value2: uX        -> result: iX
            //  * value1: {integer} value2: uX        -> result: iX
            //  * value1: iX        value2: {integer} -> result: iX
            //  * value1: uX        value2: {integer} -> result: uX
            // note: value may be const or non-const
            // TODO: due to rust we convert rhs to u32 (which is not the intended behaviour)
            TokenKind::ShiftRight => {
                if lhs.taipe.is_integer() {
                    if !rhs.taipe.is_varint() && !rhs.taipe.is_unsigned_integer() {
                        return Err(self.make_err(
                            format!("expected unsigned integer but got '{}'", rhs.taipe.to_string()),
                            right,
                        ));
                    }
                    // convert varint -> int
                    if lhs.taipe.is_varint() {
                        let context::Value::Imm(ref lhs_value) = lhs.value else {
                            unreachable!("probably some analyzer bug");
                        };
                        lhs.taipe = self.type_int.clone();
                        lhs.value = context::Value::Imm(self.transform_varint_to_int(lhs_value, right)?);
                    }
                    // implicit cast to u32
                    if rhs.taipe.is_varint() {
                        let context::Value::Imm(ref rhs_value) = rhs.value else {
                            unreachable!("probably some analyzer bug");
                        };
                        rhs.taipe = context::Type::Uint32;
                        rhs.value = context::Value::Imm(self.transform_varint(&rhs.taipe, rhs_value, right, None)?);
                    }
                    Ok(Context {
                        is_lvalue: false,
                        taipe: lhs.taipe.clone().add_const(),
                        value: context::Value::Shr(Box::new(lhs), Box::new(rhs)),
                    })
                } else {
                    return_err!();
                }
            }
            // Binary addition operator
            //    result = (value1) + (value2)
            // Description:
            //    Returns the arithmetic sum of two values
            // value1, value2 and result can be:
            //  * value1: {integer} value2: {integer} -> result: int
            //  * value1: iX        value2: iX        -> result: iX
            //  * value1: uX        value2: uX        -> result: uX
            //  * value1: fX        value2: fX        -> result: fX
            //  * value1: {integer} value2: iX        -> result: iX
            //  * value1: {integer} value2: uX        -> result: uX
            //  * value1: {integer} value2: fX        -> result: fX
            //  * value1: iX        value2: {integer} -> result: iX
            //  * value1: uX        value2: {integer} -> result: uX
            //  * value1: fX        value2: {integer} -> result: fX
            // note: value may be const or non-const
            TokenKind::Plus => {
                if (lhs.taipe.is_integer() || lhs.taipe.is_float()) && (rhs.taipe.is_integer() || rhs.taipe.is_float())
                {
                    self.resolve_value_promotion(&mut lhs, left, &mut rhs, right)?;
                    if lhs.taipe.remove_const() != rhs.taipe.remove_const() {
                        return_err!();
                    }
                    Ok(Context {
                        is_lvalue: false,
                        taipe: lhs.taipe.remove_const(),
                        value: context::Value::Add(Box::new(lhs), Box::new(rhs)),
                    })
                } else {
                    return_err!();
                }
            }
            // Binary subtraction operator
            //    result = (value1) - (value2)
            // Description:
            //    Returns the result of arithmetic subtraction of two values
            // value1, value2 and result can be:
            //  * value1: {integer} value2: {integer} -> result: int
            //  * value1: iX        value2: iX        -> result: iX
            //  * value1: uX        value2: uX        -> result: uX
            //  * value1: fX        value2: fX        -> result: fX
            //  * value1: {integer} value2: iX        -> result: iX
            //  * value1: {integer} value2: uX        -> result: uX
            //  * value1: {integer} value2: fX        -> result: fX
            //  * value1: iX        value2: {integer} -> result: iX
            //  * value1: uX        value2: {integer} -> result: uX
            //  * value1: fX        value2: {integer} -> result: fX
            // note: value may be const or non-const
            TokenKind::Minus => {
                if (lhs.taipe.is_integer() || lhs.taipe.is_float()) && (rhs.taipe.is_integer() || rhs.taipe.is_float())
                {
                    self.resolve_value_promotion(&mut lhs, left, &mut rhs, right)?;
                    if lhs.taipe.remove_const() != rhs.taipe.remove_const() {
                        return_err!();
                    }
                    Ok(Context {
                        is_lvalue: false,
                        taipe: lhs.taipe.remove_const(),
                        value: context::Value::Sub(Box::new(lhs), Box::new(rhs)),
                    })
                } else {
                    return_err!();
                }
            }
            // Binary multiplication operator
            //    result = (value1) * (value2)
            // Description:
            //    Returns the arithmetic product of two values
            // value1, value2 and result can be:
            //  * value1: {integer} value2: {integer} -> result: int
            //  * value1: iX        value2: iX        -> result: iX
            //  * value1: uX        value2: uX        -> result: uX
            //  * value1: fX        value2: fX        -> result: fX
            //  * value1: {integer} value2: iX        -> result: iX
            //  * value1: {integer} value2: uX        -> result: uX
            //  * value1: {integer} value2: fX        -> result: fX
            //  * value1: iX        value2: {integer} -> result: iX
            //  * value1: uX        value2: {integer} -> result: uX
            //  * value1: fX        value2: {integer} -> result: fX
            // note: value may be const or non-const
            TokenKind::Star => {
                if (lhs.taipe.is_integer() || lhs.taipe.is_float()) && (rhs.taipe.is_integer() || rhs.taipe.is_float())
                {
                    self.resolve_value_promotion(&mut lhs, left, &mut rhs, right)?;
                    if lhs.taipe.remove_const() != rhs.taipe.remove_const() {
                        return_err!();
                    }
                    Ok(Context {
                        is_lvalue: false,
                        taipe: lhs.taipe.clone().add_const(),
                        value: context::Value::Mul(Box::new(lhs), Box::new(rhs)),
                    })
                } else {
                    return_err!();
                }
            }
            // Binary division operator
            //    result = (value1) / (value2)
            // Description:
            //    Returns the quotient of the arithmetic division of two values
            // value1, value2 and result can be:
            //  * value1: {integer} value2: {integer} -> result: int
            //  * value1: iX        value2: iX        -> result: iX
            //  * value1: uX        value2: uX        -> result: uX
            //  * value1: fX        value2: fX        -> result: fX
            //  * value1: {integer} value2: iX        -> result: iX
            //  * value1: {integer} value2: uX        -> result: uX
            //  * value1: {integer} value2: fX        -> result: fX
            //  * value1: iX        value2: {integer} -> result: iX
            //  * value1: uX        value2: {integer} -> result: uX
            //  * value1: fX        value2: {integer} -> result: fX
            // note: value may be const or non-const
            TokenKind::Slash => {
                if (lhs.taipe.is_integer() || lhs.taipe.is_float()) && (rhs.taipe.is_integer() || rhs.taipe.is_float())
                {
                    self.resolve_value_promotion(&mut lhs, left, &mut rhs, right)?;
                    if lhs.taipe.remove_const() != rhs.taipe.remove_const() {
                        return_err!();
                    }
                    Ok(Context {
                        is_lvalue: false,
                        taipe: lhs.taipe.clone().add_const(),
                        value: context::Value::Div(Box::new(lhs), Box::new(rhs)),
                    })
                } else {
                    return_err!();
                }
            }
            // Binary modulo operator
            //    result = (value1) % (value2)
            // Description:
            //    Returns the arithmetic modulo of two values
            // value1, value2 and result can be:
            //  * value1: {integer} value2: {integer} -> result: int
            //  * value1: iX        value2: iX        -> result: iX
            //  * value1: uX        value2: uX        -> result: uX
            //  * value1: {integer} value2: iX        -> result: iX
            //  * value1: {integer} value2: uX        -> result: uX
            //  * value1: iX        value2: {integer} -> result: iX
            //  * value1: uX        value2: {integer} -> result: uX
            // note: value may be const or non-const
            TokenKind::Percent => {
                if lhs.taipe.is_integer() && rhs.taipe.is_integer() {
                    self.resolve_value_promotion(&mut lhs, left, &mut rhs, right)?;
                    if lhs.taipe.remove_const() != rhs.taipe.remove_const() {
                        return_err!();
                    }
                    Ok(Context {
                        is_lvalue: false,
                        taipe: lhs.taipe.clone().add_const(),
                        value: context::Value::Rem(Box::new(lhs), Box::new(rhs)),
                    })
                } else {
                    return_err!();
                }
            }
            _ => {
                return_err!();
            }
        }
    }

    fn visit_unary(&mut self, op: &Token, expr: &'a ast::Expr) -> CompileResult<Context<'a>> {
        let ctx = self.visit_expr(expr)?;
        match op.kind {
            // Unary minus operator
            //    result = -(value)
            // Description:
            //    Negates a signed integer or float
            // value and result can be:
            //  * value: {integer} -> result: int
            //  * value: iX        -> result: iX
            //  * value: fX        -> result: fX
            // note: value may be const or non-const
            TokenKind::Minus => match ctx.taipe.remove_const() {
                context::Type::VarInt => Ok(Context {
                    is_lvalue: false,
                    taipe: self.type_int.clone(),
                    value: {
                        let context::Value::Imm(value) = ctx.value else {
                            unreachable!("probably some analyzer bug");
                        };
                        context::Value::Imm(self.transform_varint_to_int(&value, expr)?.negate())
                    },
                    // value: if let Some(value) = ctx.value {
                    //     Some(self.transform_varint_to_int(&value, expr)?.negate())
                    // } else {
                    //     None
                    // },
                }),
                context::Type::Int8
                | context::Type::Int16
                | context::Type::Int32
                | context::Type::Int64
                | context::Type::Int128
                | context::Type::Float32
                | context::Type::Float64 => Ok(Context {
                    is_lvalue: false,
                    taipe: ctx.taipe.clone().remove_const(),
                    value: context::Value::Negate(Box::new(ctx)),
                }),
                context::Type::Uint8
                | context::Type::Uint16
                | context::Type::Uint32
                | context::Type::Uint64
                | context::Type::Uint128 => {
                    return Err(self.make_err(
                        format!(
                            "cannot apply '-' operator on type '{}': unsigned values cannot be negated",
                            ctx.taipe.to_string()
                        ),
                        expr,
                    ));
                }
                _ => {
                    return Err(self.make_err(
                        format!("cannot apply '-' operator on type '{}'", ctx.taipe.to_string()),
                        expr,
                    ));
                }
            },
            // Unary bit flip operator
            //    result = ~(value)
            // Description:
            //    Flips all the bits of an signed or unsigned integer
            // value and result can be:
            //  * value: {integer} -> result: int
            //  * value: iX        -> result: iX
            //  * value: uX        -> result: uX
            // note: value may be const or non-const
            TokenKind::Tilde => match ctx.taipe.remove_const() {
                context::Type::VarInt => Ok(Context {
                    is_lvalue: false,
                    taipe: self.type_int.clone(),
                    value: {
                        let context::Value::Imm(value) = ctx.value else {
                            unreachable!("probably some analyzer bug");
                        };
                        context::Value::Imm(self.transform_varint_to_int(&value, expr)?.flip_bits())
                    },
                }),
                context::Type::Int8
                | context::Type::Int16
                | context::Type::Int32
                | context::Type::Int64
                | context::Type::Int128
                | context::Type::Uint8
                | context::Type::Uint16
                | context::Type::Uint32
                | context::Type::Uint64
                | context::Type::Uint128 => Ok(Context {
                    is_lvalue: false,
                    taipe: ctx.taipe.clone().remove_const(),
                    value: context::Value::FlipBits(Box::new(ctx)),
                }),
                _ => {
                    return Err(self.make_err(
                        format!("cannot apply '~' operator on type '{}'", ctx.taipe.to_string()),
                        expr,
                    ));
                }
            },
            // Unary dereference operator
            //    result = *(value)
            // Description:
            //    Dereferences the value of a pointer at the specific address
            // value and result can be:
            //  * value: *T        -> result: T
            // note: value may be const or non-const
            // TODO: comptime: what about implementing this in comptime
            // There are many edge cases and memory safety violation
            TokenKind::Star => match ctx.taipe.remove_const() {
                context::Type::Pointer(taipe) => Ok(Context {
                    is_lvalue: true,
                    taipe: *taipe,
                    value: context::Value::Deref(Box::new(ctx)),
                }),
                _ => {
                    return Err(self.make_err(format!("cannot dereference type '{}'", ctx.taipe.to_string()), expr));
                }
            },
            // Unary address of operator
            //    result = &(value)
            // Description:
            //    Returns the address of the specific value
            // value and result can be:
            //  * value: T         -> result: *T
            //      T cannot be:
            //       * module
            //       * typedef
            //       * void
            //       * noreturn
            //  * value: {integer} -> result: *const int
            // note: const-ness of value is tranferred to the result
            //       for example: `const int` becomes `*const int`
            // TODO: comptime: what about implementing this in comptime
            // There are many edge cases and memory safety violation
            TokenKind::Ampersand => {
                fn is_addressable<'b>(taipe: &context::Type<'b>) -> bool {
                    match taipe {
                        context::Type::VarInt => true,
                        context::Type::Const(taipe) => is_addressable(taipe),
                        context::Type::Module
                        | context::Type::Typedef
                        | context::Type::Void
                        | context::Type::Noreturn => false,
                        _ => true,
                    }
                }
                if !is_addressable(&ctx.taipe) {
                    return Err(self.make_err(
                        format!("cannot take address of value of type '{}'", ctx.taipe.to_string()),
                        expr,
                    ));
                }
                if !ctx.is_lvalue {
                    return Err(self.make_err("cannot take address of a prvalue (pure rvalue)", expr));
                }
                assert!(!ctx.taipe.is_varint());
                Ok(Context {
                    is_lvalue: false,
                    taipe: context::Type::Pointer(Box::new(ctx.taipe.clone())),
                    value: context::Value::AddrOf(Box::new(ctx)),
                })
            }
            // Unary sizeof operator
            //    result = sizeof(value)
            // Description:
            //    Returns the size of the value in memory in bytes
            // value and result can be:
            //  * value: T         -> result: usize
            //  * value: typedef   -> result: usize
            //      T cannot be:
            //       * module
            //       * void
            //       * noreturn
            //       * {integer}
            // note: value may be const or non-const
            TokenKind::Sizeof => {
                fn is_sizeof_permitted<'b>(taipe: &context::Type<'b>) -> bool {
                    match taipe {
                        context::Type::VarInt => false,
                        context::Type::Const(taipe) => is_sizeof_permitted(taipe),
                        context::Type::Module | context::Type::Void | context::Type::Noreturn => false,
                        _ => true,
                    }
                }
                if !is_sizeof_permitted(&ctx.taipe) {
                    return Err(self.make_err(
                        format!("cannot take sizeof value of type '{}'", ctx.taipe.to_string()),
                        expr,
                    ));
                }
                let taipe = match ctx.taipe {
                    context::Type::Typedef => {
                        let context::Value::Imm(value) = ctx.value else {
                            unreachable!("probably some analyzer bug");
                        };
                        let context::Imm::Type(taipe) = value else {
                            unreachable!("probably some analyzer bug");
                        };
                        taipe
                    }
                    taipe => taipe,
                };
                let size = self.get_sizeof(&taipe, expr)?;
                self.usize2usize(size, expr)
            }
            // Unary alignof operator
            //    result = alignof(value)
            // Description:
            //    Returns the memory alignment of the value in bytes
            // value and result can be:
            //  * value: T         -> result: usize
            //  * value: typedef   -> result: usize
            //      T cannot be:
            //       * module
            //       * void
            //       * noreturn
            //       * {integer}
            // note: value may be const or non-const
            TokenKind::Alignof => {
                fn is_alignof_permitted<'b>(taipe: &context::Type<'b>) -> bool {
                    match taipe {
                        context::Type::VarInt => false,
                        context::Type::Const(taipe) => is_alignof_permitted(taipe),
                        context::Type::Module | context::Type::Void | context::Type::Noreturn => false,
                        _ => true,
                    }
                }
                if !is_alignof_permitted(&ctx.taipe) {
                    return Err(self.make_err(
                        format!("cannot take alignof value of type '{}'", ctx.taipe.to_string()),
                        expr,
                    ));
                }
                let taipe = match ctx.taipe {
                    context::Type::Typedef => {
                        let context::Value::Imm(value) = ctx.value else {
                            unreachable!("probably some analyzer bug");
                        };
                        let context::Imm::Type(taipe) = value else {
                            unreachable!("probably some analyzer bug");
                        };
                        taipe
                    }
                    taipe => taipe,
                };
                let align = self.get_alignof(&taipe, expr)?;
                self.usize2usize(align, expr)
            }
            // Unary typeof operator
            //    result = typeof(value)
            // Description:
            //    Returns the type of the value
            // value and result can be:
            //  * value: T         -> result: typedef = T
            //      T cannot be:
            //       * module
            //       * typedef
            //       * noreturn
            //       * {integer}
            // note: value may be const or non-const
            TokenKind::Typeof => {
                fn is_typeof_permitted<'b>(taipe: &context::Type<'b>) -> bool {
                    match taipe {
                        context::Type::Const(taipe) => is_typeof_permitted(taipe),
                        context::Type::VarInt
                        | context::Type::Module
                        | context::Type::Typedef
                        | context::Type::Noreturn => false,
                        _ => true,
                    }
                }
                if is_typeof_permitted(&ctx.taipe) {
                    return Err(self.make_err(
                        format!("cannot use typeof operator on type '{}'", ctx.taipe.to_string()),
                        expr,
                    ));
                }
                Ok(Context::from_type(ctx.taipe))
            }
            // Unary logical not operator
            //    result = not(value)
            // Description:
            //    Returns the logical opposite of value
            //    for example: `true` gives `false` and `false` gives `true`
            // value and result can be:
            //  * value: bool      -> result: bool
            // note: value may be const or non-const
            TokenKind::Not => {
                // comptime: perform logical not
                if !ctx.taipe.is_bool() {
                    return Err(self.make_err(
                        format!("cannot use not operator on type '{}'", ctx.taipe.to_string()),
                        expr,
                    ));
                }
                Ok(Context {
                    is_lvalue: false,
                    taipe: context::Type::Bool,
                    value: context::Value::Not(Box::new(ctx)),
                })
            }
            _ => unreachable!("probably some parser bug"),
        }
    }

    fn get_sizeof(&mut self, taipe: &context::Type<'a>, line_info: &impl HasLineInfo) -> CompileResult<usize> {
        Ok(self.resolve_layout(taipe, line_info)?.size)
    }

    fn get_alignof(&mut self, taipe: &context::Type<'a>, line_info: &impl HasLineInfo) -> CompileResult<usize> {
        Ok(self.resolve_layout(taipe, line_info)?.alignment)
    }

    fn resolve_layout(&mut self, taipe: &context::Type<'a>, line_info: &impl HasLineInfo) -> CompileResult<Layout> {
        // (usize, usize) -> (size, alignment)
        // size (in bytes) -> always a multiple of alignment
        // alignment (in bytes) -> always a power of 2
        self.resolve_layout_ex(taipe, line_info.get_line_info())
    }

    fn resolve_layout_ex(&mut self, taipe: &context::Type<'a>, line_info: LineInfo) -> CompileResult<Layout> {
        let layout = match taipe {
            context::Type::Bool => Layout { size: 1, alignment: 1 },
            context::Type::Char => Layout { size: 1, alignment: 1 },
            context::Type::Int8 | context::Type::Uint8 => Layout { size: 1, alignment: 1 },
            context::Type::Int16 | context::Type::Uint16 => Layout { size: 2, alignment: 2 },
            context::Type::Int32 | context::Type::Uint32 => Layout { size: 4, alignment: 4 },
            context::Type::Int64 | context::Type::Uint64 => Layout { size: 8, alignment: 8 },
            context::Type::Int128 | context::Type::Uint128 => Layout {
                size: 16,
                alignment: 16,
            },
            context::Type::Float32 => Layout { size: 4, alignment: 4 },
            context::Type::Float64 => Layout { size: 8, alignment: 8 },
            context::Type::Const(taipe) => self.resolve_layout_ex(taipe, line_info)?,
            context::Type::Basic(scope) => self.resolve_layout_scope(scope)?,
            context::Type::Function { ret: _, params: _ } | context::Type::Pointer(_) => {
                // On a low level, a function is nothing but a pointer
                // to the starting of the code section in memory.
                // Calling a function is nothing but bumping the instruction pointer.
                // Functions are first class and they are nothing
                // but special kind of pointers.
                Layout {
                    size: self.settings.pointer_size,
                    alignment: self.settings.pointer_size,
                }
            }
            context::Type::Array { count, taipe } => {
                let Layout { size, alignment } = self.resolve_layout_ex(taipe, line_info)?;
                Layout {
                    size: count * size,
                    alignment,
                }
            }
            context::Type::Fat(_) => {
                // Definition of fat pointer type:
                // |   []T :: struct {
                // |       count: usize,
                // |       ptr: *T,
                // |   }
                // Size:      pointer_size + pointer_size
                // Alignment: pointer_size + pointer_size
                Layout {
                    size: 2 * self.settings.pointer_size,
                    alignment: 2 * self.settings.pointer_size,
                }
            }
            context::Type::Tuple(items) => self.resolve_layout_tuple(items, line_info)?,
            context::Type::VarInt
            | context::Type::Module
            | context::Type::Typedef
            | context::Type::Void
            | context::Type::Noreturn => {
                return Err(self.make_err(
                    format!("type has no memory layout, problem type is '{}'", taipe.to_string()),
                    &line_info,
                ));
            }
        };
        Ok(layout)
    }

    fn resolve_layout_tuple(&mut self, types: &[context::Type<'a>], line_info: LineInfo) -> CompileResult<Layout> {
        fn eval_padding(offset: usize, alignment: usize) -> usize {
            // Calculate the misalignment
            let misalignment = offset % alignment;
            // Add the padding
            let padding = if misalignment > 0 { alignment - misalignment } else { 0 };
            padding
        }
        let mut tuple_alignment = 1usize;
        let mut cur_offset = 0;
        let offset_start = cur_offset;
        for taipe in types {
            // Set the offset of field
            let layout = self.resolve_layout_ex(taipe, line_info)?;
            // Advance the offset
            cur_offset += layout.size;
            // Add the padding
            cur_offset += eval_padding(cur_offset, layout.alignment);
            // Alignment of a struct is the alignment of the most aligned field
            tuple_alignment = tuple_alignment.max(layout.alignment);
        }
        // Add the final padding
        cur_offset += eval_padding(cur_offset, tuple_alignment);
        // Calculate the size
        let mut tuple_size = cur_offset - offset_start;
        // Empty tuples are not entirely empty they have size of 1 byte
        if tuple_size == 0 {
            tuple_size = tuple_alignment;
        }
        Ok(Layout {
            size: tuple_size,
            alignment: tuple_alignment,
        })
    }

    fn resolve_layout_scope(&mut self, scope: &Rc<RefCell<scope::Scope<'a>>>) -> CompileResult<Layout> {
        let scope_ref = scope.borrow();
        match &scope_ref.payload {
            Payload::Compound(compound) => {
                let compound = compound.clone();
                drop(scope_ref);
                scope.borrow_mut().payload = scope::Payload::LayoutResolutionInProg;
                let mut offsets = HashMap::<String, scope::FieldData>::new();
                // Resolve layout info for the struct or union or field
                let layout = self.resolve_layout_field(&compound.field, 0, &mut offsets, &|name| {
                    // Give child line info when requested
                    scope.borrow().children[&name.to_string()].borrow().get_line_info()
                });
                let layout = match layout {
                    Ok(layout) => layout,
                    Err(CompileError::SemCyclic { file_path, line_info }) => {
                        return Err(self
                            .make_err(
                                "memory layout is ambiguous, encountered cyclic references",
                                &scope.borrow(),
                            )
                            .chain(self.make_note_with_path("cycle occurs here", file_path, &line_info)));
                    }
                    Err(err) => return Err(err),
                };
                // Reset the payload
                scope.borrow_mut().payload = scope::Payload::Compound(scope::Compound {
                    field: compound.field,
                    layout,
                    offsets,
                });
                Ok(layout)
            }
            Payload::LayoutResolutionInProg | Payload::None => {
                return Err(CompileError::SemCyclic {
                    file_path: scope.borrow().get_src_path(),
                    line_info: scope.borrow().get_line_info(),
                });
            }
            Payload::Function(_) | Payload::Block => unreachable!("probably some analyzer bug"),
        }
    }

    fn resolve_layout_field<F>(
        &mut self,
        field: &scope::Field<'a>,
        mut cur_offset: usize,
        offset_table: &mut HashMap<String, scope::FieldData>,
        get_line_info_of_field: &F,
    ) -> CompileResult<Layout>
    where
        F: Fn(&str) -> LineInfo,
    {
        fn eval_padding(offset: usize, alignment: usize) -> usize {
            // Calculate the misalignment
            let misalignment = offset % alignment;
            // Add the padding
            let padding = if misalignment > 0 { alignment - misalignment } else { 0 };
            padding
        }

        match field {
            scope::Field::Struct(fields) => {
                let mut struct_alignment = 1usize;
                let offset_start = cur_offset;
                for field in fields {
                    // Set the offset of field
                    let layout = self.resolve_layout_field(field, cur_offset, offset_table, get_line_info_of_field)?;
                    // Advance the offset
                    cur_offset += layout.size;
                    // Add the padding
                    cur_offset += eval_padding(cur_offset, layout.alignment);
                    // Alignment of a struct is the alignment of the most aligned field
                    struct_alignment = struct_alignment.max(layout.alignment);
                }
                // Add the final padding
                cur_offset += eval_padding(cur_offset, struct_alignment);
                // Calculate the size
                let mut struct_size = cur_offset - offset_start;
                // Empty structs are not entirely empty they have size of 1 byte
                if struct_size == 0 {
                    struct_size = struct_alignment;
                }
                Ok(Layout {
                    size: struct_size,
                    alignment: struct_alignment,
                })
            }
            scope::Field::Union(fields) => {
                let mut union_alignment = 1usize;
                let mut union_size = 0usize;
                // Calculate
                for field in fields.iter() {
                    // Set the offset of field
                    let layout = self.resolve_layout_field(field, cur_offset, offset_table, get_line_info_of_field)?;
                    // Size of a union is the size of the largest field
                    union_size = union_size.max(layout.size);
                    // Alignment of a union is the alignment of the most aligned field
                    union_alignment = union_alignment.max(layout.alignment);
                }
                // Empty structs are not entirely empty they have size of 1 byte
                if union_size == 0 {
                    union_size = union_alignment;
                }
                Ok(Layout {
                    size: union_size,
                    alignment: union_alignment,
                })
            }
            scope::Field::Field {
                file_path,
                line_info,
                name,
                taipe,
                scope: _,
            } => {
                let layout = self.resolve_layout_ex(&taipe, get_line_info_of_field(name));
                let layout = match layout {
                    Ok(layout) => layout,
                    Err(CompileError::SemCyclic {
                        file_path: _,
                        line_info: _,
                    }) => {
                        return Err(CompileError::SemCyclic {
                            file_path: file_path.clone(),
                            line_info: *line_info,
                        });
                    }
                    Err(err) => return Err(err),
                };
                // Place this field at the specified offset
                offset_table.insert(
                    name.clone(),
                    scope::FieldData {
                        offset: cur_offset,
                        size: layout.size,
                        alignment: layout.alignment,
                    },
                );
                Ok(layout)
            }
        }
    }

    /// In case of declaration, 'eq_token' is the token that separates lhs and rhs.
    /// In case of assignment, 'eq_token' should always be None
    fn resolve_assign(
        &mut self,
        lhs: Option<(context::Type<'a>, LineInfo)>,
        eq_token: Option<&Token>,
        mut rhs: Option<(Context<'a>, LineInfo)>,
    ) -> CompileResult<Context<'a>> {
        // Fix {integer} problem:
        // need to convert to lhs type if it is a integer or float
        // otherwise int if there no lhs type info
        if let Some((
            Context {
                is_lvalue: _,
                taipe: ref mut rhs_type,
                value: ref mut rhs_value,
            },
            rhs_line_info,
        )) = rhs
            && rhs_type.is_varint()
        {
            if let Some((ref lhs_type, _)) = lhs {
                if lhs_type.is_integer() && !lhs_type.is_varint() {
                    let context::Value::Imm(rhs_value) = rhs_value else {
                        unreachable!("probably some analyzer bug");
                    };
                    *rhs_type = lhs_type.clone();
                    *rhs_value = self.transform_varint(lhs_type, rhs_value, &rhs_line_info, None)?;
                }
            } else {
                let context::Value::Imm(rhs_value) = rhs_value else {
                    unreachable!("probably some analyzer bug");
                };
                *rhs_type = self.type_int.clone();
                *rhs_value = self.transform_varint_to_int(rhs_value, &rhs_line_info)?;
            }
        }
        match (lhs, rhs) {
            (None, None) => panic!("either type or value information should be present"),
            // Situation
            // ---------------------------------
            // name :: value;
            // name := value;
            // ---------------------------------
            (None, Some((rhs, _rhs_line_info))) => {
                let Some(eq_token) = eq_token else {
                    unreachable!("probably some analyzer bug");
                };
                match eq_token.kind {
                    // Situation
                    // ---------------------------------
                    // name :: value;
                    // ---------------------------------
                    TokenKind::Colon => Ok(Context {
                        is_lvalue: false,
                        taipe: rhs.taipe.add_const(),
                        value: rhs.value,
                    }),
                    // Situation
                    // ---------------------------------
                    // name := value;
                    // ---------------------------------
                    TokenKind::Equal => {
                        let lhs = rhs.taipe.remove_const();
                        if lhs.is_const() {
                            return Err(self.make_err("expected ':'", eq_token));
                        }
                        Ok(Context {
                            is_lvalue: false,
                            taipe: lhs,
                            value: rhs.value,
                        })
                    }
                    _ => {
                        unreachable!("probably some parser bug");
                    }
                }
            }
            // Situation
            // ---------------------------------
            // name: type;
            // ---------------------------------
            (Some((lhs, _)), None) => {
                assert!(eq_token.is_none());
                Ok(Context {
                    is_lvalue: false,
                    taipe: lhs,
                    // TODO: check for default values
                    value: context::Value::from_nil(),
                })
            }
            // Situation
            // ---------------------------------
            // name : type : value;
            // name : type = value;
            // expr = expr;
            // ---------------------------------
            (Some((lhs, lhs_line_info)), Some((rhs, rhs_line_info))) => {
                let mut allow_assign_to_const = false;
                if let Some(eq_token) = eq_token {
                    match eq_token.kind {
                        // Situation
                        // ---------------------------------
                        // name : type : value;
                        // ---------------------------------
                        TokenKind::Colon => {
                            allow_assign_to_const = true;
                        }
                        // Situation
                        // ---------------------------------
                        // name : type = value;
                        // ---------------------------------
                        TokenKind::Equal => {
                            if lhs.is_const() {
                                return Err(self.make_err("expected ':'", eq_token));
                            }
                        }
                        _ => {
                            unreachable!("probably some parser bug");
                        }
                    }
                }
                // Type checking and implicit casting
                self.resolve_implicit_cast(lhs, lhs_line_info, rhs, rhs_line_info, allow_assign_to_const)
            }
        }
    }

    fn resolve_implicit_cast(
        &mut self,
        mut lhs: context::Type<'a>,
        lhs_line_info: LineInfo,
        mut rhs: Context<'a>,
        rhs_line_info: LineInfo,
        allow_assign_to_const: bool,
    ) -> CompileResult<Context<'a>> {
        macro_rules! return_err_const {
            () => {
                return Err(self
                    .make_err(
                        format!("cannot assign to a constant of type: '{}'", lhs.to_string()),
                        &lhs_line_info,
                    )
                    .chain(self.make_note(format!("type of value is '{}'", rhs.to_string()), &rhs_line_info)));
            };
        }
        macro_rules! return_err {
            () => {
                return Err(self
                    .make_err(
                        format!("cannot assign value of type '{}'", rhs.to_string()),
                        &rhs_line_info,
                    )
                    .chain(self.make_note(format!("cannot assign to '{}'", lhs.to_string()), &lhs_line_info)));
            };
        }
        // const qualifier in rhs does not matter at all during assignment
        // as values are always copied (except for pointers of course)
        rhs.taipe = rhs.taipe.remove_const();
        if allow_assign_to_const {
            // If this is a first assignment to a constant
            // Behave as if the constant has no const qualifier to its type
            lhs = lhs.remove_const();
        }
        // Type checking and Implicit conversions
        let value = match (&lhs, &rhs.taipe) {
            // Implicit integer conversions
            (context::Type::Int128, context::Type::Int64)
            | (context::Type::Int128, context::Type::Int32)
            | (context::Type::Int128, context::Type::Int16)
            | (context::Type::Int128, context::Type::Int8)
            | (context::Type::Int64, context::Type::Int32)
            | (context::Type::Int64, context::Type::Int16)
            | (context::Type::Int64, context::Type::Int8)
            | (context::Type::Int32, context::Type::Int16)
            | (context::Type::Int32, context::Type::Int8)
            | (context::Type::Int16, context::Type::Int8)
            | (context::Type::Uint128, context::Type::Uint64)
            | (context::Type::Uint128, context::Type::Uint32)
            | (context::Type::Uint128, context::Type::Uint16)
            | (context::Type::Uint128, context::Type::Uint8)
            | (context::Type::Uint64, context::Type::Uint32)
            | (context::Type::Uint64, context::Type::Uint16)
            | (context::Type::Uint64, context::Type::Uint8)
            | (context::Type::Uint32, context::Type::Uint16)
            | (context::Type::Uint32, context::Type::Uint8)
            | (context::Type::Uint16, context::Type::Uint8) => context::Value::Cast(Box::new(rhs)),
            (context::Type::Float32, context::Type::VarInt) => {
                let context::Value::Imm(value) = rhs.value else {
                    unreachable!("probably some analyzer bug")
                };
                let context::Imm::VarInt(value) = value else {
                    unreachable!("probably some analyzer bug");
                };
                let Some(value) = value.to_f32() else {
                    return Err(self.make_err(format!("'f32' cannot hold this value: '{}'", value), &rhs_line_info));
                };
                context::Value::Imm(context::Imm::Float32(value))
            }
            (context::Type::Float64, context::Type::VarInt) => {
                let context::Value::Imm(value) = rhs.value else {
                    unreachable!("probably some analyzer bug")
                };
                let context::Imm::VarInt(value) = value else {
                    unreachable!("probably some analyzer bug");
                };
                let Some(value) = value.to_f64() else {
                    return Err(self.make_err(format!("'f64' cannot hold this value: '{}'", value), &rhs_line_info));
                };
                context::Value::Imm(context::Imm::Float64(value))
            }
            (context::Type::Float32, context::Type::Float64) => context::Value::Cast(Box::new(rhs)),
            (context::Type::Const(_), _) => {
                if !allow_assign_to_const {
                    return_err_const!();
                }
                unreachable!("not supposed to happen")
            }
            (context::Type::Pointer(lhs_ptr), context::Type::Pointer(rhs_ptr)) => {
                //       *T = *T       (Valid)
                // *const T = *T       (Valid)
                //       *T = *const T (Invalid)
                // *const T = *const T (Valid)
                if !lhs_ptr.is_const() && rhs_ptr.is_const() {
                    return_err!();
                }
                if lhs_ptr.remove_const() != rhs_ptr.remove_const() {
                    return_err!();
                }
                rhs.value
            }
            (
                context::Type::Fat(lhs_type),
                context::Type::Array {
                    count: _,
                    taipe: rhs_type,
                },
            ) => {
                // array type can be coerced to a fat pointer
                if lhs_type != rhs_type {
                    return_err!();
                }
                context::Value::Cast(Box::new(rhs))
            }
            (context::Type::Noreturn, _) => {
                return Err(self.make_err(format!("cannot assign to: '{}'", lhs.to_string()), &lhs_line_info));
            }
            (_, context::Type::Noreturn) => {
                // noreturn type can be coerced to any type
                context::Value::from_nil()
            }
            (lhs, rhs_type) => {
                if lhs != rhs_type {
                    return_err!();
                }
                rhs.value
            }
        };
        if allow_assign_to_const {
            // Now add the constant qualifier to the type
            lhs = lhs.add_const();
        }
        Ok(Context {
            is_lvalue: false,
            taipe: lhs,
            value,
        })
    }

    fn get_member(&mut self, scope: &Rc<RefCell<scope::Scope<'a>>>, name: &Token) -> CompileResult<Context<'a>> {
        let mut searched_names = HashSet::new();
        if let Some(ctx) = self.resolve_member(&scope, &name.text, &mut searched_names)? {
            Ok(ctx)
        } else {
            Err(self
                .make_err(
                    format!(
                        "'{}' has no member named '{}'",
                        scope.borrow().sym_path.to_string(),
                        &name.text
                    ),
                    name,
                )
                .chain(self.make_did_you_mean_help(&name.text, &searched_names)))
        }
    }

    fn resolve_member(
        &mut self,
        scope: &Rc<RefCell<scope::Scope<'a>>>,
        name: &str,
        searched_names: &mut HashSet<String>,
    ) -> CompileResult<Option<Context<'a>>> {
        if let Some(child) = scope.borrow().children.get(name) {
            let node = match &child.borrow().state {
                scope::State::NotVisited(node) => node.clone(),
                scope::State::VisitInProg => {
                    return Err(CompileError::SemCyclic {
                        file_path: child.borrow().get_src_path(),
                        line_info: child.borrow().get_line_info(),
                    });
                }
                scope::State::Visited(ctx) => {
                    if ctx.taipe.is_typedef() {
                        return Ok(Some(Context {
                            is_lvalue: true,
                            taipe: context::Type::Typedef,
                            value: context::Value::Imm(context::Imm::Type(context::Type::Basic(Rc::clone(child)))),
                        }));
                    } else {
                        return Ok(Some(Context::from_scope(&ctx.taipe, child)));
                    }
                }
            };
            // Begin new scope
            let old_cur_scope = Rc::clone(&self.cur_scope);
            self.cur_scope = Rc::clone(&scope);
            // Visit the decl (and not the subsequent children)
            let ctx = match node {
                scope::ScopeNode::Decl(decl) => self.visit_decl(decl, false)?,
                scope::ScopeNode::Field(_) => {
                    // unreachable!("probably some analyzer bug")
                    return Ok(None);
                }
                scope::ScopeNode::Object(_) => {
                    unreachable!("probably some analyzer bug")
                }
            };
            // Restore old scope
            self.cur_scope = old_cur_scope;
            Ok(Some(ctx))
        } else {
            // For better errors
            for name in scope.borrow().children.keys() {
                searched_names.insert(name.clone());
            }
            Ok(None)
        }
    }

    fn get_name(&mut self, name: &Token) -> CompileResult<Context<'a>> {
        let mut searched_names = HashSet::new();
        if let Some(ctx) = self.resolve_name(&name.text, &mut searched_names)? {
            Ok(ctx)
        } else {
            Err(self
                .make_err("undefined reference", name)
                .chain(self.make_did_you_mean_help(&name.text, &searched_names)))
        }
    }

    fn resolve_name(&mut self, name: &str, searched_names: &mut HashSet<String>) -> CompileResult<Option<Context<'a>>> {
        {
            // Check in the current scope and go upwards
            let mut scope = Rc::clone(&self.cur_scope);
            loop {
                match self.resolve_member(&scope, name, searched_names) {
                    Ok(Some(ctx)) => return Ok(Some(ctx)),
                    Ok(None) => {}
                    // It is referencing cyclic, probably user refers something
                    // from the outer scope. Lets check that.
                    Err(CompileError::SemCyclic {
                        file_path: _,
                        line_info: _,
                    }) => {}
                    Err(err) => return Err(err),
                }
                let parent_opt = scope.borrow().parent.upgrade();
                if let Some(parent) = parent_opt.as_ref() {
                    scope = Rc::clone(parent);
                } else {
                    break;
                }
            }
        }
        match name {
            "__bool" => Ok(Some(Context::from_type(context::Type::Bool))),
            "__char" => Ok(Some(Context::from_type(context::Type::Char))),
            "__i8" => Ok(Some(Context::from_type(context::Type::Int8))),
            "__i16" => Ok(Some(Context::from_type(context::Type::Int16))),
            "__i32" => Ok(Some(Context::from_type(context::Type::Int32))),
            "__i64" => Ok(Some(Context::from_type(context::Type::Int64))),
            "__i128" => Ok(Some(Context::from_type(context::Type::Int128))),
            "__int" => Ok(Some(Context::from_type(self.type_int.clone()))),
            "__isize" => Ok(Some(Context::from_type(self.type_isize.clone()))),
            "__u8" => Ok(Some(Context::from_type(context::Type::Uint8))),
            "__u16" => Ok(Some(Context::from_type(context::Type::Uint16))),
            "__u32" => Ok(Some(Context::from_type(context::Type::Uint32))),
            "__u64" => Ok(Some(Context::from_type(context::Type::Uint64))),
            "__u128" => Ok(Some(Context::from_type(context::Type::Uint128))),
            "__uint" => Ok(Some(Context::from_type(self.type_uint.clone()))),
            "__usize" => Ok(Some(Context::from_type(self.type_usize.clone()))),
            "__f32" => Ok(Some(Context::from_type(context::Type::Float32))),
            "__f64" => Ok(Some(Context::from_type(context::Type::Float64))),
            _ => Ok(None),
        }
    }

    fn transform_imm(
        &self,
        lhs: &context::Type<'a>,
        rhs: &context::Imm<'a>,
        line_info: &impl HasLineInfo,
        type_name: Option<&str>,
    ) -> CompileResult<context::Imm<'a>> {
        match (lhs, rhs) {
            (context::Type::Const(lhs), _) => self.transform_imm(lhs, rhs, line_info, type_name),
            (_, context::Imm::VarInt(_)) => Ok(self.transform_varint(lhs, rhs, line_info, type_name)?),
            // Trivial conversions
            (context::Type::Int128, context::Imm::Int128(_)) => Ok(rhs.clone()),
            (context::Type::Int64, context::Imm::Int64(_)) => Ok(rhs.clone()),
            (context::Type::Int32, context::Imm::Int32(_)) => Ok(rhs.clone()),
            (context::Type::Int16, context::Imm::Int16(_)) => Ok(rhs.clone()),
            (context::Type::Int8, context::Imm::Int8(_)) => Ok(rhs.clone()),
            (context::Type::Uint128, context::Imm::Uint128(_)) => Ok(rhs.clone()),
            (context::Type::Uint64, context::Imm::Uint64(_)) => Ok(rhs.clone()),
            (context::Type::Uint32, context::Imm::Uint32(_)) => Ok(rhs.clone()),
            (context::Type::Uint16, context::Imm::Uint16(_)) => Ok(rhs.clone()),
            (context::Type::Uint8, context::Imm::Uint8(_)) => Ok(rhs.clone()),
            // Implicit signed integer conversions
            (context::Type::Int128, context::Imm::Int64(value)) => Ok(context::Imm::Int128((*value).into())),
            (context::Type::Int128, context::Imm::Int32(value)) => Ok(context::Imm::Int128((*value).into())),
            (context::Type::Int128, context::Imm::Int16(value)) => Ok(context::Imm::Int128((*value).into())),
            (context::Type::Int128, context::Imm::Int8(value)) => Ok(context::Imm::Int128((*value).into())),
            (context::Type::Int64, context::Imm::Int32(value)) => Ok(context::Imm::Int64((*value).into())),
            (context::Type::Int64, context::Imm::Int16(value)) => Ok(context::Imm::Int64((*value).into())),
            (context::Type::Int64, context::Imm::Int8(value)) => Ok(context::Imm::Int64((*value).into())),
            (context::Type::Int32, context::Imm::Int16(value)) => Ok(context::Imm::Int32((*value).into())),
            (context::Type::Int32, context::Imm::Int8(value)) => Ok(context::Imm::Int32((*value).into())),
            (context::Type::Int16, context::Imm::Int8(value)) => Ok(context::Imm::Int16((*value).into())),
            // Implicit unsigned integer conversions
            (context::Type::Uint128, context::Imm::Uint64(value)) => Ok(context::Imm::Uint128((*value).into())),
            (context::Type::Uint128, context::Imm::Uint32(value)) => Ok(context::Imm::Uint128((*value).into())),
            (context::Type::Uint128, context::Imm::Uint16(value)) => Ok(context::Imm::Uint128((*value).into())),
            (context::Type::Uint128, context::Imm::Uint8(value)) => Ok(context::Imm::Uint128((*value).into())),
            (context::Type::Uint64, context::Imm::Uint32(value)) => Ok(context::Imm::Uint64((*value).into())),
            (context::Type::Uint64, context::Imm::Uint16(value)) => Ok(context::Imm::Uint64((*value).into())),
            (context::Type::Uint64, context::Imm::Uint8(value)) => Ok(context::Imm::Uint64((*value).into())),
            (context::Type::Uint32, context::Imm::Uint16(value)) => Ok(context::Imm::Uint32((*value).into())),
            (context::Type::Uint32, context::Imm::Uint8(value)) => Ok(context::Imm::Uint32((*value).into())),
            (context::Type::Uint16, context::Imm::Uint8(value)) => Ok(context::Imm::Uint16((*value).into())),
            _ => panic!("invalid type for value conversion"),
        }
    }

    fn transform_imm_to_usize(
        &self,
        value: &context::Imm<'a>,
        line_info: &impl HasLineInfo,
    ) -> CompileResult<context::Imm<'a>> {
        self.transform_imm(&self.type_usize, value, line_info, Some("usize"))
    }

    fn transform_varint(
        &self,
        lhs: &context::Type<'a>,
        rhs: &context::Imm<'a>,
        line_info: &impl HasLineInfo,
        type_name: Option<&str>,
    ) -> CompileResult<context::Imm<'a>> {
        match rhs {
            context::Imm::VarInt(num) => {
                let num = &num.num;
                let opt = match lhs {
                    context::Type::Int8 => num.to_i8().map(|num| context::Imm::Int8(num)),
                    context::Type::Int16 => num.to_i16().map(|num| context::Imm::Int16(num)),
                    context::Type::Int32 => num.to_i32().map(|num| context::Imm::Int32(num)),
                    context::Type::Int64 => num.to_i64().map(|num| context::Imm::Int64(num)),
                    context::Type::Int128 => num.to_i128().map(|num| context::Imm::Int128(num)),
                    context::Type::Uint8 => num.to_u8().map(|num| context::Imm::Uint8(num)),
                    context::Type::Uint16 => num.to_u16().map(|num| context::Imm::Uint16(num)),
                    context::Type::Uint32 => num.to_u32().map(|num| context::Imm::Uint32(num)),
                    context::Type::Uint64 => num.to_u64().map(|num| context::Imm::Uint64(num)),
                    context::Type::Uint128 => num.to_u128().map(|num| context::Imm::Uint128(num)),
                    context::Type::Float32 => num.to_f32().map(|num| context::Imm::Float32(num)),
                    context::Type::Float64 => num.to_f64().map(|num| context::Imm::Float64(num)),
                    context::Type::Const(lhs) => Some(self.transform_varint(lhs, rhs, line_info, type_name)?),
                    _ => panic!("invalid type for varint conversion"),
                };
                if let Some(num) = opt {
                    Ok(num)
                } else {
                    Err(self.make_err(
                        format!(
                            "'{}' cannot hold this value: '{}'",
                            type_name.unwrap_or(&lhs.to_string()),
                            num,
                        ),
                        line_info,
                    ))
                }
            }
            _ => panic!("not a valid conversion"),
        }
    }

    fn transform_varint_to_usize(
        &self,
        value: &context::Imm<'a>,
        line_info: &impl HasLineInfo,
    ) -> CompileResult<context::Imm<'a>> {
        self.transform_varint(&self.type_usize, value, line_info, Some("usize"))
    }

    fn transform_varint_to_int(
        &self,
        value: &context::Imm<'a>,
        line_info: &impl HasLineInfo,
    ) -> CompileResult<context::Imm<'a>> {
        self.transform_varint(&self.type_int, value, line_info, Some("int"))
    }

    fn usize2usize(&self, val: usize, line_info: &impl HasLineInfo) -> CompileResult<Context<'a>> {
        let opt = match self.type_usize {
            context::Type::Uint8 => val.to_u8().map(|val| context::Value::Imm(context::Imm::Uint8(val))),
            context::Type::Uint16 => val.to_u16().map(|val| context::Value::Imm(context::Imm::Uint16(val))),
            context::Type::Uint32 => val.to_u32().map(|val| context::Value::Imm(context::Imm::Uint32(val))),
            context::Type::Uint64 => val.to_u64().map(|val| context::Value::Imm(context::Imm::Uint64(val))),
            context::Type::Uint128 => val.to_u128().map(|val| context::Value::Imm(context::Imm::Uint128(val))),
            _ => panic!("invalid type for Analyzer::type_usize"),
        };
        let value = if let Some(num) = opt {
            num
        } else {
            return Err(self.make_err(format!("'usize' cannot hold this value: '{}'", val), line_info));
        };
        Ok(Context {
            is_lvalue: false,
            taipe: self.type_usize.clone(),
            value: value,
        })
    }

    fn make_did_you_mean_help(&self, name: &str, searched_names: &HashSet<String>) -> CompileError {
        let maybe = fuzzy_search_best(name, &searched_names, None);
        if maybe.len() == 1 {
            self.make_help(format!("did you mean '{}'?", maybe.iter().next().unwrap()))
        } else if maybe.len() != 0 {
            let mut maybe_str = String::new();
            for name in maybe {
                maybe_str.push('\'');
                maybe_str.push_str(&name);
                maybe_str.push_str("', ");
            }
            maybe_str.pop();
            maybe_str.pop();
            self.make_help(format!("did you mean one of {}?", maybe_str))
        } else {
            CompileError::Errors(Vec::new())
        }
    }

    fn make_note_with_path(
        &self,
        msg: impl ToString,
        file_path: impl ToString,
        obj: &impl HasLineInfo,
    ) -> CompileError {
        CompileError::SemNote {
            file_path: file_path.to_string(),
            line_info: obj.get_line_info(),
            msg: msg.to_string(),
        }
    }

    fn make_note(&self, msg: impl ToString, obj: &impl HasLineInfo) -> CompileError {
        self.make_note_with_path(msg, self.get_cur_scope().get_src_path(), obj)
    }

    fn make_err(&self, msg: impl ToString, obj: &impl HasLineInfo) -> CompileError {
        CompileError::SemError {
            file_path: self.get_cur_scope().get_src_path(),
            line_info: obj.get_line_info(),
            msg: msg.to_string(),
        }
    }

    fn make_warning(&self, msg: impl ToString, obj: &impl HasLineInfo) -> CompileError {
        CompileError::SemWarning {
            file_path: self.get_cur_scope().get_src_path(),
            line_info: obj.get_line_info(),
            msg: msg.to_string(),
        }
    }

    fn make_help(&self, msg: impl ToString) -> CompileError {
        CompileError::SemHelp { msg: msg.to_string() }
    }

    fn get_cur_scope(&self) -> Ref<'_, scope::Scope<'a>> {
        self.cur_scope.borrow()
    }

    fn get_current_function(&self) -> Option<Rc<RefCell<scope::Scope<'a>>>> {
        if self.cur_scope.borrow().is_function() {
            Some(Rc::clone(&self.cur_scope))
        } else {
            self.cur_scope.borrow().get_enclosing_function()
        }
    }

    fn use_current_function_data<F, T>(&self, handler: F) -> T
    where
        F: FnOnce(&scope::Function) -> T,
    {
        let function = self.get_current_function().expect("not in a function");
        let scope::Payload::Function(ref data) = function.borrow().payload else {
            unreachable!("probably some analyzer bug");
        };
        handler(data)
    }

    fn mut_current_function_data<F, T>(&self, handler: F) -> T
    where
        F: FnOnce(&mut scope::Function) -> T,
    {
        let function = self.get_current_function().expect("not in a function");
        let scope::Payload::Function(ref mut data) = function.borrow_mut().payload else {
            unreachable!("probably some analyzer bug");
        };
        handler(data)
    }

    // fn get_current_block(&self) -> Option<Rc<RefCell<scope::Scope<'a>>>> {
    //     if self.cur_scope.borrow().is_block() {
    //         Some(Rc::clone(&self.cur_scope))
    //     } else {
    //         self.cur_scope.borrow().get_enclosing_block()
    //     }
    // }
}
