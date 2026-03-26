use std::{
    cell::{Ref, RefCell},
    collections::{HashMap, HashSet},
    rc::Rc,
    sync::atomic::AtomicU64,
};

use num_bigint::{BigInt, ToBigInt};
use num_traits::cast::ToPrimitive;

use crate::{
    ast,
    common::{
        CompileError, CompileResult, HasLineInfo, Int, Layout, LineInfo, Settings,
        fuzzy_search_best,
    },
    context::{self, Context},
    lexer::{Token, TokenKind, TokenValue},
    scope::{self, HasSrcInfo, Payload, State},
};

// TODO: Unique counter should not be global
// It should be a member of scope
static UNIQUE_COUNTER: AtomicU64 = AtomicU64::new(0);
static BLOCK_COUNTER: AtomicU64 = AtomicU64::new(0);

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
                        ast::Object::Module {
                            line_info: _,
                            decls,
                        } => {
                            for decl in decls {
                                final_decls.push(decl);
                            }
                            root.state =
                                State::Visited(Context::from_module(Rc::downgrade(root_rc)));
                        }
                        _ => unreachable!("not supposed to happen"),
                    },
                    _ => unreachable!("not supposed to happen"),
                },
                _ => unreachable!("not supposed to happen"),
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
            ast::Decl::Using {
                line_info: _,
                items: _,
            } => todo!("import statements are not yet supported"),
        };
        Ok(())
    }

    pub fn pre_declare_decls(&mut self, decls: &'a [ast::Decl]) -> CompileResult<()> {
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

    fn declare_sym(
        &mut self,
        node: &'a ast::Decl,
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
                "unnamed.{}$",
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
                "unnamed.{}$",
                UNIQUE_COUNTER.fetch_add(1, std::sync::atomic::Ordering::SeqCst)
            )
        } else {
            name.text.clone()
        };

        Ok(scope::Scope::add_child(
            &self.cur_scope,
            &sym_name,
            state,
            name,
        ))
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
                "unnamed.{}$",
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

    fn declare_field(
        &mut self,
        field: &'a ast::Field,
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
                "unnamed.{}$",
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

    pub fn visit_decl(
        &mut self,
        node: &'a ast::Decl,
        should_visit_children: bool,
    ) -> CompileResult<Context<'a>> {
        macro_rules! colon_compulsory {
            ($parser:expr, $token:expr) => {
                // Check the colon thing
                let Some(eq_token) = $token else {
                    unreachable!("probably some parser bug");
                };
                if eq_token.kind != TokenKind::Colon {
                    $parser
                        .saved_errs
                        .push($parser.make_err("expected ':'", eq_token));
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
                    let mut scope = scope.borrow_mut();
                    match &scope.state {
                        State::NotVisited(_) => {
                            scope.state = scope::State::VisitInProg;
                        }
                        State::VisitInProg => unreachable!("probably some analyzer bug"),
                        State::Visited(context) => {
                            if !context.taipe.is_module() {
                                return Ok(context.clone());
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
                    let ctx =
                        self.resolve_assign(Some((type_ctx, taipe.get_line_info())), None, None)?;
                    scope.borrow_mut().state = State::Visited(ctx.clone());
                    return Ok(ctx);
                };
                match object {
                    ast::Object::ExternModule {
                        line_info: _,
                        value,
                    } => {
                        colon_compulsory!(self, eq_token);
                        todo!("extern modules are not supported yet")
                    }
                    ast::Object::Module {
                        line_info: _,
                        decls,
                    } => {
                        colon_compulsory!(self, eq_token);
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
                            ctx.clone()
                        } else {
                            // Predeclare all declarations (only if not already visited)
                            self.pre_declare_decls(decls)?;
                            let ctx = Context::from_module(Rc::downgrade(&scope));
                            scope.borrow_mut().state = State::Visited(ctx.clone());
                            ctx
                        };
                        if should_visit_children {
                            // Visit every decl
                            for decl in decls {
                                self.visit_decl(decl, true)?;
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
                    ast::Object::Compound { line_info, field } => {
                        colon_compulsory!(self, eq_token);
                        // Visit type
                        if let Some(taipe) = taipe {
                            let taipe = self.visit_type(taipe)?;
                            let context::Type::Typedef = taipe else {
                                return Err(self.make_err("expected 'typedef'", node));
                            };
                        }
                        // TODO: implement field layout to distinguish between union and struct
                        let ctx = self.visit_compound(scope, field)?;
                        Ok(ctx)
                    }
                    ast::Object::Fun {
                        line_info,
                        params,
                        ret,
                        body,
                    } => {
                        colon_compulsory!(self, eq_token);
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
                        for param in params {
                            let taipe = self.visit_type(&param.taipe)?;
                            param_infos.push((&param.name, taipe));
                        }
                        let mut param_types = Vec::new();
                        for (name, taipe) in param_infos {
                            param_types.push(context::Param {
                                taipe: taipe.clone(),
                            });
                            let _ = self.declare_sym_ex(
                                scope::State::Visited(Context { taipe, value: None }),
                                name,
                            )?;
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
                            taipe: context::Type::Function {
                                ret: Box::new(ret_type),
                                params: param_types,
                            },
                            value: Some(context::Value::Function(Rc::downgrade(&scope))),
                        };
                        // Resolve assignment
                        let ctx =
                            self.resolve_assign(lhs, eq_token.as_ref(), Some((rhs, *line_info)))?;
                        // Mark it visited
                        scope.borrow_mut().state = scope::State::Visited(ctx.clone());
                        scope.borrow_mut().payload = scope::Payload::Function(scope::Function {
                            ret_line_info: ret.as_ref().map(|ret| ret.get_line_info()),
                        });
                        // TODO: visit stmts
                        if let Some(body) = body {
                            let ctx = self.visit_stmt(body)?;
                            dbg!(ctx.to_string());
                        }
                        //
                        // Restore old scope
                        self.cur_scope = old_cur_scope;
                        // --- FUNCTION CODE END
                        Ok(ctx)
                    }
                    ast::Object::Typedef(node) => {
                        colon_compulsory!(self, eq_token);
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
                        scope.borrow_mut().state = scope::State::Visited(ctx.clone());
                        Ok(ctx)
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
                        let ctx = self.resolve_assign(
                            lhs,
                            eq_token.as_ref(),
                            Some((rhs, expr.get_line_info())),
                        )?;
                        // Complete the visit
                        scope.borrow_mut().state = scope::State::Visited(ctx.clone());
                        Ok(ctx)
                    }
                }
            }
            ast::Decl::Using {
                line_info: _,
                items: _,
            } => {
                todo!("import statements are not supported yet")
            }
        }
    }

    fn visit_stmt(&mut self, node: &'a ast::Stmt) -> CompileResult<Context<'a>> {
        match node {
            ast::Stmt::If {
                line_info,
                expr,
                then_body,
                else_body,
            } => todo!(),
            ast::Stmt::While {
                line_info,
                label,
                expr,
                then_body,
                else_body,
            } => todo!(),
            ast::Stmt::Block {
                line_info,
                label,
                stmts,
            } => self.visit_block(*line_info, label.as_ref(), stmts),
            ast::Stmt::Yield { token, label, expr } => todo!(),
            ast::Stmt::Continue { token, label } => todo!(),
            ast::Stmt::Break { token, label, expr } => todo!(),
            ast::Stmt::Return { token, expr } => self.visit_return(token, expr.as_ref()),
            ast::Stmt::Decl(decl) => todo!(),
            ast::Stmt::Expr(expr) => {
                let _ = self.visit_expr(expr)?;
                Ok(Context::from_void())
            }
            ast::Stmt::Nop(_) => Ok(Context::from_void()),
        }
    }

    fn visit_return(
        &mut self,
        token: &Token,
        expr: Option<&'a ast::Expr>,
    ) -> CompileResult<Context<'a>> {
        let Some(function) = self.get_current_function() else {
            return Err(self.make_err("'return' is allowed in functions only", token));
        };
        let scope::State::Visited(ctx) = function.borrow().state.clone() else {
            unreachable!("probably some analyzer bug");
        };
        let scope::Payload::Function(scope::Function { ret_line_info }) = function.borrow().payload
        else {
            unreachable!("probably some analyzer bug");
        };
        let ret_line_info = ret_line_info.unwrap_or_else(|| function.borrow().get_line_info());
        let context::Type::Function { ret, params: _ } = ctx.taipe else {
            unreachable!("probably some analyzer bug");
        };
        let ret = *ret;
        if let Some(expr) = expr {
            if ret.is_void() {
                return Err(self
                    .make_err("invalid expression", expr)
                    .chain(self.make_note(
                        format!("function expects return type '{}'", ret.to_string()),
                        &ret_line_info,
                    )));
            }
            let rhs = self.visit_expr(expr)?;
            let _ = self.resolve_assign(
                Some((ret, ret_line_info)),
                None,
                Some((rhs, expr.get_line_info())),
            )?;
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

    fn visit_block(
        &mut self,
        line_info: LineInfo,
        label: Option<&Token>,
        stmts: &'a [ast::Stmt],
    ) -> CompileResult<Context<'a>> {
        let scope = self.create_block_scope(line_info);
        // Begin new scope
        let old_cur_scope = Rc::clone(&self.cur_scope);
        self.cur_scope = Rc::clone(&scope);
        // Saves the (last index + 1) of the last stmt visited
        let mut last_stmt_index = 0;
        // Visit individual statements
        for (i, stmt) in stmts.iter().enumerate() {
            let ctx = self.visit_stmt(stmt)?;
            last_stmt_index = i + 1;
            // if ctx.taipe.is_void() {
            //     continue;
            // }
            if ctx.taipe.is_noreturn() {
                break;
            }
        }
        if last_stmt_index < stmts.len() {
            // We have unreachable code
            return Err(self.make_err("unreachable code", &&stmts[last_stmt_index..]));
        }
        let ctx = Context::from_void();
        scope.borrow_mut().state = scope::State::Visited(ctx.clone());
        // Restore old scope
        self.cur_scope = old_cur_scope;
        Ok(ctx)
    }

    fn create_block_scope(&mut self, line_info: LineInfo) -> Rc<RefCell<scope::Scope<'a>>> {
        let block_name = format!(
            "block.{}$",
            BLOCK_COUNTER.fetch_add(1, std::sync::atomic::Ordering::SeqCst)
        );
        let scope = scope::Scope::add_child(
            &self.cur_scope,
            &block_name,
            scope::State::VisitInProg,
            &line_info,
        );
        scope.borrow_mut().payload = Payload::Block;
        scope
    }

    fn get_fields(&mut self, field: &'a ast::Field) -> CompileResult<scope::Field<'a>> {
        self.get_fields_ex(field, false)
    }

    fn get_fields_ex(
        &mut self,
        field: &'a ast::Field,
        is_alone: bool,
    ) -> CompileResult<scope::Field<'a>> {
        match field {
            ast::Field::Compound { token, fields } => {
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
                    // Resolve assignment
                    self.resolve_assign(
                        Some(lhs),
                        eq_token.as_ref(),
                        Some((rhs, expr.get_line_info())),
                    )?
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
                            format!(
                                "'{}' cannot be used as a type of a field",
                                ctx.taipe.to_string()
                            ),
                            taipe,
                        ));
                    }
                    _ => {}
                }
                // TODO: The value of the field should be evaluated at compile time
                // If no value is provided then default value should be evaluated
                //
                // if ctx.value.is_none() {
                //     return Err(self.make_err("value cannot be evaluated at compile time", decl));
                // }
                // Complete the visit
                scope.borrow_mut().state = scope::State::Visited(ctx.clone());
                Ok(scope::Field::Field {
                    file_path: scope.borrow().get_src_path(),
                    line_info: name.get_line_info(),
                    name: scope.borrow().name.clone(),
                    ctx,
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
            taipe: context::Type::Typedef,
            value: Some(context::Value::Type(context::Type::Basic(Rc::downgrade(
                &scope,
            )))),
        };
        scope.borrow_mut().state = State::Visited(ctx.clone());
        // Visit every field
        let field = self.get_fields(field)?;
        // TODO: calculate size
        // Set the payload
        scope.borrow_mut().payload = Payload::Compound(scope::Compound::new(field));
        // Eval the layout
        let layout = self.resolve_layout_scope(Rc::clone(&scope))?;
        // Print the layout
        {
            println!(
                "Memory layout of {}: {:?}",
                ctx.clone().value.unwrap().to_string(),
                layout
            );
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
        Ok(ctx)
    }

    fn visit_var(
        &mut self,
        name: &crate::lexer::Token,
        expr: &'a ast::Expr,
    ) -> CompileResult<Context<'a>> {
        match self.visit_expr(expr) {
            Ok(ctx) => {
                if ctx.taipe.is_module() {
                    Err(self.make_err("cannot assign a module to a variable", expr))
                } else {
                    Ok(ctx)
                }
            }
            Err(err) => {
                if let CompileError::SemCyclic {
                    file_path,
                    line_info,
                } = err
                {
                    Err(self
                        .make_err(
                            "inference is ambiguous, encountered cyclic references",
                            name,
                        )
                        .chain(self.make_note_with_path(
                            "another one declared here",
                            file_path,
                            &line_info,
                        )))
                } else {
                    Err(err)
                }
            }
        }
    }

    pub fn visit_type(&mut self, node: &'a ast::Type) -> CompileResult<context::Type<'a>> {
        match node {
            ast::Type::Path { items } => {
                let mut index = 0;
                let mut ctx = self.get_name(&items[index])?;
                index += 1;
                while index < items.len() {
                    let name = &items[index];
                    ctx = match ctx.taipe.remove_const() {
                        context::Type::Module => {
                            let Some(value) = ctx.value else {
                                unreachable!("probably some analyzer bug");
                            };
                            let context::Value::Module(module) = value else {
                                unreachable!("probably some analyzer bug");
                            };
                            let Some(module) = module.upgrade() else {
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
                    return Err(self.make_err(
                        format!("expression is not a type: '{}'", ctx.to_string()),
                        node,
                    ));
                }
                // Post checks
                let Some(taipe) = ctx.value else {
                    unreachable!("not supposed to happen");
                };
                let context::Value::Type(taipe) = taipe else {
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
                            return Err(self.make_err(
                                format!("'{}' cannot be a parameter type", taipe.to_string()),
                                param,
                            ));
                        }
                        context::Type::Typedef => {
                            // TODO: Think about this
                            // FIXME: This parameter has to be comptime
                            return Err(
                                self.make_err("'typedef' cannot be a parameter type", param)
                            );
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
            ast::Type::Pointer {
                token: _,
                taipe: node,
            } => {
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
                let length = self.visit_expr(expr)?;
                if !length.taipe.is_integer() {
                    return Err(self
                        .make_err("argument of index operator should be an integer type", expr)
                        .chain(
                            self.make_note(format!("but got '{}'", length.taipe.to_string()), expr),
                        ));
                }
                let Some(length) = length.value else {
                    return Err(self.make_err("value cannot be evaluated at compile time", expr));
                };
                let context::Value::VarInt(length) = length else {
                    unreachable!("probably some analyzer bug");
                };
                Ok(context::Type::Array {
                    count: self.varint2usize(length, expr.get_line_info())?,
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
                        return Err(self.make_err(
                            format!("fat pointer to '{}' is invalid", taipe.to_string()),
                            node,
                        ));
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
                            return Err(self.make_err(
                                format!("'{}' cannot be a tuple item", taipe.to_string()),
                                node,
                            ));
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

    fn validate_fun_ret_type(
        &mut self,
        taipe: &context::Type<'a>,
        line_info: &impl HasLineInfo,
    ) -> CompileResult<()> {
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

    pub fn visit_expr(&mut self, node: &'a ast::Expr) -> CompileResult<Context<'a>> {
        match node {
            ast::Expr::Assign { lhs, op, rhs } => todo!(),
            ast::Expr::Binary2 {
                left,
                op1,
                op2,
                right,
            } => todo!(),
            ast::Expr::Binary { left, op, right } => todo!(),
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
            ast::Expr::Member { expr, name } => {
                let ctx = self.visit_expr(expr)?;
                // Remember const
                let is_const = ctx.taipe.remove_pointer().is_const();
                // Turn `const *const T' => `T'
                match ctx.taipe.remove_const().remove_pointer().remove_const() {
                    context::Type::Basic(scope) => {
                        let Some(scope) = scope.upgrade() else {
                            unreachable!("probably some analyzer bug");
                        };
                        let mut ctx = self.get_member(&scope, &name)?;
                        if is_const && !ctx.taipe.is_const() {
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
                            return Err(self.make_err(
                                format!("expected {}", TokenKind::IntLit.get_repr()),
                                name,
                            ));
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
                                format!(
                                    "index out of bounds, tuple length: {}, index: '{}'",
                                    items.len(),
                                    index
                                ),
                                name,
                            ));
                        }
                        // comptime: array indexing
                        // TODO: check usize for target system
                        let index = self.varint2usize(index, name.get_line_info())?;
                        // Get the type and value respectively
                        let taipe = items[index].clone();
                        let value = if let Some(tuple) = ctx.value {
                            let context::Value::Tuple(tuple) = tuple else {
                                unreachable!("probably some analyzer bug");
                            };
                            Some(tuple[index].clone())
                        } else {
                            None
                        };
                        Ok(Context { taipe, value })
                    }
                    context::Type::Module => {
                        let Some(value) = ctx.value else {
                            unreachable!("probably some analyzer bug");
                        };
                        let context::Value::Module(module) = value else {
                            unreachable!("probably some analyzer bug");
                        };
                        let Some(module) = module.upgrade() else {
                            unreachable!("probably some analyzer bug");
                        };
                        self.get_member(&module, &name)
                    }
                    // TODO: implement this after struct functions
                    // context::Type::Typedef => todo!(),
                    _ => Err(self.make_err(
                        format!("cannot use '.' operator on '{}'", ctx.taipe.to_string()),
                        expr,
                    )),
                }
            }
            ast::Expr::Call {
                line_info: _,
                expr,
                args,
            } => todo!(),
            ast::Expr::Index {
                line_info: _,
                expr,
                items,
            } => {
                if items.len() != 1 {
                    // TODO: to be changed
                    return Err(
                        self.make_err("only 1 argument is allowed in index operator", items)
                    );
                }
                let ctx = self.visit_expr(expr)?;
                let index_node = &items[0];
                let index = self.visit_expr(index_node)?;
                if !index.taipe.is_integer() {
                    return Err(self
                        .make_err("argument of index operator should be an integer type", node)
                        .chain(self.make_note(
                            format!("but got '{}'", index.taipe.to_string()),
                            index_node,
                        )));
                }
                match ctx.taipe.remove_const() {
                    context::Type::Array { count, taipe } => {
                        let mut value: Option<context::Value<'a>> = None;
                        if let Some(index) = index.value {
                            let context::Value::VarInt(index) = index else {
                                unreachable!("probably some analyzer bug");
                            };
                            // comptime: bounds checking
                            if index.num < BigInt::ZERO || index.num >= count.to_bigint().unwrap() {
                                return Err(self.make_err(
                                    format!(
                                        "index out of bounds, array length: {}, index: '{}'",
                                        count, index
                                    ),
                                    index_node,
                                ));
                            }
                            // comptime: array indexing
                            // TODO: check usize for target system
                            let index = self.varint2usize(index, index_node.get_line_info())?;
                            if let Some(array) = ctx.value {
                                let context::Value::Array(array) = array else {
                                    unreachable!("probably some analyzer bug");
                                };
                                value = Some(array[index].clone());
                            }
                        }
                        Ok(Context {
                            taipe: *taipe,
                            value,
                        })
                    }
                    context::Type::Fat(taipe) => {
                        let mut value: Option<context::Value<'a>> = None;
                        if let Some(array) = ctx.value
                            && let Some(index) = index.value
                        {
                            let context::Value::Array(array) = array else {
                                unreachable!("probably some analyzer bug");
                            };
                            let context::Value::VarInt(index) = index else {
                                unreachable!("probably some analyzer bug");
                            };
                            // comptime: bounds checking
                            if index.num < BigInt::ZERO
                                || index.num >= array.len().to_bigint().unwrap()
                            {
                                return Err(self.make_err(
                                    format!(
                                        "index out of bounds, array length: {}, index: '{}'",
                                        array.len(),
                                        index
                                    ),
                                    index_node,
                                ));
                            }
                            // comptime: array indexing
                            // TODO: check usize for target system
                            let index = self.varint2usize(index, index_node.get_line_info())?;
                            value = Some(array[index].clone());
                        }
                        Ok(Context {
                            taipe: *taipe,
                            value,
                        })
                    }
                    _ => {
                        return Err(self.make_err(
                            format!(
                                "cannot use index operator on type '{}'",
                                ctx.taipe.to_string()
                            ),
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
                        taipe: context::Type::Const(Box::new(context::Type::VarInt)),
                        value: Some(context::Value::VarInt(tok_val.clone())),
                    })
                }
                // TODO: get value from token
                TokenKind::FloatLit => Ok(Context {
                    taipe: context::Type::Const(Box::new(context::Type::Float64)),
                    value: None,
                }),
                TokenKind::Ident => self.get_name(&token),
                _ => unreachable!("probably some parser bug"),
            },
            ast::Expr::Paren { line_info: _, expr } => self.visit_expr(expr),
            ast::Expr::Tuple {
                line_info: _,
                exprs,
            } => {
                let mut types = Vec::new();
                let mut values = Vec::new();
                for expr in exprs {
                    let ctx = self.visit_expr(expr)?;
                    types.push(ctx.taipe);
                    if let Some(value) = ctx.value {
                        values.push(value);
                    }
                }
                if types.len() == values.len() {
                    Ok(Context {
                        taipe: context::Type::Const(Box::new(context::Type::Tuple(types))),
                        value: Some(context::Value::Tuple(values)),
                    })
                } else {
                    Ok(Context {
                        taipe: context::Type::Const(Box::new(context::Type::Tuple(types))),
                        value: None,
                    })
                }
            }
            // TODO: implement this
            ast::Expr::ArrayLit {
                line_info: _,
                items,
            } => todo!(),
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
            //  * value: {integer} -> result: const int
            //  * value: iX        -> result: const iX
            //  * value: fX        -> result: const fX
            // note: value may be const or non-const
            TokenKind::Minus => match ctx.taipe.remove_const() {
                context::Type::VarInt => Ok(Context {
                    taipe: self.type_int.clone().add_const(),
                    value: if let Some(value) = ctx.value {
                        self.transform_varint_to_int(value, expr)?.negate()
                    } else {
                        None
                    },
                }),
                context::Type::Int8
                | context::Type::Int16
                | context::Type::Int32
                | context::Type::Int64
                | context::Type::Int128 => Ok(Context {
                    taipe: ctx.taipe.add_const(),
                    value: if let Some(value) = ctx.value {
                        value.negate()
                    } else {
                        None
                    },
                }),
                context::Type::Float32 | context::Type::Float64 => Ok(Context {
                    taipe: ctx.taipe,
                    value: if let Some(value) = ctx.value {
                        value.negate()
                    } else {
                        None
                    },
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
                        format!(
                            "cannot apply '-' operator on type '{}'",
                            ctx.taipe.to_string()
                        ),
                        expr,
                    ));
                }
            },
            // Unary bit flip operator
            //    result = ~(value)
            // Description:
            //    Flips all the bits of an signed or unsigned integer
            // value and result can be:
            //  * value: {integer} -> result: const int
            //  * value: iX        -> result: const iX
            //  * value: uX        -> result: const uX
            // note: value may be const or non-const
            TokenKind::Tilde => match ctx.taipe.remove_const() {
                context::Type::VarInt => Ok(Context {
                    taipe: self.type_int.clone().add_const(),
                    value: if let Some(value) = ctx.value {
                        self.transform_varint_to_int(value, expr)?.flip_bits()
                    } else {
                        None
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
                    taipe: ctx.taipe.add_const(),
                    value: if let Some(value) = ctx.value {
                        value.flip_bits()
                    } else {
                        None
                    },
                }),
                _ => {
                    return Err(self.make_err(
                        format!(
                            "cannot apply '~' operator on type '{}'",
                            ctx.taipe.to_string()
                        ),
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
                    taipe: *taipe,
                    value: None,
                }),
                _ => {
                    return Err(self.make_err(
                        format!("cannot dereference type '{}'", ctx.taipe.to_string()),
                        expr,
                    ));
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
                        format!(
                            "cannot take address of value of type '{}'",
                            ctx.taipe.to_string()
                        ),
                        expr,
                    ));
                }
                match ctx.taipe {
                    context::Type::VarInt => Ok(Context {
                        taipe: context::Type::Pointer(Box::new(context::Type::Const(Box::new(
                            self.type_int.clone(),
                        )))),
                        value: None,
                    }),
                    _ => Ok(Context {
                        taipe: context::Type::Pointer(Box::new(ctx.taipe)),
                        value: None,
                    }),
                }
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
                        context::Type::Module | context::Type::Void | context::Type::Noreturn => {
                            false
                        }
                        _ => true,
                    }
                }
                if !is_sizeof_permitted(&ctx.taipe) {
                    return Err(self.make_err(
                        format!(
                            "cannot take sizeof value of type '{}'",
                            ctx.taipe.to_string()
                        ),
                        expr,
                    ));
                }
                let taipe = match ctx.taipe {
                    context::Type::Typedef => {
                        let Some(value) = ctx.value else {
                            unreachable!("probably some analyzer bug");
                        };
                        let context::Value::Type(taipe) = value else {
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
                        context::Type::Module | context::Type::Void | context::Type::Noreturn => {
                            false
                        }
                        _ => true,
                    }
                }
                if !is_alignof_permitted(&ctx.taipe) {
                    return Err(self.make_err(
                        format!(
                            "cannot take alignof value of type '{}'",
                            ctx.taipe.to_string()
                        ),
                        expr,
                    ));
                }
                let taipe = match ctx.taipe {
                    context::Type::Typedef => {
                        let Some(value) = ctx.value else {
                            unreachable!("probably some analyzer bug");
                        };
                        let context::Value::Type(taipe) = value else {
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
                        format!(
                            "cannot use typeof operator on type '{}'",
                            ctx.taipe.to_string()
                        ),
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
            //  * value: bool      -> result: const bool
            //  * value: T         -> result: const bool
            //      T must be implicitly convertible to bool
            // note: value may be const or non-const
            TokenKind::Not => {
                let lhs = context::Type::Bool;
                let lhs_line_info = LineInfo::from_range(op, expr);
                let rhs = ctx;
                let rhs_line_info = expr.get_line_info();
                let mut ctx = self.resolve_assign(
                    Some((lhs, lhs_line_info)),
                    None,
                    Some((rhs, rhs_line_info)),
                )?;
                // Perform the operation at compile time
                ctx.value = ctx.value.map(|value| match value {
                    context::Value::Bool(b) => context::Value::Bool(!b),
                    _ => unreachable!("probably some analyzer bug"),
                });
                Ok(Context {
                    taipe: context::Type::Const(Box::new(context::Type::Bool)),
                    value: ctx.value,
                })
            }
            _ => unreachable!("probably some parser bug"),
        }
    }

    fn get_sizeof(
        &mut self,
        taipe: &context::Type<'a>,
        line_info: &impl HasLineInfo,
    ) -> CompileResult<usize> {
        Ok(self.resolve_layout(taipe, line_info)?.size)
    }

    fn get_alignof(
        &mut self,
        taipe: &context::Type<'a>,
        line_info: &impl HasLineInfo,
    ) -> CompileResult<usize> {
        Ok(self.resolve_layout(taipe, line_info)?.alignment)
    }

    fn resolve_layout(
        &mut self,
        taipe: &context::Type<'a>,
        line_info: &impl HasLineInfo,
    ) -> CompileResult<Layout> {
        // (usize, usize) -> (size, alignment)
        // size (in bytes) -> always a multiple of alignment
        // alignment (in bytes) -> always a power of 2
        self.resolve_layout_ex(taipe, line_info.get_line_info())
    }

    fn resolve_layout_ex(
        &mut self,
        taipe: &context::Type<'a>,
        line_info: LineInfo,
    ) -> CompileResult<Layout> {
        let layout = match taipe {
            context::Type::Bool => Layout {
                size: 1,
                alignment: 1,
            },
            context::Type::Char => Layout {
                size: 1,
                alignment: 1,
            },
            context::Type::Int8 | context::Type::Uint8 => Layout {
                size: 1,
                alignment: 1,
            },
            context::Type::Int16 | context::Type::Uint16 => Layout {
                size: 2,
                alignment: 2,
            },
            context::Type::Int32 | context::Type::Uint32 => Layout {
                size: 4,
                alignment: 4,
            },
            context::Type::Int64 | context::Type::Uint64 => Layout {
                size: 8,
                alignment: 8,
            },
            context::Type::Int128 | context::Type::Uint128 => Layout {
                size: 16,
                alignment: 16,
            },
            context::Type::Float32 => Layout {
                size: 4,
                alignment: 4,
            },
            context::Type::Float64 => Layout {
                size: 8,
                alignment: 8,
            },
            context::Type::Const(taipe) => self.resolve_layout_ex(taipe, line_info)?,
            context::Type::Basic(weak) => self.resolve_layout_scope(
                weak.upgrade().expect("i dont really know what to do here"),
            )?,
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
                // pointer_size + pointer_size
                // FIXME: fix this after generalizing fat pointers
                Layout {
                    size: 2 * self.settings.pointer_size,
                    alignment: 2 * self.settings.pointer_size,
                }
            }
            context::Type::Tuple(items) => todo!("layout of tuples is not implemented"),
            context::Type::VarInt
            | context::Type::Module
            | context::Type::Typedef
            | context::Type::Void
            | context::Type::Noreturn => {
                return Err(self.make_err(
                    format!(
                        "type has no memory layout, problem type is '{}'",
                        taipe.to_string()
                    ),
                    &line_info,
                ));
            }
        };
        Ok(layout)
    }

    fn resolve_layout_scope(
        &mut self,
        scope: Rc<RefCell<scope::Scope<'a>>>,
    ) -> CompileResult<Layout> {
        let payload = scope.borrow().payload.clone();
        scope.borrow_mut().payload = scope::Payload::LayoutResolutionInProg;
        match payload {
            Payload::Compound(compound) => {
                let mut offsets = HashMap::<String, scope::FieldData>::new();
                // Resolve layout info for the struct or union or field
                let layout = self.resolve_layout_field(&compound.field, 0, &mut offsets, &|name| {
                    // Give child line info when requested
                    scope.borrow().children[&name.to_string()]
                        .borrow()
                        .get_line_info()
                });
                let layout = match layout {
                    Ok(layout) => layout,
                    Err(err) => {
                        return if let CompileError::SemCyclic {
                            file_path,
                            line_info,
                        } = err
                        {
                            Err(self
                                .make_err(
                                    "memory layout is ambiguous, encountered cyclic references",
                                    &scope.borrow(),
                                )
                                .chain(self.make_note_with_path(
                                    "cycle occurs here",
                                    file_path,
                                    &line_info,
                                )))
                        } else {
                            Err(err)
                        };
                    }
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
            let padding = if misalignment > 0 {
                alignment - misalignment
            } else {
                0
            };
            padding
        }

        match field {
            scope::Field::Struct(fields) => {
                let mut struct_alignment = 1usize;
                let offset_start = cur_offset;
                for field in fields {
                    // Set the offset of field
                    let layout = self.resolve_layout_field(
                        field,
                        cur_offset,
                        offset_table,
                        get_line_info_of_field,
                    )?;
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
                // TODO: think about empty structs
                // Reference: https://doc.rust-lang.org/nomicon/exotic-sizes.html#zero-sized-types-zsts
                // Reference: https://doc.rust-lang.org/nomicon/vec/vec-zsts.html
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
                    let layout = self.resolve_layout_field(
                        field,
                        cur_offset,
                        offset_table,
                        get_line_info_of_field,
                    )?;
                    // Size of a union is the size of the largest field
                    union_size = union_size.max(layout.size);
                    // Alignment of a union is the alignment of the most aligned field
                    union_alignment = union_alignment.max(layout.alignment);
                }
                // TODO: think about empty unions
                // Reference: https://doc.rust-lang.org/nomicon/exotic-sizes.html#zero-sized-types-zsts
                // Reference: https://doc.rust-lang.org/nomicon/vec/vec-zsts.html
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
                ctx,
            } => {
                let layout = self.resolve_layout_ex(&ctx.taipe, get_line_info_of_field(name));
                let layout = match layout {
                    Ok(layout) => layout,
                    Err(err) => {
                        return if let CompileError::SemCyclic {
                            file_path: _,
                            line_info: _,
                        } = err
                        {
                            Err(CompileError::SemCyclic {
                                file_path: file_path.clone(),
                                line_info: *line_info,
                            })
                        } else {
                            Err(err)
                        };
                    }
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
        // Fix {integer} problem, need to convert to int
        if let Some((
            Context {
                ref mut taipe,
                value: Some(ref mut value),
            },
            rhs_line_info,
        )) = rhs
        {
            *taipe = self.type_int.clone();
            *value = self.transform_varint_to_int(value.clone(), &rhs_line_info)?;
        }
        match (lhs, rhs) {
            (None, None) => panic!("either type or value information should be present"),
            // Situation
            // ---------------------------------
            // name :: value;
            // name := value;
            // ---------------------------------
            (None, Some((rhs, rhs_line_info))) => {
                let Some(eq_token) = eq_token else {
                    unreachable!("probably some analyzer bug");
                };
                match eq_token.kind {
                    // Situation
                    // ---------------------------------
                    // name :: value;
                    // ---------------------------------
                    TokenKind::Colon => {
                        if rhs.value.is_none() {
                            return Err(self.make_err(
                                "value cannot be evaluated at compile time",
                                &rhs_line_info,
                            ));
                        }
                        Ok(Context {
                            taipe: rhs.taipe.add_const(),
                            value: rhs.value,
                        })
                    }
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
                    taipe: lhs,
                    value: None,
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
                            if rhs.value.is_none() {
                                return Err(self.make_err(
                                    "value cannot be evaluated at compile time",
                                    &rhs_line_info,
                                ));
                            }
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
                self.resolve_implicit_cast(
                    lhs,
                    lhs_line_info,
                    rhs,
                    rhs_line_info,
                    true,
                    allow_assign_to_const,
                )
            }
        }
    }

    fn resolve_implicit_cast(
        &mut self,
        mut lhs: context::Type<'a>,
        lhs_line_info: LineInfo,
        mut rhs: Context<'a>,
        rhs_line_info: LineInfo,
        allow_assign_from_const: bool,
        allow_assign_to_const: bool,
    ) -> CompileResult<Context<'a>> {
        macro_rules! return_err {
            () => {
                return Err(self
                    .make_err(
                        format!("cannot assign to: '{}'", lhs.to_string()),
                        &lhs_line_info,
                    )
                    .chain(self.make_note(
                        format!("type of value is '{}'", rhs.to_string()),
                        &rhs_line_info,
                    )));
            };
        }
        // if allow_assign_from_const {
        //     // const qualifier in rhs does not matter at all during assignment
        //     // as values are always copied (except for pointers of course)
        //     rhs.taipe = rhs.taipe.remove_const();
        // }
        // if allow_assign_to_const {
        //     // If this is a first assignment to a constant
        //     // Behave as if the constant has no const qualifier to its type
        //     lhs = lhs.remove_const();
        // }
        // Type checking and Implicit conversions
        match (&lhs, &rhs.taipe) {
            // Implicit signed integer conversions
            (context::Type::Int128, context::Type::Int64) => todo!(),
            (context::Type::Int128, context::Type::Int32) => todo!(),
            (context::Type::Int128, context::Type::Int16) => todo!(),
            (context::Type::Int128, context::Type::Int8) => todo!(),
            (context::Type::Int64, context::Type::Int32) => todo!(),
            (context::Type::Int64, context::Type::Int16) => todo!(),
            (context::Type::Int64, context::Type::Int8) => todo!(),
            (context::Type::Int32, context::Type::Int16) => todo!(),
            (context::Type::Int32, context::Type::Int8) => todo!(),
            (context::Type::Int16, context::Type::Int8) => todo!(),
            // Implicit unsigned integer conversions
            (context::Type::Uint128, context::Type::Uint64) => todo!(),
            (context::Type::Uint128, context::Type::Uint32) => todo!(),
            (context::Type::Uint128, context::Type::Uint16) => todo!(),
            (context::Type::Uint128, context::Type::Uint8) => todo!(),
            (context::Type::Uint64, context::Type::Uint32) => todo!(),
            (context::Type::Uint64, context::Type::Uint16) => todo!(),
            (context::Type::Uint64, context::Type::Uint8) => todo!(),
            (context::Type::Uint32, context::Type::Uint16) => todo!(),
            (context::Type::Uint32, context::Type::Uint8) => todo!(),
            (context::Type::Uint16, context::Type::Uint8) => todo!(),
            // (context::Type::Int, context::Type::Float32) => {
            //     if let Some(value) = &rhs.value {
            //         let context::Value::Float32(value) = value else {
            //             unreachable!("probably some analyzer bug");
            //         };
            //         rhs.value = Some(context::Value::Int(Int::from_f32(*value)));
            //     }
            //     // TODO: record info for generating IR
            // }
            // (context::Type::Int, context::Type::Float64) => {
            //     if let Some(value) = &rhs.value {
            //         let context::Value::Float64(value) = value else {
            //             unreachable!("probably some analyzer bug");
            //         };
            //         rhs.value = Some(context::Value::Int(Int::from_f64(*value)));
            //     }
            //     // TODO: record info for generating IR
            // }
            (context::Type::Float32, context::Type::VarInt) => {
                if let Some(value) = &rhs.value {
                    let context::Value::VarInt(value) = value else {
                        unreachable!("probably some analyzer bug");
                    };
                    let Some(value) = value.to_f32() else {
                        return Err(self.make_err(
                            format!("'f32' cannot hold this value: '{}'", value),
                            &rhs_line_info,
                        ));
                    };
                    rhs.value = Some(context::Value::Float32(value));
                }
                // TODO: record info for generating IR
            }
            (context::Type::Float64, context::Type::VarInt) => {
                if let Some(value) = &rhs.value {
                    let context::Value::VarInt(value) = value else {
                        unreachable!("probably some analyzer bug");
                    };
                    let Some(value) = value.to_f64() else {
                        return Err(self.make_err(
                            format!("'f64' cannot hold this value: '{}'", value),
                            &rhs_line_info,
                        ));
                    };
                    rhs.value = Some(context::Value::Float64(value));
                }
                // TODO: record info for generating IR
            }
            (context::Type::Float32, context::Type::Float64) => {
                if let Some(value) = &rhs.value {
                    let context::Value::Float64(value) = value else {
                        unreachable!("probably some analyzer bug");
                    };
                    rhs.value = Some(context::Value::Float32(*value as f32));
                }
                // TODO: record info for generating IR
            }
            (context::Type::Const(lhs_const), context::Type::Const(rhs_const)) => {
                if !allow_assign_to_const {
                    return Err(self.make_err(
                        format!("cannot assign to a constant of type: '{}'", lhs.to_string()),
                        &lhs_line_info,
                    ));
                }
                let lhs = (**lhs_const).clone();
                let rhs = Context {
                    taipe: (**rhs_const).clone(),
                    value: rhs.value.clone(),
                };
                if let Err(_) =
                    self.resolve_implicit_cast(lhs, lhs_line_info, rhs, rhs_line_info, false, true)
                {
                    return_err!();
                };
            }
            (context::Type::Const(lhs_const), _) => {
                if !allow_assign_to_const {
                    return Err(self.make_err(
                        format!("cannot assign to a constant of type: '{}'", lhs.to_string()),
                        &lhs_line_info,
                    ));
                }
                if let Err(_) = self.resolve_implicit_cast(
                    (**lhs_const).clone(),
                    lhs_line_info,
                    rhs.clone(),
                    rhs_line_info,
                    false,
                    false,
                ) {
                    return_err!();
                };
            }
            (lhs, context::Type::Const(rhs_const)) => {
                if !allow_assign_from_const {
                    return_err!();
                }
                let rhs = Context {
                    taipe: (**rhs_const).clone(),
                    value: rhs.value.clone(),
                };
                if let Err(_) = self.resolve_implicit_cast(
                    lhs.clone(),
                    lhs_line_info,
                    rhs,
                    rhs_line_info,
                    false,
                    allow_assign_to_const,
                ) {
                    return_err!();
                };
            }
            (context::Type::Pointer(lhs_ptr), context::Type::Pointer(rhs_ptr)) => {
                //       *T = *T       (Valid)
                // *const T = *T       (Valid)
                //       *T = *const T (Invalid)
                // *const T = *const T (Valid)
                assert!(rhs.value.is_none());
                let lhs = (**lhs_ptr).clone();
                let rhs = Context {
                    taipe: (**rhs_ptr).clone(),
                    value: rhs.value.clone(),
                };
                if let Err(_) =
                    self.resolve_implicit_cast(lhs, lhs_line_info, rhs, rhs_line_info, false, true)
                {
                    return_err!();
                };
            }
            (
                context::Type::Fat(lhs_type),
                context::Type::Array {
                    count: _,
                    taipe: rhs_type,
                },
            ) => {
                // array type can be coerced to a fat pointer
                // TODO: record length information (for generating IR)
                if lhs_type != rhs_type {
                    return_err!();
                }
            }
            (context::Type::Noreturn, _) => {
                return Err(self.make_err(
                    format!("cannot assign to: '{}'", lhs.to_string()),
                    &lhs_line_info,
                ));
            }
            (_, context::Type::Noreturn) => {
                // noreturn type can be coerced to any type
                rhs.value = None;
            }
            (lhs, rhs) => {
                if lhs != rhs {
                    return_err!();
                }
            }
        }
        if allow_assign_to_const {
            // Now add the constant qualifier to the type
            lhs = lhs.add_const();
        }
        Ok(Context {
            taipe: lhs,
            value: rhs.value,
        })
    }

    fn get_member(
        &mut self,
        scope: &Rc<RefCell<scope::Scope<'a>>>,
        name: &Token,
    ) -> CompileResult<Context<'a>> {
        let mut searched_names = HashSet::new();
        if let Some(ctx) = self.resolve_member(&scope, &name.text, &mut searched_names)? {
            Ok(ctx)
        } else {
            let maybe = fuzzy_search_best(&name.text, &searched_names, None);
            let mut err = self.make_err(
                format!(
                    "'{}' has no member named '{}'",
                    scope.borrow().sym_path.to_string(),
                    &name.text
                ),
                name,
            );
            if maybe.len() == 1 {
                err = err.chain(
                    self.make_help(format!("did you mean '{}'?", maybe.iter().next().unwrap())),
                );
            } else if maybe.len() != 0 {
                let mut maybe_str = String::new();
                for name in maybe {
                    maybe_str.push('\'');
                    maybe_str.push_str(&name);
                    maybe_str.push_str("', ");
                }
                maybe_str.pop();
                maybe_str.pop();
                err = err.chain(self.make_help(format!("did you mean one of {}?", maybe_str)));
            }
            Err(err)
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
                scope::State::Visited(ctx) => return Ok(Some(ctx.clone())),
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
        if let Some(mut ctx) = self.resolve_name(&name.text, &mut searched_names)? {
            if !ctx.taipe.is_const() {
                ctx.value = None;
            }
            Ok(ctx)
        } else {
            let maybe = fuzzy_search_best(&name.text, &searched_names, None);
            let mut err = self.make_err("undefined reference", name);
            if maybe.len() == 1 {
                err = err.chain(
                    self.make_help(format!("did you mean '{}'?", maybe.iter().next().unwrap())),
                );
            } else if maybe.len() != 0 {
                let mut maybe_str = String::new();
                for name in maybe {
                    maybe_str.push('\'');
                    maybe_str.push_str(&name);
                    maybe_str.push_str("', ");
                }
                maybe_str.pop();
                maybe_str.pop();
                err = err.chain(self.make_help(format!("did you mean one of {}?", maybe_str)));
            }
            Err(err)
        }
    }

    fn resolve_name(
        &mut self,
        name: &str,
        searched_names: &mut HashSet<String>,
    ) -> CompileResult<Option<Context<'a>>> {
        {
            // Check in the current scope and go upwards
            let mut scope = Rc::clone(&self.cur_scope);
            loop {
                if let Some(ctx) = self.resolve_member(&scope, name, searched_names)? {
                    return Ok(Some(ctx));
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

    fn transform_varint_to_usize(
        &self,
        value: context::Value<'a>,
        line_info: &impl HasLineInfo,
    ) -> CompileResult<context::Value<'a>> {
        match value {
            context::Value::VarInt(num) => {
                let num = num.num;
                let opt = match self.type_usize {
                    context::Type::Uint8 => num.to_u8().map(|num| context::Value::Uint8(num)),
                    context::Type::Uint16 => num.to_u16().map(|num| context::Value::Uint16(num)),
                    context::Type::Uint32 => num.to_u32().map(|num| context::Value::Uint32(num)),
                    context::Type::Uint64 => num.to_u64().map(|num| context::Value::Uint64(num)),
                    context::Type::Uint128 => num.to_u128().map(|num| context::Value::Uint128(num)),
                    _ => panic!("invalid type for Analyzer::type_usize"),
                };
                if let Some(num) = opt {
                    Ok(num)
                } else {
                    Err(self.make_err(
                        format!("'usize' cannot hold this value: '{}'", num),
                        line_info,
                    ))
                }
            }
            _ => Ok(value),
        }
    }

    fn transform_varint_to_int(
        &self,
        value: context::Value<'a>,
        line_info: &impl HasLineInfo,
    ) -> CompileResult<context::Value<'a>> {
        match value {
            context::Value::VarInt(num) => {
                let num = num.num;
                let opt = match self.type_int {
                    context::Type::Int8 => num.to_i8().map(|num| context::Value::Int8(num)),
                    context::Type::Int16 => num.to_i16().map(|num| context::Value::Int16(num)),
                    context::Type::Int32 => num.to_i32().map(|num| context::Value::Int32(num)),
                    context::Type::Int64 => num.to_i64().map(|num| context::Value::Int64(num)),
                    context::Type::Int128 => num.to_i128().map(|num| context::Value::Int128(num)),
                    _ => panic!("invalid type for Analyzer::type_int"),
                };
                if let Some(num) = opt {
                    Ok(num)
                } else {
                    Err(self.make_err(
                        format!("'int' cannot hold this value: '{}'", num),
                        line_info,
                    ))
                }
            }
            _ => Ok(value),
        }
    }

    fn usize2usize(&self, val: usize, line_info: &impl HasLineInfo) -> CompileResult<Context<'a>> {
        let opt = match self.type_usize {
            context::Type::Uint8 => val.to_u8().map(|val| context::Value::Uint8(val)),
            context::Type::Uint16 => val.to_u16().map(|val| context::Value::Uint16(val)),
            context::Type::Uint32 => val.to_u32().map(|val| context::Value::Uint32(val)),
            context::Type::Uint64 => val.to_u64().map(|val| context::Value::Uint64(val)),
            context::Type::Uint128 => val.to_u128().map(|val| context::Value::Uint128(val)),
            _ => panic!("invalid type for Analyzer::type_usize"),
        };
        let value = if let Some(num) = opt {
            num
        } else {
            return Err(self.make_err(
                format!("'usize' cannot hold this value: '{}'", val),
                line_info,
            ));
        };
        Ok(Context {
            taipe: self.type_usize.clone(),
            value: Some(value),
        })
    }

    fn varint2usize(&self, num: Int, line_info: LineInfo) -> CompileResult<usize> {
        if let Some(num) = num.to_usize() {
            Ok(num)
        } else {
            Err(self.make_err(
                format!("'usize' cannot hold this value: '{}'", num),
                &line_info,
            ))
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
        CompileError::SemHelp {
            msg: msg.to_string(),
        }
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

    fn get_current_block(&self) -> Option<Rc<RefCell<scope::Scope<'a>>>> {
        if self.cur_scope.borrow().is_block() {
            Some(Rc::clone(&self.cur_scope))
        } else {
            self.cur_scope.borrow().get_enclosing_block()
        }
    }
}
