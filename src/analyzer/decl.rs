use std::{cell::RefCell, rc::Rc};

use indexmap::IndexMap;
use log::{debug, info};

use crate::{
    ast,
    cfg::{ControlInfo, ControlNode},
    common::{CompileError, CompileResult, HasLineInfo},
    context::{self, Context},
    lexer::{Token, TokenKind},
    scope::{self, HasSrcInfo, Payload, State},
};

use super::Analyzer;

impl<'a> Analyzer<'a> {
    pub(crate) fn pre_declare_decl(&mut self, decl: &'a ast::Decl) -> CompileResult<()> {
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
            ast::Decl::DeclWithDirective {
                name,
                taipe: _,
                eq_token: _,
                directive: _,
            } => self.declare_sym(decl, &name)?,
            ast::Decl::Using { line_info: _, items: _ } => todo!("import statements are not yet supported"),
        };
        Ok(())
    }

    pub(crate) fn pre_declare_decls(&mut self, decls: &'a [ast::Decl]) -> CompileResult<()> {
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
                self.cur_scope
                    .borrow()
                    .unique_counter
                    .fetch_add(1, std::sync::atomic::Ordering::SeqCst)
            )
        } else {
            name.text.clone()
        };

        Ok(scope::Scope::add_child(
            &self.cur_scope,
            scope::ScopeKind::None,
            &sym_name,
            scope::State::NotVisited(scope::ScopeNode::Decl(node)),
            name,
        ))
    }

    fn declare_param(&mut self, state: scope::State<'a>, name: &Token) -> CompileResult<Rc<RefCell<scope::Scope<'a>>>> {
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
                self.cur_scope
                    .borrow()
                    .unique_counter
                    .fetch_add(1, std::sync::atomic::Ordering::SeqCst)
            )
        } else {
            name.text.clone()
        };

        Ok(scope::Scope::add_child(
            &self.cur_scope,
            scope::ScopeKind::Param,
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
                "unnamed{}$",
                self.cur_scope
                    .borrow()
                    .unique_counter
                    .fetch_add(1, std::sync::atomic::Ordering::SeqCst)
            )
        } else {
            name.text.clone()
        };

        Ok(scope::Scope::add_child(
            &self.cur_scope,
            scope::ScopeKind::None,
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
                self.cur_scope
                    .borrow()
                    .unique_counter
                    .fetch_add(1, std::sync::atomic::Ordering::SeqCst)
            )
        } else {
            name.text.clone()
        };

        Ok(scope::Scope::add_child(
            &self.cur_scope,
            scope::ScopeKind::Field,
            &sym_name,
            scope::State::NotVisited(scope::ScopeNode::Field(field)),
            field,
        ))
    }

    pub(crate) fn visit_decl(
        &mut self,
        node: &'a ast::Decl,
        should_visit_children: bool,
    ) -> CompileResult<Context<'a>> {
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
            ast::Decl::DeclWithDirective {
                name,
                taipe,
                eq_token,
                directive,
            } => {
                fn is_directive_allowed<'a>(taipe: &context::Type<'a>) -> bool {
                    match taipe {
                        context::Type::Const(taipe) => is_directive_allowed(taipe),
                        context::Type::Module
                        | context::Type::Typedef
                        | context::Type::Void
                        | context::Type::Noreturn => false,
                        _ => true,
                    }
                }

                let scope = if self.get_current_block().is_some() {
                    self.declare_sym(node, &name)?
                } else {
                    if let Some(child) = self.get_cur_scope().children.get(&name.text) {
                        Rc::clone(child)
                    } else {
                        self.declare_sym(node, &name)?
                    }
                };
                // Set in progress
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
                drop(scope_ref);
                // Visit type
                let lhs = self.visit_type(taipe)?;
                if !is_directive_allowed(&lhs) {
                    return Err(self.make_err(format!("invalid type: '{}'", lhs), taipe));
                }
                let cfg_assign;
                // Check directives
                let ctx = match directive.kind {
                    TokenKind::DirectiveZero => {
                        cfg_assign = true;
                        self.get_zero_value(&lhs, taipe)?
                    }
                    TokenKind::DirectiveUninit => {
                        cfg_assign = false;
                        Context {
                            is_lvalue: false,
                            taipe: lhs,
                            value: context::Value::from_nil(),
                        }
                    }
                    TokenKind::DirectiveGhost => {
                        cfg_assign = true;
                        Context {
                            is_lvalue: false,
                            taipe: lhs,
                            value: context::Value::from_nil(),
                        }
                    }
                    TokenKind::DirectiveDefault => {
                        // TODO: Get default init value
                        cfg_assign = true;
                        Context {
                            is_lvalue: false,
                            taipe: lhs,
                            value: context::Value::from_nil(),
                        }
                    }
                    _ => unreachable!("probably some parser bug"),
                };
                // Complete the visit
                if ctx.taipe.is_typedef() {
                    scope.borrow_mut().kind = scope::ScopeKind::Typedef;
                } else if ctx.taipe.is_const() {
                    scope.borrow_mut().kind = scope::ScopeKind::Const;
                } else {
                    scope.borrow_mut().kind = scope::ScopeKind::Variable;
                }

                if self.get_current_block().is_some() {
                    // cfg: insert variable declared node
                    self.mut_current_block_data(|data| {
                        let cf_declare = data.cfg.insert_vertex(ControlNode::Info(ControlInfo::VarDeclared {
                            scope: Rc::clone(&scope),
                        }));
                        data.cfg.insert_edge(data.cf_last, cf_declare);
                        data.cf_last = cf_declare;
                    });
                    // cfg: insert variable assigned node
                    if cfg_assign {
                        self.mut_current_block_data(|data| {
                            let cf_assign = data.cfg.insert_vertex(ControlNode::Info(ControlInfo::VarAssigned {
                                line_info: node.get_line_info(),
                                scope: Rc::clone(&scope),
                            }));
                            data.cfg.insert_edge(data.cf_last, cf_assign);
                            data.cf_last = cf_assign;
                        });
                    }
                }

                let result = Context::from_scope(&ctx.taipe, &scope);
                scope.borrow_mut().state = scope::State::Visited(ctx);
                Ok(result)
            }
            ast::Decl::Decl {
                name,
                taipe,
                eq_token,
                object,
            } => {
                let scope = if self.get_current_block().is_some() {
                    if let Some(object) = object {
                        self.declare_sym_with_value(node, &name, object)?
                    } else {
                        self.declare_sym(node, &name)?
                    }
                } else {
                    if let Some(child) = self.get_cur_scope().children.get(&name.text) {
                        Rc::clone(child)
                    } else {
                        if let Some(object) = object {
                            self.declare_sym_with_value(node, &name, object)?
                        } else {
                            self.declare_sym(node, &name)?
                        }
                    }
                };
                // Set in progress
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
                drop(scope_ref);
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
                    scope.borrow_mut().kind = if ctx.taipe.is_typedef() {
                        scope::ScopeKind::Typedef
                    } else if ctx.taipe.is_const() {
                        scope::ScopeKind::Const
                    } else {
                        scope::ScopeKind::Variable
                    };

                    // cfg: insert variable declared node
                    //      only if it is a local variable or constant
                    let should_insert_cfg = match scope.borrow().kind {
                        scope::ScopeKind::Variable => true,
                        scope::ScopeKind::Const => true,
                        _ => false,
                    };
                    if should_insert_cfg && self.get_current_block().is_some() {
                        self.mut_current_block_data(|data| {
                            let cf_declare = data.cfg.insert_vertex(ControlNode::Info(ControlInfo::VarDeclared {
                                scope: Rc::clone(&scope),
                            }));
                            data.cfg.insert_edge(data.cf_last, cf_declare);
                            data.cf_last = cf_declare;
                        });
                    }

                    scope.borrow_mut().state = State::Visited(ctx);
                    return Ok(result);
                };
                match object {
                    ast::Object::ExternModule { line_info: _, value } => {
                        colon_compulsory!(eq_token);
                        scope.borrow_mut().kind = scope::ScopeKind::Module;
                        todo!("extern modules are not supported yet")
                    }
                    ast::Object::Module { line_info: _, decls } => {
                        colon_compulsory!(eq_token);
                        scope.borrow_mut().kind = scope::ScopeKind::Module;
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
                        scope.borrow_mut().kind = scope::ScopeKind::Compound;
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
                        scope.borrow_mut().kind = scope::ScopeKind::Function;
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
                            let param_scope = self.declare_param(scope::State::VisitInProg, name)?;
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
                                            context::Type::Void,
                                            context::Type::Noreturn,
                                            ctx.taipe
                                        ),
                                        body,
                                    ));
                                }
                            } else if ret_type.is_noreturn() && !ctx.taipe.is_noreturn() {
                                return Err(self.make_err(
                                    format!(
                                        "invalid function returns value: '{}' function can never return",
                                        context::Type::Noreturn,
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
                        scope.borrow_mut().kind = scope::ScopeKind::Typedef;
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
                        let mut rhs = self.visit_expr(expr)?;
                        // Resolve assignment
                        if rhs.taipe.is_module() {
                            return Err(self.make_err("cannot assign a module to a variable", expr));
                        }
                        // If this is a global constant or variable then trivially evaluate the
                        // expression.
                        if self.get_cur_scope().get_enclosing_function().is_none() {
                            rhs = self.compeval_trivial(rhs, expr)?;
                        }
                        let ctx = self.resolve_assign(lhs, eq_token.as_ref(), Some((rhs, expr.get_line_info())))?;
                        let result = Context::from_scope(&ctx.taipe, &scope);
                        // Complete the visit
                        if ctx.taipe.is_typedef() {
                            scope.borrow_mut().kind = scope::ScopeKind::Typedef;
                        } else if ctx.taipe.is_const() {
                            scope.borrow_mut().kind = scope::ScopeKind::Const;
                        } else {
                            scope.borrow_mut().kind = scope::ScopeKind::Variable;
                        }

                        // cfg: insert variable declared node
                        //      only if it is a local variable or constant
                        let should_insert_cfg = match scope.borrow().kind {
                            scope::ScopeKind::Variable => true,
                            scope::ScopeKind::Const => true,
                            _ => false,
                        };
                        if should_insert_cfg && self.get_current_block().is_some() {
                            self.mut_current_block_data(|data| {
                                let cf_declare = data.cfg.insert_vertex(ControlNode::Info(ControlInfo::VarDeclared {
                                    scope: Rc::clone(&scope),
                                }));
                                let cf_assign = data.cfg.insert_vertex(ControlNode::Info(ControlInfo::VarAssigned {
                                    line_info: node.get_line_info(),
                                    scope: Rc::clone(&scope),
                                }));
                                data.cfg.insert_edge(data.cf_last, cf_declare);
                                data.cfg.insert_edge(cf_declare, cf_assign);
                                data.cf_last = cf_assign;
                            });
                        }

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

    fn get_fields(&mut self, field: &'a ast::Field) -> CompileResult<scope::Field<'a>> {
        self.get_fields_impl(field, false)
    }

    fn get_fields_impl(&mut self, field: &'a ast::Field, is_alone: bool) -> CompileResult<scope::Field<'a>> {
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
                    vec.push(self.get_fields_impl(field, is_child_alone)?);
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
                    let rhs = match self.visit_expr(expr) {
                        Ok(ctx) => ctx,
                        Err(CompileError::SemCyclic { file_path, line_info }) => {
                            return Err(self
                                .make_err("inference is ambiguous, encountered cyclic references", name)
                                .chain(self.make_note_with_path("another one declared here", file_path, &line_info)));
                        }
                        Err(err) => return Err(err),
                    };
                    let rhs = self.compeval_trivial(rhs, expr)?;
                    // Resolve assignment
                    self.resolve_assign(Some(lhs), eq_token.as_ref(), Some((rhs, expr.get_line_info())))?
                } else {
                    // Situation
                    // ---------------------------------
                    // name : type;
                    // ---------------------------------
                    assert!(eq_token.is_none());
                    // TODO: If no value is provided then default value should be evaluated
                    let rhs = (self.get_zero_value(&lhs.0, taipe)?, name.get_line_info());
                    self.resolve_assign(Some(lhs), None, Some(rhs))?
                };
                // Check the type of the fields
                match ctx.taipe {
                    context::Type::Const(_)
                    | context::Type::Module
                    | context::Type::Typedef
                    | context::Type::Noreturn => {
                        return Err(self.make_err(
                            format!("'{}' cannot be used as a type of a field", ctx.taipe),
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
            debug!("Memory layout of {}: {:?}", scope.borrow().sym_path, layout);
            let scope::Payload::Compound(ref compound) = scope.borrow().payload else {
                unreachable!("not supposed to happen")
            };
            let mut fields = compound.offsets.iter().collect::<Vec<_>>();
            fields.sort_by_key(|&(_, &data)| data.offset);
            for (name, field_data) in fields {
                debug!("  field '{}' = {:?}", name, field_data);
            }
            debug!("");
        }
        // Restore old scope
        self.cur_scope = old_cur_scope;
        Ok(result)
    }
}
