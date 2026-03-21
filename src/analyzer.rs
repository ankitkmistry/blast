use std::{
    cell::{Ref, RefCell},
    collections::HashMap,
    rc::Rc,
};

use num_bigint::{BigInt, ToBigInt};

use crate::{
    ast,
    common::{CompileError, CompileResult, HasLineInfo, Int, LineInfo},
    context::{self, Context},
    lexer::{Token, TokenKind, TokenValue},
    scope::{self, HasSrcInfo, Payload, State},
};

pub struct Analyzer<'a> {
    roots: HashMap<String, Rc<RefCell<scope::Scope<'a>>>>,
    cur_scope: Rc<RefCell<scope::Scope<'a>>>,
    saved_errs: Vec<CompileError>,
    warnings: Vec<CompileError>,
}

impl<'a> Analyzer<'a> {
    pub fn new(file_path: &str, name: &str, root: &'a ast::Object) -> Self {
        let scope = scope::Scope::new_root(file_path, root);
        let mut roots = HashMap::new();
        roots.insert(name.to_owned(), Rc::clone(&scope));
        Self {
            roots,
            cur_scope: scope,
            saved_errs: Vec::new(),
            warnings: Vec::new(),
        }
    }

    pub fn analyze(mut self) -> CompileResult<HashMap<String, Rc<RefCell<scope::Scope<'a>>>>> {
        let result = self.sem_analysis();
        if let Err(err) = result {
            // If there are any accumulated errors return them
            Err(err.chain(CompileError::Errors(self.saved_errs.clone())))
        } else {
            Ok(self.roots)
        }
    }

    fn sem_analysis(&mut self) -> CompileResult<()> {
        let Some(decls) = self.cur_scope.borrow().node.unwrap().get_decls().take() else {
            // TODO: handle the else situation here
            return Ok(());
        };
        self.pre_declare_decls(decls)?;
        for decl in decls {
            self.visit_decl(decl, true)?;
        }
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
            let result = match decl {
                ast::Decl::Decl {
                    name,
                    taipe: _,
                    eq_token: _,
                    object,
                } => self.declare_sym(decl, &name, object.as_ref()),
                ast::Decl::Using {
                    line_info: _,
                    items: _,
                } => todo!("import statements are not yet supported"),
            };
            if let Err(err) = result {
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
        object: Option<&'a ast::Object>,
    ) -> CompileResult<Rc<RefCell<scope::Scope<'a>>>> {
        // Check for redeclaration
        // Except for '_' declarations
        if name.kind != TokenKind::Underscore
            && let Some(prev_scope_ref) = self.get_cur_scope().children.get(&name.text)
        {
            let prev_scope = prev_scope_ref.borrow();
            if let Some(object) = object
                && object.is_module()
            {
                // Allow merging module declarations
                if let scope::State::Visited(prev_ctx) = &prev_scope.state {
                    if prev_ctx.taipe.is_module() {
                        return Ok(Rc::clone(prev_scope_ref));
                    }
                }
                if let scope::State::NotVisited(prev_decl) = prev_scope.state
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

        Ok(scope::Scope::add_child(
            &self.cur_scope,
            &name.text,
            Some(name.clone()),
            scope::State::NotVisited(node),
            object,
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
                    self.declare_sym(node, name, object.as_ref())?
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
                    ast::Object::Struct {
                        line_info: _,
                        decls,
                    } => {
                        // TODO: type punning syntax
                        // A :: struct {
                        //     foo: i32;
                        // }
                        // B :: struct {
                        //     using A;
                        //     bar: i32;
                        // }
                        colon_compulsory!(self, eq_token);
                        self.visit_compound(scope, object, decls)
                    }
                    ast::Object::Union {
                        line_info: _,
                        decls,
                    } => {
                        colon_compulsory!(self, eq_token);
                        // TODO: implement field layout to distinguish between union and struct
                        self.visit_compound(scope, object, decls)
                    }
                    ast::Object::Fun {
                        line_info: _,
                        params,
                        ret,
                        body,
                    } => {
                        colon_compulsory!(self, eq_token);
                        todo!("functions are not supported yet")
                    }
                    ast::Object::Typedef(node) => {
                        colon_compulsory!(self, eq_token);
                        // Visit type
                        let lhs = if let Some(taipe) = taipe {
                            Some((self.visit_type(taipe)?, taipe.get_line_info()))
                        } else {
                            None
                        };
                        let rhs = self.visit_type(node)?;
                        if let context::Type::Typedef = rhs {
                            // context: type -> typedef, value -> typedef
                            // this cannot happen, there is no type of a type
                            // parser prevents this
                            return Err(self.make_err("invalid type alias", node));
                        }
                        // Resolve assignment
                        let ctx = self.resolve_assign(
                            lhs,
                            eq_token.as_ref(),
                            Some((Context::from_type(rhs), node.get_line_info())),
                        )?;
                        // Complete the visit
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

    fn visit_compound(
        &mut self,
        scope: Rc<RefCell<scope::Scope<'a>>>,
        object: &'a ast::Object,
        decls: &'a Vec<ast::Decl>,
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
        let mut fields = Vec::new();
        for decl in decls {
            let ctx = self.visit_decl(decl, true)?;
            // Check the type of the fields
            match ctx.taipe.remove_const() {
                context::Type::Function { ret: _, params: _ } => {
                    return Err(self.make_err("function cannot be used as a field", decl));
                }
                context::Type::Module | context::Type::Typedef | context::Type::Noreturn => {
                    return Err(self.make_err(
                        format!("'{}' cannot be used as a field", ctx.taipe.to_string()),
                        decl,
                    ));
                }
                _ => {}
            }
            // Retrieve the name
            let name = match decl {
                ast::Decl::Decl {
                    name,
                    taipe: _,
                    eq_token: _,
                    object: _,
                } => name.text.clone(),
                ast::Decl::Using {
                    line_info: _,
                    items: _,
                } => unreachable!(),
            };
            fields.push((name, ctx));
        }
        // TODO: improve payload
        // provide advanced field layout information
        scope.borrow_mut().payload = Payload::Compound(scope::Compound::new(&fields, object));
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
                            "type inference is ambiguous, encountered cyclic references",
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
        let ctx = match node {
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
                ctx
            }
            ast::Type::Function {
                line_info: _,
                params,
                ret,
            } => {
                let mut ctx_params = Vec::new();
                for param in params {
                    let taipe = self.visit_type(&param.taipe)?;
                    match &taipe {
                        context::Type::Module => {
                            return Err(
                                self.make_err("'module' cannot be a parameter type", &param.taipe)
                            );
                        }
                        context::Type::Typedef => {
                            // TODO: Think about this
                            return Err(
                                self.make_err("'typedef' cannot be a parameter type", &param.taipe)
                            );
                        }
                        _ => {}
                    }
                    ctx_params.push(context::Param {
                        name: param.name.clone().map(|tok| tok.text),
                        taipe,
                        node: param,
                    });
                }
                let ctx_ret = self.visit_type(ret)?;
                match &ctx_ret {
                    context::Type::Module => {
                        return Err(self.make_err("'module' cannot be a return type", ret));
                    }
                    context::Type::Typedef => {
                        return Err(self.make_err("'typedef' cannot be a return type", ret));
                    }
                    _ => {}
                }
                Context::from_type(context::Type::Function {
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
                            self.warnings.push(self.make_err(
                                format!(
                                    "'const' is redundant here, '{}' is always a constant",
                                    taipe.to_string()
                                ),
                                token,
                            ));
                            Context::from_type(taipe)
                        } else {
                            Context::from_type(context::Type::Const(Box::new(taipe)))
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
                    _ => Context::from_type(context::Type::Pointer(Box::new(taipe))),
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
                let context::Value::Int(length) = length else {
                    unreachable!("probably some analyzer bug");
                };
                Context::from_type(context::Type::Array {
                    count: self.bigint2usize(length, expr.get_line_info())?,
                    taipe: Box::new(taipe),
                })
            }
            ast::Type::Fat {
                line_info: _,
                taipe: node,
            } => {
                let taipe = self.visit_type(node)?;
                match &taipe {
                    context::Type::Module => {
                        return Err(self.make_err("fat pointer to 'module' is invalid", node));
                    }
                    context::Type::Typedef => {
                        return Err(self.make_err("fat pointer to 'typedef' is invalid", node));
                    }
                    _ => Context::from_type(context::Type::Fat(Box::new(taipe))),
                }
            }
            ast::Type::Paren {
                line_info: _,
                taipe: node,
            } => Context::from_type(self.visit_type(node)?),
            ast::Type::Tuple {
                line_info: _,
                types: nodes,
            } => {
                let mut vec = Vec::new();
                for node in nodes {
                    let taipe = self.visit_type(node)?;
                    match &taipe {
                        context::Type::Module => {
                            return Err(self.make_err("'module' cannot be a tuple item", node));
                        }
                        context::Type::Typedef => {
                            return Err(self.make_err("'typedef' cannot be a tuple item", node));
                        }
                        _ => vec.push(taipe),
                    }
                }
                Context::from_type(context::Type::Tuple(vec))
            }
            ast::Type::Literal(token) => match token.kind {
                TokenKind::Void => Context::from_type(context::Type::Tuple(Vec::new())),
                TokenKind::Noreturn => Context::from_noreturn(),
                TokenKind::Typedef => Context::from_type_literal(),
                _ => unreachable!("probably some parser bug"),
            },
        };
        // Post checks
        match &ctx.taipe {
            context::Type::Typedef => {}
            _ => {
                return Err(self.make_err(
                    format!("expression is not a type: '{}'", ctx.to_string()),
                    node,
                ));
            }
        }
        let Some(taipe) = ctx.value else {
            unreachable!("not supposed to happen");
        };
        let context::Value::Type(taipe) = taipe else {
            unreachable!("not supposed to happen");
        };
        Ok(taipe)
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
            ast::Expr::Unary { op, expr } => {
                let ctx = self.visit_expr(expr)?;
                match op.kind {
                    TokenKind::Minus => match ctx.taipe.remove_const() {
                        context::Type::Int => Ok(Context {
                            taipe: ctx.taipe,
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
                    TokenKind::Tilde => match ctx.taipe.remove_const() {
                        // TODO: comptime: implement this
                        // ~ operator is not possible on variable sized integers
                        context::Type::Int => Ok(Context {
                            taipe: ctx.taipe,
                            value: None,
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
                    TokenKind::Star => match ctx.taipe.remove_const() {
                        // TODO: comptime: what about implementing this in comptime
                        // There are many edge cases and memory safety violation
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
                    TokenKind::Ampersand => todo!(),
                    TokenKind::Sizeof => {
                        let taipe = match ctx.taipe {
                            context::Type::Typedef => {
                                let Some(taipe) = ctx.value else {
                                    unreachable!("probably some analyzer bug");
                                };
                                let context::Value::Type(taipe) = taipe else {
                                    unreachable!("probably some analyzer bug");
                                };
                                taipe
                            }
                            taipe => taipe,
                        };
                        let Some(size) = taipe.get_size() else {
                            return Err(self.make_err(
                                format!("type has no size: '{}'", taipe.to_string()),
                                node,
                            ));
                        };
                        // TODO: make this usize not variable int
                        Ok(Context::from_int(Int::from_arbitrary(size as u64)))
                    }
                    TokenKind::Typeof => todo!(),
                    TokenKind::Alignof => {
                        let taipe = match ctx.taipe {
                            context::Type::Typedef => {
                                let Some(taipe) = ctx.value else {
                                    unreachable!("probably some analyzer bug");
                                };
                                let context::Value::Type(taipe) = taipe else {
                                    unreachable!("probably some analyzer bug");
                                };
                                taipe
                            }
                            taipe => taipe,
                        };
                        let Some(size) = taipe.get_align() else {
                            return Err(self.make_err(
                                format!("type has no alignment: '{}'", taipe.to_string()),
                                node,
                            ));
                        };
                        // TODO: make this usize not variable int
                        Ok(Context::from_int(Int::from_arbitrary(size as u64)))
                    }
                    TokenKind::Not => todo!(),
                    _ => unreachable!("probably some parser bug"),
                }
            }
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
                                node,
                            ));
                        }
                        // comptime: array indexing
                        // TODO: check usize for target system and retrieve the index
                        // Also check the value is in hardware allowed range
                        let index = self.bigint2usize(index, name.get_line_info())?;
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
                        self.make_err("number of arguments to index operator should be 1", items)
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
                            let context::Value::Int(index) = index else {
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
                            // TODO: check usize for target system and retrieve the index
                            // Also check the value is in hardware allowed range
                            let index = self.bigint2usize(index, index_node.get_line_info())?;
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
                            let context::Value::Int(index) = index else {
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
                            // TODO: check usize for target system and retrieve the index
                            // Also check the value is in hardware allowed range
                            let index = self.bigint2usize(index, index_node.get_line_info())?;
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
                        unreachable!("probably some parser bug")
                    };
                    let TokenValue::String(str) = tok_val else {
                        unreachable!("probably some parser bug")
                    };
                    Ok(Context::from_str(str))
                }
                TokenKind::IntLit => {
                    let Some(tok_val) = token.value.as_ref() else {
                        unreachable!("probably some parser bug");
                    };
                    let TokenValue::Int(tok_val) = tok_val else {
                        unreachable!("probably some parser bug");
                    };
                    // TODO: check suffix
                    Ok(Context {
                        taipe: context::Type::Const(Box::new(context::Type::Int)),
                        value: Some(context::Value::Int(tok_val.clone())),
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

    /// In case of declaration, 'eq_token' is the token that separates lhs and rhs.
    /// In case of assignment, 'eq_token' should always be None
    fn resolve_assign(
        &mut self,
        lhs: Option<(context::Type<'a>, LineInfo)>,
        eq_token: Option<&Token>,
        rhs: Option<(Context<'a>, LineInfo)>,
    ) -> CompileResult<Context<'a>> {
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
            (Some((mut lhs, lhs_line_info)), Some((mut rhs, rhs_line_info))) => {
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
                // const qualifier in rhs does not matter at all during assignment
                // as values are always copied
                rhs.taipe = rhs.taipe.remove_const();
                if allow_assign_to_const {
                    // If this is a first assignment to a constant
                    // Behave as if the constant has no const qualifier to its type
                    lhs = lhs.remove_const();
                }
                // Type checking
                match (&lhs, &rhs.taipe) {
                    (context::Type::Bool, context::Type::Char) => {
                        // true  => __char != 0
                        // false => __char != 0
                        // TODO: record info for generating IR
                    }
                    (context::Type::Bool, context::Type::Int) => {
                        // true  => int != 0
                        // false => int != 0
                        // TODO: record info for generating IR
                    }
                    (context::Type::Bool, context::Type::Float32) => {
                        // true  => __f32 != 0
                        // false => __f32 != 0
                        // TODO: record info for generating IR
                    }
                    (context::Type::Bool, context::Type::Float64) => {
                        // true  => __f64 != 0
                        // false => __f64 != 0
                        // TODO: record info for generating IR
                    }
                    (context::Type::Const(_), _) => {
                        return Err(self.make_err(
                            format!("cannot assign to a constant of type: '{}'", lhs.to_string()),
                            &lhs_line_info,
                        ));
                    }
                    (context::Type::Fat(_), context::Type::Array { count, taipe }) => {
                        // array type can be coerced to a fat pointer
                        // TODO: record length information (for generating IR)
                    }
                    (context::Type::Noreturn, _) => {
                        return Err(self.make_err(
                            format!("cannot assign to: '{}'", lhs.to_string()),
                            &lhs_line_info,
                        ));
                    }
                    (_, context::Type::Noreturn) => {
                        // noreturn type can be coerced to any type
                    }
                    (lhs, rhs) => {
                        if lhs != rhs {
                            return Err(self
                                .make_err(
                                    format!("cannot assign to: '{}'", lhs.to_string()),
                                    &lhs_line_info,
                                )
                                .chain(self.make_note(
                                    format!("type of value is '{}'", rhs.to_string()),
                                    &rhs_line_info,
                                )));
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
        }
    }

    fn get_member(
        &mut self,
        scope: &Rc<RefCell<scope::Scope<'a>>>,
        name: &Token,
    ) -> CompileResult<Context<'a>> {
        if let Some(ctx) = self.resolve_member(&scope, &name.text)? {
            Ok(ctx)
        } else {
            Err(self.make_err(
                format!(
                    "'{}' has no member named '{}'",
                    scope.borrow().sym_path.to_string(),
                    &name.text
                ),
                name,
            ))
        }
    }

    fn resolve_member(
        &mut self,
        scope: &Rc<RefCell<scope::Scope<'a>>>,
        name: &str,
    ) -> CompileResult<Option<Context<'a>>> {
        if let Some(child) = scope.borrow().children.get(name) {
            let node = match &child.borrow().state {
                scope::State::NotVisited(node) => *node,
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
            let ctx = self.visit_decl(node, false)?;
            // Restore old scope
            self.cur_scope = old_cur_scope;
            return Ok(Some(ctx));
        }
        Ok(None)
    }

    fn get_name(&mut self, name: &Token) -> CompileResult<Context<'a>> {
        if let Some(mut ctx) = self.resolve_name(&name.text)? {
            if !ctx.taipe.is_const() {
                ctx.value = None;
            }
            Ok(ctx)
        } else {
            Err(self.make_err("undefined reference", name))
        }
    }

    fn resolve_name(&mut self, name: &str) -> CompileResult<Option<Context<'a>>> {
        {
            // Check in the current scope and go upwards
            let mut scope = Rc::clone(&self.cur_scope);
            loop {
                if let Some(ctx) = self.resolve_member(&scope, name)? {
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
            "__bool" => {
                return Ok(Some(Context {
                    taipe: context::Type::Typedef,
                    value: Some(context::Value::Type(context::Type::Bool)),
                }));
            }
            "__char" => {
                return Ok(Some(Context {
                    taipe: context::Type::Typedef,
                    value: Some(context::Value::Type(context::Type::Char)),
                }));
            }
            "__f32" => {
                return Ok(Some(Context {
                    taipe: context::Type::Typedef,
                    value: Some(context::Value::Type(context::Type::Float32)),
                }));
            }
            "__f64" => {
                return Ok(Some(Context {
                    taipe: context::Type::Typedef,
                    value: Some(context::Value::Type(context::Type::Float64)),
                }));
            }
            _ => Ok(None),
        }
    }

    fn bigint2usize(&self, num: Int, line_info: LineInfo) -> CompileResult<usize> {
        if let Some(num) = num.to_usize() {
            Ok(num)
        } else {
            Err(self.make_err(format!("usize cannot hold value: '{}'", num), &line_info))
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

    fn get_cur_scope(&self) -> Ref<scope::Scope<'a>> {
        self.cur_scope.borrow()
    }
}
