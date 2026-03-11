use std::{
    cell::{Ref, RefCell},
    collections::HashMap,
    rc::Rc,
};

use crate::{
    ast,
    common::{CompileError, CompileResult, HasLineInfo, LineInfo},
    context::{self, Context},
    lexer::{Token, TokenKind, TokenValue},
    scope::{self, HasSrcInfo, State},
};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SymbolPath {
    elms: Vec<String>,
}

impl From<&str> for SymbolPath {
    fn from(value: &str) -> Self {
        SymbolPath {
            elms: value
                .to_string()
                .split('.')
                .map(|item| item.to_owned())
                .collect::<Vec<String>>(),
        }
    }
}

impl ToString for SymbolPath {
    fn to_string(&self) -> String {
        self.elms.join(".")
    }
}

impl SymbolPath {
    pub fn is_empty(&self) -> bool {
        self.elms.is_empty()
    }

    pub fn get_elements(&self) -> &[String] {
        &self.elms
    }
}

pub struct Analyzer<'a> {
    roots: HashMap<String, Rc<RefCell<scope::Scope<'a>>>>,
    cur_scope: Rc<RefCell<scope::Scope<'a>>>,
    saved_errs: Vec<CompileError>,
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
        let root = self.roots.values().next().unwrap();
        let Some(decls) = root.borrow().node.unwrap().get_decls().take() else {
            // TODO: handle the else situation here
            return Ok(());
        };
        self.pre_declare_decls(decls)?;
        for decl in decls {
            self.visit_decl(decl)?;
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

    pub fn pre_declare_fields(&mut self, decls: &'a [ast::Decl]) -> CompileResult<()> {
        // Pre declare all the members (of struct/union) except real fields
        // without visiting so that fields that are declared before
        // can access these types without interfering
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
                } => {
                    if let Some(obj) = object {
                        match obj {
                            ast::Object::ExternModule {
                                line_info: _,
                                value: _,
                            } => Err(self.make_err("'module' cannot used as a field", decl)),
                            ast::Object::Module {
                                line_info: _,
                                decls: _,
                            } => Err(self.make_err("'module' cannot used as a field", decl)),
                            ast::Object::Fun {
                                line_info: _,
                                params: _,
                                ret: _,
                                body: _,
                            } => Err(self.make_err("'function' cannot used as a field", decl)),
                            ast::Object::Typedef(_) => continue,
                            ast::Object::Expr(_) => continue,
                            _ => self.declare_sym(decl, &name, object.as_ref()),
                        }
                    } else {
                        self.declare_sym(decl, &name, object.as_ref())
                    }
                }
                ast::Decl::Using {
                    line_info: _,
                    items: _,
                } => Err(self.make_err("'use' declaration cannot used in a 'struct'", decl)),
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
        let result = scope::Scope::add_child(
            &self.cur_scope,
            &name.text,
            Some(name.clone()),
            scope::State::NotEvaled(node),
            object,
        );
        // Check for redeclaration
        if let Some(prev_scope) = result {
            Err(self
                .make_err("redeclaration of symbol", name)
                .chain(self.make_note("already declared here", &prev_scope.borrow())))
        } else {
            Ok(Rc::clone(
                self.get_cur_scope().children.get(&name.text).unwrap(),
            ))
        }
    }

    pub fn visit_decl(&mut self, node: &'a ast::Decl) -> CompileResult<Context<'a>> {
        macro_rules! colon_compulsory {
            ($parser:expr, $token:expr) => {
                // Check the colon thing
                let Some(eq_token) = $token else {
                    unreachable!("probably some parser bug");
                };
                if eq_token.kind != TokenKind::Colon {
                    self.saved_errs
                        .push(self.make_err("expected ':'", eq_token));
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
                scope.borrow_mut().state = scope::State::EvalInProg;
                // Unwrap the object
                let Some(object) = object else {
                    // Situation
                    // ---------------------------------
                    // name : type;
                    // ---------------------------------
                    let Some(taipe) = taipe else {
                        unreachable!("probably some parser bug");
                    };
                    let type_ctx = self.visit_type(taipe)?;
                    match type_ctx {
                        context::Type::Const(_) => todo!("mark scope as constant"),
                        context::Type::Module | context::Type::Typedef => {
                            return Err(self.make_err("value must be specified", node));
                        }
                        context::Type::Noreturn => {
                            return Err(self.make_err(
                                format!(
                                    "'{}' cannot be the type of a declaration",
                                    type_ctx.to_string()
                                ),
                                node,
                            ));
                        }
                        _ => {}
                    }
                    let ctx = Context {
                        taipe: type_ctx,
                        value: None,
                    };
                    scope.borrow_mut().state = State::Evaled(ctx.clone());
                    return Ok(ctx);
                };
                let ctx: Context<'_> = match object {
                    ast::Object::ExternModule { line_info, value } => {
                        colon_compulsory!(self, eq_token);
                        todo!("modules are not supported yet")
                    }
                    ast::Object::Module { line_info, decls } => {
                        colon_compulsory!(self, eq_token);
                        todo!("modules are not supported yet")
                    }
                    ast::Object::Struct { line_info, decls } => {
                        // TODO: type punning syntax
                        // A :: struct {
                        //     foo: i32;
                        // }
                        // B :: struct {
                        //     using A;
                        //     bar: i32;
                        // }
                        colon_compulsory!(self, eq_token);
                        // Begin new scope
                        let old_cur_scope = Rc::clone(&self.cur_scope);
                        self.cur_scope = Rc::clone(&scope);
                        // Pre declaration round
                        self.pre_declare_fields(decls)?;
                        // Start visiting
                        let mut fields: HashMap<String, Context<'a>> = HashMap::new();
                        for decl in decls {
                            let ctx = self.visit_decl(decl)?;
                            // Check the type of the fields
                            match ctx.taipe {
                                context::Type::Function { ret: _, params: _ } => {
                                    return Err(
                                        self.make_err("function cannot be used as a field", decl)
                                    );
                                }
                                context::Type::Module
                                | context::Type::Typedef
                                | context::Type::Noreturn => {
                                    return Err(self.make_err(
                                        format!(
                                            "'{}' cannot be used as a field",
                                            ctx.taipe.to_string()
                                        ),
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
                            fields.insert(name, ctx);
                        }
                        // Create the context
                        let ctx = Context {
                            taipe: context::Type::Typedef,
                            value: Some(context::Value::Struct(context::Struct {
                                fields,
                                node: object,
                            })),
                        };
                        // Mark it evaluated
                        scope.borrow_mut().state = State::Evaled(ctx.clone());
                        // Restore old scope
                        self.cur_scope = old_cur_scope;
                        ctx
                    }
                    ast::Object::Union { line_info, decls } => {
                        colon_compulsory!(self, eq_token);
                        todo!("unions are not supported yet")
                    }
                    ast::Object::Fun {
                        line_info,
                        params,
                        ret,
                        body,
                    } => {
                        colon_compulsory!(self, eq_token);
                        todo!("functions are not supported yet")
                    }
                    ast::Object::Typedef(node) => {
                        colon_compulsory!(self, eq_token);
                        let taipe = self.visit_type(node)?;
                        if let context::Type::Typedef = taipe {
                            // context: type -> typedef, value -> typedef
                            // this cannot happen, there is no type of a type
                            // parser prevents this
                            return Err(self.make_err("invalid type alias", node));
                        }
                        let ctx = Context::from_type(taipe);
                        scope.borrow_mut().state = scope::State::Evaled(ctx.clone());
                        ctx
                    }
                    ast::Object::Expr(expr) => {
                        // TODO: Handle module variables and type variables
                        // They should be constant
                        let ctx = self.visit_var(name, expr)?;
                        scope.borrow_mut().state = scope::State::Evaled(ctx.clone());
                        ctx
                    }
                };
                self.resolve_assign(taipe.as_ref(), eq_token.as_ref(), object, ctx)
            }
            ast::Decl::Using {
                line_info: _,
                items: _,
            } => {
                todo!("import statements are not supported yet")
            }
        }
    }

    fn visit_var(
        &mut self,
        name: &crate::lexer::Token,
        expr: &'a ast::Expr,
    ) -> CompileResult<Context<'a>> {
        match self.visit_expr(expr) {
            Ok(ctx) => Ok(ctx),
            Err(err) => {
                if let CompileError::SemCyclic {
                    file_path,
                    line_info,
                } = err
                {
                    Err(self
                        .make_err(
                            "declaration is ambiguous, encountered cyclic references",
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
                assert!(
                    items.len() == 1,
                    "type resolution more than 1 not implemented yet"
                );
                let result = self.resolve_name(&items[0].text)?;
                let Some(ctx) = result else {
                    return Err(self.make_err("undefined reference", &items[0]));
                };
                ctx
            }
            ast::Type::Function {
                line_info,
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
            ast::Type::Const {
                token: _,
                taipe: node,
            } => {
                let taipe = self.visit_type(node)?;
                match &taipe {
                    context::Type::Const(_) => {
                        unreachable!("already handled in the parser");
                    }
                    context::Type::Module => {
                        return Err(
                            self.make_err("'const' qualifier cannot be applied on 'module'", node)
                        );
                    }
                    context::Type::Typedef => {
                        return Err(
                            self.make_err("'const' qualifier cannot be applied on 'typedef'", node)
                        );
                    }
                    _ => Context::from_type(context::Type::Const(Box::new(taipe))),
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
            } => todo!("implement this after implementing comptime eval"),
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
            ast::Expr::Unary { op, expr } => todo!(),
            ast::Expr::Member { expr, name } => todo!(),
            ast::Expr::Call {
                line_info,
                expr,
                args,
            } => todo!(),
            ast::Expr::Index {
                line_info,
                expr,
                items,
            } => todo!(),
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
                TokenKind::IntLit => todo!("integer literals are not supported yet"),
                TokenKind::FloatLit => todo!("floating point literals are not supported yet"),
                TokenKind::Ident => {
                    if let Some(ctx) = self.resolve_name(&token.text)? {
                        Ok(ctx)
                    } else {
                        Err(self.make_err("undefined reference", token))
                    }
                }
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
                assert!(
                    values.len() == 0,
                    "compile time evaluation not supported yet"
                );
                Ok(Context::from_tuple(types, values))
            }
            ast::Expr::ArrayLit { line_info, items } => todo!(),
        }
    }

    fn resolve_assign(
        &mut self,
        taipe: Option<&'a ast::Type>,
        eq_token: Option<&Token>,
        object: &ast::Object,
        ctx: Context<'a>,
    ) -> CompileResult<Context<'a>> {
        // Type checking
        // TODO: Type checking done here is strict
        // And assignment should not be this strict.
        // For example:
        //      val : i32 = 0i64;
        // Does not work.
        if let Some(type_node) = taipe {
            // Situation
            // ---------------------------------
            // name : type : object;
            // name : type = object;
            // ---------------------------------
            let mut errs = Vec::new();
            let type_ctx = self.visit_type(type_node)?;
            if type_ctx != ctx.taipe {
                errs.push(
                    self.make_err("types do not match", type_node)
                        .chain(self.make_note(
                            format!("type of value is '{}'", ctx.taipe.to_string()),
                            object,
                        )),
                );
            }
            let eq_token = eq_token.unwrap();
            if eq_token.kind == TokenKind::Colon {
                // Situation
                // ---------------------------------
                // name : type : object;
                // ---------------------------------
                if !ctx.taipe.is_const() {
                    errs.push(
                        self.make_err("type should be 'const'", type_node)
                            .chain(self.make_note("':' is used here", eq_token)),
                    );
                }
            } else if eq_token.kind == TokenKind::Equal {
                // Situation
                // ---------------------------------
                // name : type = object;
                // ---------------------------------
                if ctx.taipe.is_const() {
                    errs.push(
                        self.make_err("expected ':'", eq_token)
                            .chain(self.make_note("type is declared 'const' here", type_node)),
                    );
                }
            } else {
                unreachable!("probably some parser bug");
            }
            // Return the accumulated errors
            if !errs.is_empty() {
                return Err(CompileError::Errors(errs));
            }
        }
        Ok(ctx)
    }

    fn resolve_name(&mut self, name: &str) -> CompileResult<Option<Context<'a>>> {
        struct Result<'a> {
            state: scope::State<'a>,
            line_info: LineInfo,
        }

        let result: Option<Result<'a>>;
        result = {
            if name == "__bool" {
                return Ok(Some(Context {
                    taipe: context::Type::Typedef,
                    value: Some(context::Value::Type(context::Type::Bool)),
                }));
            }
            // First, check in the current scope
            let scope = self.get_cur_scope();
            scope.children.get(name).map(|child| Result {
                state: child.borrow().state.clone(),
                line_info: child.borrow().get_line_info(),
            })
        };
        if let Some(result) = result {
            match result.state {
                scope::State::NotEvaled(node) => Ok(Some(self.visit_decl(node)?)),
                scope::State::EvalInProg => Err(CompileError::SemCyclic {
                    file_path: self.get_cur_scope().get_src_path(),
                    line_info: result.line_info,
                }),
                scope::State::Evaled(ctx) => Ok(Some(ctx.clone())),
            }
        } else {
            Ok(None)
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
