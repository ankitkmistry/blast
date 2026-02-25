use std::{
    cell::{Ref, RefCell},
    collections::HashMap,
    rc::Rc,
};

use crate::{
    ast,
    common::{CompileError, CompileResult, HasLineInfo},
    context::{self, Context},
    lexer::{TokenKind, TokenValue},
    scope::{self, HasSrcInfo},
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

struct Name<'a> {
    in_prog: bool,
    node: &'a ast::Decl,
}

impl<'a> Name<'a> {
    fn new(node: &'a ast::Decl) -> Self {
        Self {
            in_prog: false,
            node,
        }
    }
}

fn get_names<'a>(decls: &'a [ast::Decl]) -> HashMap<&'a str, Name<'a>> {
    let mut names = HashMap::new();
    for decl in decls {
        match decl {
            ast::Decl::Decl {
                name,
                taipe: _,
                object: _,
            } => {
                names.insert(name.text.as_str(), Name::new(decl));
            }
            ast::Decl::Import {
                line_info: _,
                items: _,
            } => {
                todo!("import statements are not supported yet")
            }
        }
    }
    names
}

pub struct Analyzer<'a> {
    cur_syms: HashMap<&'a str, Name<'a>>,
    roots: HashMap<String, Rc<RefCell<scope::Scope<'a>>>>,
    cur_scope: Rc<RefCell<scope::Scope<'a>>>,
}

impl<'a> Analyzer<'a> {
    pub fn new(file_path: &str, name: &str, root: &'a ast::Object) -> Self {
        let scope = scope::Scope::new_root(file_path, root);
        let mut roots = HashMap::new();
        roots.insert(name.to_owned(), Rc::clone(&scope));
        Self {
            cur_syms: HashMap::new(),
            roots,
            cur_scope: scope,
        }
    }

    pub fn analyze(&mut self) -> CompileResult<()> {
        let root = self.roots.values().next().unwrap();
        let Some(decls) = root.borrow().node.get_decls().take() else {
            // TODO: handle the else situation here
            return Ok(());
        };
        self.cur_syms = get_names(decls);
        for decl in decls {
            self.visit_decl(decl)?;
        }
        // dbg!(
        //     &self.get_cur_scope()
        //         .children
        //         .get("a")
        //         .unwrap()
        //         .borrow()
        //         .ctx
        //         .taipe
        // );
        // dbg!(
        //     &self.get_cur_scope()
        //         .children
        //         .get("b")
        //         .unwrap()
        //         .borrow()
        //         .ctx
        //         .taipe
        // );
        Ok(())
    }

    pub fn visit_decl(&mut self, node: &'a ast::Decl) -> CompileResult<Context<'a>> {
        match node {
            ast::Decl::Decl {
                name,
                taipe,
                object,
            } => {
                {
                    // Check for redeclaration
                    let scope = self.get_cur_scope();
                    let result = scope.children.get(&name.text);
                    if let Some(shit) = result {
                        let scope = shit.borrow();
                        let Some(object) = object else {
                            return Err(self
                                .make_err("redeclaration of symbol", name)
                                .chain(self.make_note("already declared here", &scope)));
                        };
                        if scope.node.get_line_info() != object.get_line_info() {
                            return Err(self
                                .make_err("redeclaration of symbol", name)
                                .chain(self.make_note("already declared here", &scope)));
                        }
                    }
                }
                // Set in progress
                if let Some(sym) = self.cur_syms.get_mut(name.text.as_str()) {
                    sym.in_prog = true;
                }
                let Some(object) = object else {
                    let Some(_) = taipe else {
                        unreachable!("probably some parser bug");
                    };
                    todo!("variables with types only are not supported yet")
                };
                let result = match object {
                    ast::Object::ExternModule { line_info, value } => {
                        todo!("modules are not supported yet")
                    }
                    ast::Object::Module { line_info, decls } => {
                        todo!("modules are not supported yet")
                    }
                    ast::Object::Struct { line_info, decls } => {
                        todo!("structs are not supported yet")
                    }
                    ast::Object::Union { line_info, decls } => {
                        todo!("unions are not supported yet")
                    }
                    ast::Object::Fun {
                        line_info,
                        params,
                        ret,
                        body,
                    } => todo!("functions are not supported yet"),
                    ast::Object::Typedef(node) => {
                        let taipe = self.visit_type(node)?;
                        if let context::Type::Typedef = taipe {
                            // context: type -> typedef, value -> typedef
                            // this cannot happen, there is no type of a type
                            // parser prevents this
                            return Err(self.make_err("invalid type alias", node));
                        }
                        let ctx = Context::from_type(taipe);
                        scope::Scope::add_child(
                            &self.cur_scope,
                            &name.text,
                            Some(name.clone()),
                            ctx.clone(),
                            object,
                        );
                        Ok(ctx)
                    }
                    ast::Object::Expr(expr) => self.define_global(name, object, expr),
                };
                // Set not in progress
                if let Some(sym) = self.cur_syms.get_mut(name.text.as_str()) {
                    sym.in_prog = false;
                }
                result
            }
            ast::Decl::Import {
                line_info: _,
                items: _,
            } => {
                todo!("import statements are not supported yet")
            }
        }
    }

    fn define_global(
        &mut self,
        name: &crate::lexer::Token,
        node: &'a ast::Object,
        expr: &'a ast::Expr,
    ) -> CompileResult<Context<'a>> {
        match self.visit_expr(expr) {
            Ok(ctx) => {
                scope::Scope::add_child(
                    &self.cur_scope,
                    &name.text,
                    Some(name.clone()),
                    ctx.clone(),
                    node,
                );
                Ok(ctx)
            }
            Err(err) => {
                if let CompileError::SemCyclic {
                    file_path,
                    line_info,
                } = err
                {
                    Err(self
                        .make_err("type inference is ambiguous", name)
                        .chain(self.make_note_with_path("declared here", file_path, &line_info)))
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
                        // TODO: Think about this
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
        if let context::Type::Typedef = &ctx.taipe {
        } else {
            return Err(self.make_err(
                format!("expression is not a type: '{}'", ctx.to_string()),
                node,
            ));
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

    fn resolve_name(&mut self, name: &str) -> CompileResult<Option<Context<'a>>> {
        {
            // First, check in the current scope
            let scope = self.get_cur_scope();
            if let Some(child) = scope.children.get(name) {
                return Ok(Some(child.borrow().ctx.clone()));
            }
        }
        // Then, check whether it is declared later maybe
        if let Some(sym) = self.cur_syms.get(name) {
            if sym.in_prog {
                Err(CompileError::SemCyclic {
                    file_path: self.get_cur_scope().get_src_path(),
                    line_info: if let ast::Decl::Decl {
                        name,
                        taipe: _,
                        object: _,
                    } = sym.node
                    {
                        name.get_line_info()
                    } else {
                        panic!("aashashahsh!!!!!!")
                    },
                })
            } else {
                Ok(Some(self.visit_decl(sym.node)?))
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
