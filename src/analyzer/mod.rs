use std::{
    cell::{Ref, RefCell},
    collections::{HashMap, HashSet},
    rc::Rc,
};

use num_traits::cast::ToPrimitive;

use crate::{
    ast,
    cfg::{ControlGraph, ControlInfo, ControlNode, ControlNodeId},
    common::{CompileError, CompileResult, HasLineInfo, Layout, LineInfo, Settings, fuzzy_search_best},
    context::{self, Context},
    lexer::{Token, TokenKind},
    scope::{self, HasSrcInfo, Payload, State, SymbolPath},
};

pub struct SemResult<'a> {
    /// Root scopes that are present in the scope trees
    pub roots: HashMap<String, Rc<RefCell<scope::Scope<'a>>>>,
    /// Generated warnings about the code
    pub warnings: Vec<CompileError>,
}

pub struct Analyzer<'a> {
    /// Root scopes that are present in the scope trees
    roots: HashMap<String, Rc<RefCell<scope::Scope<'a>>>>,
    /// Current scope in which things are being evaluated
    cur_scope: Rc<RefCell<scope::Scope<'a>>>,
    /// Compiler settings to customise semantic analysis
    settings: Settings,
    /// Saved errors to continue compilation and accumulate more errors
    saved_errs: Vec<CompileError>,
    /// Generated warnings about the code
    warnings: Vec<CompileError>,

    /// The type that is used for '__int'
    type_int: context::Type<'a>,
    /// The type that is used for '__uint'
    type_uint: context::Type<'a>,
    /// The type that is used for '__size'
    type_isize: context::Type<'a>,
    /// The type that is used for '__usize'
    type_usize: context::Type<'a>,
}

pub(crate) mod decl;
pub(crate) mod expr;

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
        } else if !self.saved_errs.is_empty() {
            // If there are any accumulated errors return them
            Err(CompileError::Errors(self.saved_errs).chain(CompileError::Errors(self.warnings)))
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

    fn visit_stmt(&mut self, node: &'a ast::Stmt) -> CompileResult<Context<'a>> {
        match node {
            ast::Stmt::If {
                line_info: _,
                expr,
                then_body,
                else_body,
            } => self.visit_if_stmt(expr, then_body, else_body.as_ref().map(|s| &**s), node.get_line_info()),
            ast::Stmt::While {
                line_info: _,
                label,
                expr,
                then_body,
            } => self.visit_while_stmt(label.as_ref(), expr, then_body, node.get_line_info()),
            ast::Stmt::Block { line_info, stmts } => self.visit_block(*line_info, stmts),
            ast::Stmt::Yield { token: _, expr } => {
                let mut ctx = self.visit_expr(expr)?;
                if ctx.taipe.is_varint() {
                    let context::Value::Imm(ref imm) = ctx.value else {
                        unreachable!("probably some analyzer bug");
                    };
                    ctx.taipe = self.type_int.clone();
                    ctx.value = context::Value::Imm(self.transform_varint_to_int(imm, expr)?);
                }
                self.mut_current_block_data(|data| {
                    data.cfg.insert_edge(data.cf_last, data.cf_end);
                    data.cf_last = data.cf_unreachable;
                });
                Ok(ctx)
            }
            ast::Stmt::Continue { token, label } => self.visit_continue(token, label.as_ref()),
            ast::Stmt::Break { token, label } => self.visit_break(token, label.as_ref()),
            ast::Stmt::Return { token, expr } => self.visit_return(token, expr.as_ref()),
            ast::Stmt::Decl(decl) => {
                let _ = self.visit_decl(decl, false)?;
                Ok(Context::from_void())
            }
            ast::Stmt::Expr(expr) => {
                let ctx = self.visit_expr(expr)?;
                Ok(Context {
                    is_lvalue: false,
                    taipe: context::Type::Void,
                    value: context::Value::Eval(Box::new(ctx)),
                })
            }
            ast::Stmt::Nop(_) => Ok(Context::from_void()),
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
            *ret.clone()
        };
        if ret.is_noreturn() {
            return Err(self.make_err(
                format!(
                    "cannot return from a '{}' function",
                    context::Type::Noreturn
                ),
                token,
            ));
        }
        // Get some line info
        let scope::Payload::Function(scope::Function {
            param_infos: _,
            loop_stack: _,
            ret_line_info,
        }) = function.borrow().payload
        else {
            unreachable!("probably some analyzer bug");
        };
        let ret_line_info = ret_line_info.unwrap_or_else(|| function.borrow().get_line_info());
        // Check return
        if let Some(expr) = expr {
            if ret.is_void() {
                return Err(self.make_err("invalid expression", expr).chain(self.make_note(
                    format!("function expects return type '{}'", ret),
                    &ret_line_info,
                )));
            }
            let rhs = self.visit_expr(expr)?;

            // cfg: direct the control flow as return node
            self.mut_current_block_data(|data| {
                let cf_return = data.cfg.insert_vertex(ControlNode::Return);
                data.cfg.insert_edge(data.cf_last, cf_return);
                data.cf_last = data.cf_unreachable;
            });

            let ctx = self.resolve_assign(Some((ret, ret_line_info)), None, Some((rhs, expr.get_line_info())))?;
            Ok(Context {
                is_lvalue: false,
                taipe: context::Type::Noreturn,
                value: context::Value::Ret(Box::new(ctx)),
            })
        } else {
            // cfg: direct the control flow as return node
            self.mut_current_block_data(|data| {
                let cf_return = data.cfg.insert_vertex(ControlNode::Return);
                data.cfg.insert_edge(data.cf_last, cf_return);
                data.cf_last = data.cf_unreachable;
            });

            if !ret.is_void() {
                return Err(self
                    .make_err("expected <expression> for 'return'", token)
                    .chain(self.make_note(
                        format!("function expects return type '{}'", ret),
                        &ret_line_info,
                    )));
            }
            Ok(Context {
                is_lvalue: false,
                taipe: context::Type::Noreturn,
                value: context::Value::RetVoid,
            })
        }
    }

    fn visit_break(&mut self, token: &Token, label: Option<&Token>) -> CompileResult<Context<'a>> {
        self.use_current_function_data(|data| {
            let cf_break = if let Some(label) = label {
                if let Some(loop_info) = data.loop_stack.get(&label.text) {
                    loop_info.cf_break
                } else {
                    let mut searched_names = HashSet::new();
                    for (name, _) in &data.loop_stack {
                        searched_names.insert(name.clone());
                    }
                    return Err(self
                        .make_err(format!("undefined loop label '{}'", label.text), label)
                        .chain(self.make_did_you_mean_help(&label.text, &searched_names)));
                }
            } else if let Some((_, loop_info)) = data.loop_stack.last() {
                loop_info.cf_break
            } else {
                return Err(self.make_err(format!("'{}' can be used only in a loop", token.text), token));
            };
            // cfg: direct the control flow to cf_break node
            self.mut_current_block_data(|data| {
                data.cfg.insert_edge(data.cf_last, cf_break);
                data.cf_last = data.cf_unreachable;
            });
            Ok(Context::from_noreturn())
        })
    }

    fn visit_continue(&mut self, token: &Token, label: Option<&Token>) -> CompileResult<Context<'a>> {
        self.use_current_function_data(|data| {
            let cf_continue = if let Some(label) = label {
                if let Some(loop_info) = data.loop_stack.get(&label.text) {
                    loop_info.cf_continue
                } else {
                    let mut searched_names = HashSet::new();
                    for (name, _) in &data.loop_stack {
                        searched_names.insert(name.clone());
                    }
                    return Err(self
                        .make_err(format!("undefined loop label '{}'", label.text), label)
                        .chain(self.make_did_you_mean_help(&label.text, &searched_names)));
                }
            } else if let Some((_, loop_info)) = data.loop_stack.last() {
                loop_info.cf_continue
            } else {
                return Err(self.make_err(format!("'{}' can be used only in a loop", token.text), token));
            };
            // cfg: direct the control flow to cf_continue node
            self.mut_current_block_data(|data| {
                data.cfg.insert_edge(data.cf_last, cf_continue);
                data.cf_last = data.cf_unreachable;
            });
            Ok(Context::from_noreturn())
        })
    }

    fn visit_while_stmt(
        &mut self,
        label: Option<&Token>,
        expr: &'a ast::Expr,
        then_body: &'a ast::Stmt,
        line_info: LineInfo,
    ) -> Result<Context<'a>, CompileError> {
        // cfg: create the break and continue node for this loop
        let cf_break = self.mut_current_block_data(|data| data.cfg.insert_vertex(ControlNode::Junction));
        let cf_continue = self.mut_current_block_data(|data| data.cfg.insert_vertex(ControlNode::Junction));

        // cfg: Get the loop start flow
        // let cf_loop_start = cf_continue;
        self.mut_current_block_data(|data| {
            data.cfg.insert_edge(data.cf_last, cf_continue);
            data.cf_last = cf_continue;
        });

        let cond = self.visit_expr(expr)?;
        if !cond.taipe.is_bool() {
            return Err(self.make_err(
                format!(
                    "expected value of type '{}' but got value of type '{}'",
                    context::Type::Bool,
                    cond
                ),
                expr,
            ));
        }

        // cfg: Get the cond flow
        let cf_cond = self.use_current_block_data(|data| data.cf_last);

        self.mut_current_function_data(|data| {
            let loop_info = scope::LoopInfo { cf_break, cf_continue };
            if let Some(label) = label {
                data.loop_stack.insert(label.text.clone(), loop_info);
            } else {
                data.loop_stack.insert(
                    format!(
                        "loop{}$",
                        self.cur_scope
                            .borrow()
                            .loop_counter
                            .fetch_add(1, std::sync::atomic::Ordering::SeqCst)
                    ),
                    loop_info,
                );
            }
        });
        let then_body_result = self.visit_stmt(then_body)?;

        // cfg: Get the loop end flow
        let cf_loop_end = self.use_current_block_data(|data| data.cf_last);

        // cfg: Stitch them together
        self.mut_current_block_data(|data| {
            data.cfg.insert_edge(cf_loop_end, cf_continue);
            data.cfg.insert_edge(cf_cond, cf_break);
            data.cf_last = cf_break;
        });

        self.mut_current_function_data(|data| {
            data.loop_stack.pop();
        });
        if then_body_result.taipe.is_noreturn() || then_body_result.taipe.is_void() {
            Ok(Context {
                is_lvalue: false,
                taipe: context::Type::Void,
                value: context::Value::While {
                    line_info,
                    cond: Box::new(cond),
                    body_ctx: Box::new(then_body_result),
                },
            })
        } else {
            Err(self.make_err(
                format!(
                    "expected '{}' but got '{}'",
                    context::Type::Void,
                    then_body_result
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
        line_info: LineInfo,
    ) -> Result<Context<'a>, CompileError> {
        let cond = self.visit_expr(expr)?;
        if !cond.taipe.is_bool() {
            return Err(self.make_err(
                format!(
                    "expected value of type '{}' but got value of type '{}'",
                    context::Type::Bool,
                    cond
                ),
                expr,
            ));
        }

        // cfg: Get the cond flow
        let cf_cond = self.use_current_block_data(|data| data.cf_last);

        let then_body_result = self.visit_stmt(then_body)?;

        // cfg: Get the then branch flow
        let cf_then = self.use_current_block_data(|data| data.cf_last);

        if let Some(else_body) = else_body {
            // cfg: Let the flow before else branch descend from cf_cond
            self.mut_current_block_data(|data| {
                data.cf_last = cf_cond;
            });

            let else_body_result = self.visit_stmt(else_body)?;

            // cfg: Get the else branch flow
            let cf_else = self.use_current_block_data(|data| data.cf_last);

            // cfg: Stitch them together
            self.mut_current_block_data(|data| {
                let cf_join = data.cfg.insert_vertex(ControlNode::Junction);
                data.cfg.insert_edge(cf_then, cf_join);
                data.cfg.insert_edge(cf_else, cf_join);
                data.cf_last = cf_join;
            });

            if then_body_result.taipe.is_noreturn() {
                Ok(Context {
                    is_lvalue: else_body_result.is_lvalue,
                    taipe: else_body_result.taipe.clone(),
                    value: context::Value::IfElse {
                        line_info,
                        cond: Box::new(cond),
                        then_ctx: Box::new(then_body_result),
                        else_ctx: Box::new(else_body_result),
                    },
                })
            } else if else_body_result.taipe.is_noreturn() {
                Ok(Context {
                    is_lvalue: then_body_result.is_lvalue,
                    taipe: then_body_result.taipe.clone(),
                    value: context::Value::IfElse {
                        line_info,
                        cond: Box::new(cond),
                        then_ctx: Box::new(then_body_result),
                        else_ctx: Box::new(else_body_result),
                    },
                })
            } else if then_body_result.taipe == else_body_result.taipe {
                // TODO: allow mixing of compatible values
                Ok(Context {
                    is_lvalue: then_body_result.is_lvalue && else_body_result.is_lvalue,
                    taipe: then_body_result.taipe.clone(),
                    value: context::Value::IfElse {
                        line_info,
                        cond: Box::new(cond),
                        then_ctx: Box::new(then_body_result),
                        else_ctx: Box::new(else_body_result),
                    },
                })
            } else {
                let line_info = if let context::Value::Reference(ref scope) = else_body_result.value {
                    scope.borrow().get_line_info()
                } else {
                    else_body.get_line_info()
                };
                return Err(self.make_err(
                    format!(
                        "expected '{}' but got '{}'",
                        then_body_result,
                        else_body_result,
                    ),
                    &line_info,
                ));
            }
        } else {
            // cfg: Stitch them together
            self.mut_current_block_data(|data| {
                let cf_join = data.cfg.insert_vertex(ControlNode::Junction);
                data.cfg.insert_edge(cf_then, cf_join);
                data.cfg.insert_edge(cf_cond, cf_join);
                data.cf_last = cf_join;
            });

            if then_body_result.taipe.is_noreturn() {
                Ok(Context {
                    is_lvalue: false,
                    taipe: context::Type::Noreturn,
                    value: context::Value::If {
                        line_info,
                        cond: Box::new(cond),
                        then_ctx: Box::new(then_body_result),
                    },
                })
            } else if then_body_result.taipe.is_void() {
                Ok(Context {
                    is_lvalue: false,
                    taipe: context::Type::Void,
                    value: context::Value::If {
                        line_info,
                        cond: Box::new(cond),
                        then_ctx: Box::new(then_body_result),
                    },
                })
            } else {
                Err(self.make_err(
                    format!(
                        "expected '{}' but got '{}'",
                        context::Type::Void,
                        then_body_result
                    ),
                    then_body,
                ))
            }
        }
    }

    fn create_block_scope(&mut self, line_info: LineInfo) -> Rc<RefCell<scope::Scope<'a>>> {
        // Generate unique block name
        let block_name = format!(
            "block{}$",
            self.cur_scope
                .borrow()
                .block_counter
                .fetch_add(1, std::sync::atomic::Ordering::SeqCst)
        );
        // Create a block scope
        let scope = scope::Scope::add_child(
            &self.cur_scope,
            scope::ScopeKind::Block,
            &block_name,
            scope::State::VisitInProg,
            &line_info,
        );
        // Create its own control graph
        let mut cfg = ControlGraph::new();
        let cf_start = cfg.insert_vertex(ControlNode::Start);
        let cf_unreachable = cfg.insert_vertex(ControlNode::Unreachable);
        let cf_end = cfg.insert_vertex(ControlNode::End);
        scope.borrow_mut().payload = scope::Payload::Block(scope::Block {
            cfg,
            cf_start,
            cf_end,
            cf_last: cf_start,
            cf_unreachable,
        });
        scope
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
        // For better error output change the line info of the block scope
        if !stmts.is_empty() {
            scope.borrow_mut().line_info = stmts[last_stmt_index - 1].get_line_info();
        }
        // cfg: everything after this is unreachable
        self.mut_current_block_data(|data| {
            if data.cf_last != data.cf_end {
                data.cfg.insert_edge(data.cf_last, data.cf_end);
                data.cf_last = data.cf_unreachable;
            }
        });
        if last_stmt_index < stmts.len() {
            // Check them anyway
            for stmt in &stmts[last_stmt_index..] {
                self.visit_stmt(stmt)?;
            }
            // We have unreachable code
            self.warnings
                .push(self.make_warning("unreachable code", &&stmts[last_stmt_index..]));
        }
        // Restore old scope
        self.cur_scope = old_cur_scope;
        // cfg: now traverse the cfg
        {
            let scope::Payload::Block(ref data) = scope.borrow().payload else {
                unreachable!("probably some analyzer bug");
            };
            // Track all variables by checking their initialization and usage (by performing DFS on the CFG)
            if let Err(err) = self.traverse_cfg(&data.cfg, data.cf_start) {
                self.saved_errs.push(err);
            }
        }
        // Create the context
        block_ret_type = block_ret_type.add_const();
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
        Ok(result)
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
                                format!("cannot use '.' operator on '{}'", ctx.taipe),
                                &items[..index].to_vec(),
                            ));
                        }
                    };
                    index += 1;
                }
                if !ctx.taipe.is_typedef() {
                    return Err(self.make_err(format!("expression is not a type: '{}'", ctx), node));
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
                                self.make_err(format!("'{}' cannot be a parameter type", taipe), param)
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
                                        taipe
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
                let length_ctx = self.compeval_trivial(length_ctx, expr)?;
                if !length_ctx.taipe.is_unsigned_integer() {
                    return Err(self
                        .make_err("argument of index operator should be an unsigned integer type", expr)
                        .chain(self.make_note(format!("but got '{}'", length_ctx.taipe), expr)));
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
                        return Err(self.make_err(format!("fat pointer to '{}' is invalid", taipe), node));
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
                            return Err(self.make_err(format!("'{}' cannot be a tuple item", taipe), node));
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

    fn get_default_value(&self, taipe: &context::Type<'a>, line_info: &impl HasLineInfo) -> CompileResult<Context<'a>> {
        self.get_default_value_impl(taipe, taipe, line_info)
    }

    fn get_default_value_impl(
        &self,
        top_type: &context::Type<'a>,
        cur_type: &context::Type<'a>,
        line_info: &impl HasLineInfo,
    ) -> CompileResult<Context<'a>> {
        match cur_type {
            context::Type::Bool => Ok(Context::from_bool(false)),
            context::Type::Char => Ok(Context::from_char('\0')),
            context::Type::VarInt => unreachable!("probably some analyzer bug"),
            context::Type::Int8 => Ok(Context::from_i8(0)),
            context::Type::Int16 => Ok(Context::from_i16(0)),
            context::Type::Int32 => Ok(Context::from_i32(0)),
            context::Type::Int64 => Ok(Context::from_i64(0)),
            context::Type::Int128 => Ok(Context::from_i128(0)),
            context::Type::Uint8 => Ok(Context::from_u8(0)),
            context::Type::Uint16 => Ok(Context::from_u16(0)),
            context::Type::Uint32 => Ok(Context::from_u32(0)),
            context::Type::Uint64 => Ok(Context::from_u64(0)),
            context::Type::Uint128 => Ok(Context::from_u128(0)),
            context::Type::Float32 => Ok(Context::from_f32(0.0)),
            context::Type::Float64 => Ok(Context::from_f64(0.0)),
            context::Type::Const(taipe) => Ok(self.get_default_value_impl(top_type, taipe, line_info)?.add_const()),
            context::Type::Pointer(_) => todo!("pointer default value"),
            context::Type::Fat(_) => todo!("fat pointer default value"),
            // TODO: implement custom type default values
            // context::Type::Basic(ref_cell) => todo!("custom type default value"),
            context::Type::Array {
                count,
                taipe: item_type,
            } => {
                let mut values = Vec::new();
                for _ in 0..*count {
                    values.push(self.get_default_value_impl(top_type, item_type, line_info)?.value);
                }
                Ok(Context {
                    is_lvalue: false,
                    taipe: cur_type.clone(),
                    value: context::Value::Tuple(values),
                })
            }
            context::Type::Tuple(items) => {
                let mut values = Vec::new();
                for item in items {
                    values.push(self.get_default_value_impl(top_type, item, line_info)?.value);
                }
                Ok(Context {
                    is_lvalue: false,
                    taipe: cur_type.clone(),
                    value: context::Value::Tuple(values),
                })
            }
            _ => Err(self
                .make_err(
                    format!("type does not have a default value: '{}'", top_type),
                    line_info,
                )
                .chain(self.make_note_no_path(format!(
                    "error occured because this type does not have a default value: '{}'",
                    cur_type
                )))),
        }
    }

    fn get_zero_value(&self, taipe: &context::Type<'a>, line_info: &impl HasLineInfo) -> CompileResult<Context<'a>> {
        self.get_zero_value_impl(taipe, taipe, line_info)
    }

    fn get_zero_value_impl(
        &self,
        top_type: &context::Type<'a>,
        cur_type: &context::Type<'a>,
        line_info: &impl HasLineInfo,
    ) -> CompileResult<Context<'a>> {
        match cur_type {
            context::Type::Bool => Ok(Context::from_bool(false)),
            context::Type::Char => Ok(Context::from_char('\0')),
            context::Type::VarInt => unreachable!("probably some analyzer bug"),
            context::Type::Int8 => Ok(Context::from_i8(0)),
            context::Type::Int16 => Ok(Context::from_i16(0)),
            context::Type::Int32 => Ok(Context::from_i32(0)),
            context::Type::Int64 => Ok(Context::from_i64(0)),
            context::Type::Int128 => Ok(Context::from_i128(0)),
            context::Type::Uint8 => Ok(Context::from_u8(0)),
            context::Type::Uint16 => Ok(Context::from_u16(0)),
            context::Type::Uint32 => Ok(Context::from_u32(0)),
            context::Type::Uint64 => Ok(Context::from_u64(0)),
            context::Type::Uint128 => Ok(Context::from_u128(0)),
            context::Type::Float32 => Ok(Context::from_f32(0.0)),
            context::Type::Float64 => Ok(Context::from_f64(0.0)),
            context::Type::Const(taipe) => Ok(self.get_zero_value_impl(top_type, taipe, line_info)?.add_const()),
            context::Type::Pointer(_) => todo!("pointer zero value"),
            context::Type::Fat(_) => todo!("fat pointer zero value"),
            // TODO: implement custom type zero values
            // context::Type::Basic(ref_cell) => todo!("custom type zero value"),
            context::Type::Array {
                count,
                taipe: item_type,
            } => {
                let mut values = Vec::new();
                for _ in 0..*count {
                    values.push(self.get_zero_value_impl(top_type, item_type, line_info)?.value);
                }
                Ok(Context {
                    is_lvalue: false,
                    taipe: cur_type.clone(),
                    value: context::Value::Tuple(values),
                })
            }
            context::Type::Tuple(items) => {
                let mut values = Vec::new();
                for item in items {
                    values.push(self.get_zero_value_impl(top_type, item, line_info)?.value);
                }
                Ok(Context {
                    is_lvalue: false,
                    taipe: cur_type.clone(),
                    value: context::Value::Tuple(values),
                })
            }
            _ => Err(self
                .make_err(
                    format!("type does not have a zero value: '{}'", top_type),
                    line_info,
                )
                .chain(self.make_note_no_path(format!(
                    "error occured because this type does not have a zero value: '{}'",
                    cur_type
                )))),
        }
    }

    fn traverse_cfg(&mut self, cfg: &ControlGraph<'a>, node_id: ControlNodeId) -> CompileResult<()> {
        // debug!("in: {}", self.cur_scope.borrow().sym_path);
        let result = self.traverse_cfg_impl(cfg, node_id, &mut HashSet::new(), HashMap::new(), 0);
        // debug!("");
        result
    }
    fn traverse_cfg_impl(
        &mut self,
        cfg: &ControlGraph<'a>,
        node_id: ControlNodeId,
        visited: &mut HashSet<ControlNodeId>,
        mut declared_vars: HashMap<SymbolPath, ControlInfo<'a>>,
        mut depth: usize,
    ) -> CompileResult<()> {
        // Mark as visited
        visited.insert(node_id);
        let mut err = CompileError::Errors(Vec::new());

        // Track variables
        let mut is_end = false;
        let node = cfg.get_vertex(node_id).unwrap();
        match node {
            ControlNode::Start => {
                // debug!("{}start", " ".repeat(depth));
                depth += 1;
            }
            ControlNode::Junction => {
                // debug!("{}junction", " ".repeat(depth));
            }
            ControlNode::Info(info) => match info {
                ControlInfo::VarDeclared { scope } => {
                    // debug!(
                    //     "{}declared variable -> {}:{}",
                    //     " ".repeat(depth),
                    //     line_info.line_start,
                    //     line_info.col_start
                    // );
                    declared_vars.insert(scope.borrow().sym_path.clone(), info.clone());
                }
                ControlInfo::VarUsed { line_info, scope } => {
                    // debug!(
                    //     "{}variable used -> {}:{}",
                    //     " ".repeat(depth),
                    //     line_info.line_start,
                    //     line_info.col_start
                    // );
                    if let Some(prev_cf_info) = declared_vars.get(&scope.borrow().sym_path) {
                        match prev_cf_info {
                            ControlInfo::VarDeclared { scope: _ } => {
                                let msg = format!("'{}' may be uninitialized", scope.borrow().name);
                                err = err
                                    .chain(self.make_err(msg, line_info))
                                    .chain(self.make_note("declared here", &scope.borrow()));
                            }
                            _ => {}
                        }
                    } else {
                        // probably the declaration is outside of this scope
                        self.mut_current_block_data(|data| {
                            let cf_node = data.cfg.insert_vertex(ControlNode::Info(ControlInfo::VarUsed {
                                line_info: *line_info,
                                scope: Rc::clone(scope),
                            }));
                            data.cfg.insert_edge(data.cf_last, cf_node);
                            data.cf_last = cf_node;
                        })
                    }
                }
                ControlInfo::VarAssigned { line_info, scope } => {
                    // debug!(
                    //     "{}declared assigned -> {}:{}",
                    //     " ".repeat(depth),
                    //     line_info.line_start,
                    //     line_info.col_start
                    // );
                    if let Some(prev_cf_info) = declared_vars.get_mut(&scope.borrow().sym_path) {
                        match prev_cf_info {
                            // TODO: implement this
                            // this is not complete as we have to check whether a variable
                            // assignment is read in all possible consequent control flows
                            // ControlInfo::VarAssigned { line_info, scope: _ } => {
                            //     self.warnings.push(self.make_warning("value of assignment is never read", line_info));
                            // }
                            _ => *prev_cf_info = info.clone(),
                        }
                    } else {
                        // probably the declaration is outside of this scope
                        self.mut_current_block_data(|data| {
                            let cf_node = data.cfg.insert_vertex(ControlNode::Info(ControlInfo::VarAssigned {
                                line_info: *line_info,
                                scope: Rc::clone(scope),
                            }));
                            data.cfg.insert_edge(data.cf_last, cf_node);
                            data.cf_last = cf_node;
                        })
                    }
                }
            },
            ControlNode::Return => {
                depth -= 1;
                // debug!("{}return", " ".repeat(depth));
                is_end = true;
            }
            ControlNode::End => {
                depth -= 1;
                // debug!("{}end", " ".repeat(depth));
                is_end = true;
            }
            ControlNode::Unreachable => unreachable!("probably some control flow contruction bug"),
        }

        // Traverse other destination nodes
        let outgoing = cfg.outgoing(node_id);
        for dest_node_id in outgoing {
            assert!(!is_end);
            if !visited.contains(&dest_node_id) {
                if let Err(dest_err) = self.traverse_cfg_impl(cfg, dest_node_id, visited, declared_vars.clone(), depth)
                {
                    // Accumulate errors
                    err = err.chain(dest_err)
                };
            }
        }
        // Return the accumulated errors
        if err.is_empty() { Ok(()) } else { Err(err) }
    }

    fn resolve_layout(&mut self, taipe: &context::Type<'a>, line_info: &impl HasLineInfo) -> CompileResult<Layout> {
        // (usize, usize) -> (size, alignment)
        // size (in bytes) -> always a multiple of alignment
        // alignment (in bytes) -> always a power of 2
        self.resolve_layout_impl(taipe, line_info.get_line_info())
    }

    fn resolve_layout_impl(&mut self, taipe: &context::Type<'a>, line_info: LineInfo) -> CompileResult<Layout> {
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
            context::Type::Const(taipe) => self.resolve_layout_impl(taipe, line_info)?,
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
                let Layout { size, alignment } = self.resolve_layout_impl(taipe, line_info)?;
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
                // Alignment: pointer_size
                Layout {
                    size: 2 * self.settings.pointer_size,
                    alignment: self.settings.pointer_size,
                }
            }
            context::Type::Tuple(items) => self.resolve_layout_tuple(items, line_info)?,
            context::Type::VarInt
            | context::Type::Module
            | context::Type::Typedef
            | context::Type::Void
            | context::Type::Noreturn => {
                return Err(self.make_err(
                    format!("type has no memory layout, problem type is '{}'", taipe),
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
            let layout = self.resolve_layout_impl(taipe, line_info)?;
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
            Payload::Function(_) | Payload::Block(_) => unreachable!("probably some analyzer bug"),
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
                let layout = self.resolve_layout_impl(&taipe, get_line_info_of_field(name));
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
        // Fix void assignment problem:
        if let Some((ref rhs, ref rhs_line_info)) = rhs
            && rhs.taipe.is_void()
        {
            return Err(self.make_err(
                format!("cannot assign value of type '{}'", rhs),
                rhs_line_info,
            ));
        }
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
                        format!("cannot assign to a constant of type: '{}'", lhs),
                        &lhs_line_info,
                    )
                    .chain(self.make_note(format!("type of value is '{}'", rhs), &rhs_line_info)));
            };
        }
        macro_rules! return_err {
            () => {
                return Err(self
                    .make_err(
                        format!("cannot assign value of type '{}'", rhs),
                        &rhs_line_info,
                    )
                    .chain(self.make_note(format!("cannot assign to '{}'", lhs), &lhs_line_info)));
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
            (_, context::Type::Void) => {
                // void type cannot be coerced to any type
                return_err!();
            }
            (context::Type::Noreturn, _) => {
                return Err(self.make_err(format!("cannot assign to: '{}'", lhs), &lhs_line_info));
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
                        scope.borrow().sym_path,
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
        if let Some(ctx) = self.resolve_name(&name.text, name.get_line_info(), &mut searched_names)? {
            Ok(ctx)
        } else {
            Err(self
                .make_err("undefined reference", name)
                .chain(self.make_did_you_mean_help(&name.text, &searched_names)))
        }
    }

    fn resolve_name(
        &mut self,
        name: &str,
        line_info: LineInfo,
        searched_names: &mut HashSet<String>,
    ) -> CompileResult<Option<Context<'a>>> {
        // Check in the current scope and go upwards
        let mut scope = Rc::clone(&self.cur_scope);
        let mut inner_fn: Option<Rc<RefCell<scope::Scope<'a>>>> = None;
        loop {
            match self.resolve_member(&scope, name, searched_names) {
                Ok(Some(ctx)) => {
                    if ctx.taipe.is_typedef() {
                        // Typedef is encoded by Type::Basic so ignore that case
                        return Ok(Some(ctx));
                    } else {
                        let context::Value::Reference(ref scope) = ctx.value else {
                            unreachable!("probably some bug in resolve_member");
                        };

                        if let Some(inner_fn) = inner_fn {
                            let scope = scope.borrow();
                            if scope.is_variable()
                                && let Some(outer_fn) = scope.get_enclosing_function()
                            {
                                return Err(self
                                    .make_err(
                                        "cannot use local variable of outer function from inner function context",
                                        &line_info,
                                    )
                                    .chain(self.make_note("variable is declared here", &scope))
                                    .chain(self.make_note("inner function is declared here", &inner_fn.borrow()))
                                    .chain(self.make_note("outer function is declared here", &outer_fn.borrow())));
                            }
                            drop(scope);
                        }
                        return Ok(Some(ctx));
                    }
                }
                Ok(None) => {}
                // It is referencing cyclic, probably user refers something
                // from the outer scope. Lets check that.
                Err(CompileError::SemCyclic {
                    file_path: _,
                    line_info: _,
                }) => {}
                Err(err) => return Err(err),
            }
            // If the current one is function then be aware of usage of local variables of outer
            // functions from inner function context
            if scope.borrow().is_function() {
                inner_fn = Some(Rc::clone(&scope));
            }
            let parent_opt = scope.borrow().parent.upgrade();
            if let Some(parent) = parent_opt.as_ref() {
                scope = Rc::clone(parent);
            } else {
                break;
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
                let opt = match lhs {
                    context::Type::VarInt => return Ok(rhs.clone()),
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

    fn make_note_no_path(&self, msg: impl ToString) -> CompileError {
        CompileError::SemNoteWithoutPath { msg: msg.to_string() }
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
        F: FnOnce(&scope::Function<'a>) -> T,
    {
        let function = self.get_current_function().expect("not in a function");
        let scope::Payload::Function(ref data) = function.borrow().payload else {
            unreachable!("probably some analyzer bug");
        };
        handler(data)
    }

    fn mut_current_function_data<F, T>(&self, handler: F) -> T
    where
        F: FnOnce(&mut scope::Function<'a>) -> T,
    {
        let function = self.get_current_function().expect("not in a function");
        let scope::Payload::Function(ref mut data) = function.borrow_mut().payload else {
            unreachable!("probably some analyzer bug");
        };
        handler(data)
    }

    fn get_current_block(&self) -> Option<Rc<RefCell<scope::Scope<'a>>>> {
        if self.cur_scope.borrow().is_block() {
            Some(Rc::clone(&self.cur_scope))
        } else {
            self.cur_scope.borrow().get_enclosing_block()
        }
    }

    fn use_current_block_data<F, T>(&self, handler: F) -> T
    where
        F: FnOnce(&scope::Block<'a>) -> T,
    {
        let block = self.get_current_block().expect("not in a block");
        let scope::Payload::Block(ref data) = block.borrow().payload else {
            unreachable!("probably some analyzer bug");
        };
        handler(data)
    }

    fn mut_current_block_data<F, T>(&self, handler: F) -> T
    where
        F: FnOnce(&mut scope::Block<'a>) -> T,
    {
        let block = self.get_current_block().expect("not in a block");
        let scope::Payload::Block(ref mut data) = block.borrow_mut().payload else {
            unreachable!("probably some analyzer bug");
        };
        handler(data)
    }
}
