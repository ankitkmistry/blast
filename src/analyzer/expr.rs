use std::{
    collections::HashSet,
    rc::Rc,
};

use indexmap::IndexMap;
use num_bigint::ToBigInt;

use super::Analyzer;
use crate::{
    ast,
    cfg::{ControlInfo, ControlNode},
    common::{CompileError, CompileResult, HasLineInfo, LineInfo, get_plural},
    context::{self, Context},
    lexer::{Token, TokenKind, TokenValue},
    scope::{self, HasSrcInfo},
};

impl<'a> Analyzer<'a> {
    pub(crate) fn visit_expr(&mut self, node: &'a ast::Expr) -> CompileResult<Context<'a>> {
        let ctx = self.visit_expr_impl(node)?;
        if let context::Value::Reference(ref scope) = ctx.value {
            // cfg: insert variable used node
            //      only if it is a local variable or constant
            let should_insert_cfg = match scope.borrow().kind {
                scope::ScopeKind::Variable => true,
                scope::ScopeKind::Const => true,
                _ => false,
            };
            if should_insert_cfg && self.get_current_block().is_some() && scope.borrow().get_enclosing_block().is_some()
            {
                self.mut_current_block_data(|data| {
                    let cf_node = data.cfg.insert_vertex(ControlNode::Info(ControlInfo::VarUsed {
                        line_info: node.get_line_info(),
                        scope: Rc::clone(scope),
                    }));
                    data.cfg.insert_edge(data.cf_last, cf_node);
                    data.cf_last = cf_node;
                });
            }
        }
        Ok(ctx)
    }
    fn visit_expr_lhs_of_assign(&mut self, node: &'a ast::Expr) -> CompileResult<Context<'a>> {
        let ctx = self.visit_expr_impl(node)?;
        if let context::Value::Reference(ref scope) = ctx.value {
            // cfg: insert variable assigned node
            //      only if it is a local variable or constant
            let should_insert_cfg = match scope.borrow().kind {
                scope::ScopeKind::Variable => true,
                scope::ScopeKind::Const => true,
                _ => false,
            };
            if should_insert_cfg && self.get_current_block().is_some() && scope.borrow().get_enclosing_block().is_some()
            {
                self.mut_current_block_data(|data| {
                    let cf_node = data.cfg.insert_vertex(ControlNode::Info(ControlInfo::VarAssigned {
                        line_info: node.get_line_info(),
                        scope: Rc::clone(scope),
                    }));
                    data.cfg.insert_edge(data.cf_last, cf_node);
                    data.cf_last = cf_node;
                });
            }
        }
        Ok(ctx)
    }
    fn visit_expr_impl(&mut self, node: &'a ast::Expr) -> CompileResult<Context<'a>> {
        match node {
            ast::Expr::Block { line_info, stmts } => self.visit_block(*line_info, stmts),
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
                let mut lhs_ctxes = Vec::new();
                let mut rhs_ctxes = Vec::new();
                for i in 0..rhses.len() {
                    let rhs_node = &rhses[i];
                    let rhs_line_info = rhs_node.get_line_info();
                    let rhs = self.visit_expr(rhs_node)?;
                    let lhs_node = &lhses[i];
                    let lhs_line_info = lhs_node.get_line_info();
                    let lhs = self.visit_expr_lhs_of_assign(lhs_node)?;
                    // do lvalue checking
                    if !lhs.is_lvalue {
                        return Err(self.make_err("cannot assign to a prvalue (pure rvalue)", &lhs_line_info));
                    }
                    lhs_ctxes.push(Context {
                        is_lvalue: lhs.is_lvalue,
                        taipe: lhs.taipe.clone(),
                        value: lhs.value,
                    });
                    let rhs_ctx =
                        self.resolve_assign(Some((lhs.taipe, lhs_line_info)), None, Some((rhs, rhs_line_info)))?;
                    rhs_ctxes.push(rhs_ctx);
                }
                Ok(Context {
                    is_lvalue: false,
                    taipe: context::Type::Void,
                    value: context::Value::Assign(lhs_ctxes, rhs_ctxes),
                })
            }
            ast::Expr::Binary { left, op, right } => self.visit_binary(left, op, right),
            ast::Expr::Cast { expr, taipe } => todo!("implement casting"),
            ast::Expr::Unary { op, expr } => self.visit_unary(op, expr),
            ast::Expr::Member { expr, name } => {
                let ctx = self.visit_expr(expr)?;
                let keep_lvalue = ctx.is_lvalue;
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
                        ctx.is_lvalue = keep_lvalue;
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
}
