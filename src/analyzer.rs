use std::{collections::{HashMap, HashSet}, fmt, sync::atomic::AtomicU64};

use bigdecimal::BigDecimal;
use log::debug;
use num_bigint::{BigInt, ToBigInt};
use num_traits::cast::ToPrimitive;
use std::str::FromStr;
use indexmap::IndexMap;

use crate::{
    ast,
    common::{fuzzy_search_best, get_plural, CompileError, CompileResult, HasLineInfo, Layout, LineInfo, Settings},
    lexer::{Token, TokenKind, TokenSuffix, TokenValue},
    scope::*,
    context::{self, Context},
    cfg::{ControlGraph, ControlInfo, ControlNode, ControlNodeId},
    errors,
};

// ------------------------------------------------------------
// Semantic Analysis code
// ------------------------------------------------------------

pub struct ScopePool {
    pool: IndexMap<ScopeId, Scope>,
}

impl ScopePool {
    pub fn new(pool: IndexMap<ScopeId, Scope>) -> Self {
        Self { pool }
    }

    pub fn get_scope(&self, scope_id: &ScopeId) -> &Scope {
        if let Some(scope) = self.pool.get(scope_id) {
            scope
        } else {
            panic!("invalid scope id")
        }
    }

    // pub fn get_scope_mut(&mut self, scope_id: &ScopeId) -> &Scope {
    //     if let Some(scope) = self.pool.get_mut(scope_id) {
    //         scope
    //     } else {
    //         panic!("invalid scope id")
    //     }
    // }
}

pub struct SemResult {
    pub scope_pool: ScopePool,
    pub roots: IndexMap<String, ScopeId>,
    pub warnings: CompileError,
}

#[derive(Clone, Copy)]
pub enum ScopeNode<'a> {
    Decl(&'a ast::Decl),
    Object(&'a ast::Object),
}

impl<'a> fmt::Debug for ScopeNode<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ScopeNode::Decl(_) => write!(f, "decl"),
            ScopeNode::Object(_) => write!(f, "object"),
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub enum ScopeEvalState<'a> {
    /// Scope is not visited yet
    NotVisited(ScopeNode<'a>),
    /// Visitation is in progress
    VisitInProgress,
    /// Scope has been visited
    Visited,    
}

pub struct Analyzer<'a> {
    scope_pool: IndexMap<ScopeId, Scope>,
    roots: IndexMap<String, ScopeId>,
    scope_eval_state_table: IndexMap<ScopeId, ScopeEvalState<'a>>,
    
    current_scope_stack: Vec<ScopeId>,

    /// The type that is used for '__int'
    type_int: context::Type,
    /// The type that is used for '__uint'
    type_uint: context::Type,
    /// The type that is used for '__size'
    type_isize: context::Type,
    /// The type that is used for '__usize'
    type_usize: context::Type,

    settings: Settings,
    saved_errors: CompileError,
    warnings: Vec<CompileError>,
}

impl<'a> Analyzer<'a> {
    pub fn new(settings: Settings, file_path: &str, name: &str, root: &'a ast::Object) -> Self {
        // Create the symbol path and id
        let mut sym_path = SymbolPath::new();
        sym_path.push_name(name);
        let id = ScopeId { index: 0, sym_path };
        // Create the root scope
        let scope = Scope {
            id: id.clone(),
            kind: ScopeKind::Module,
            file_path: Some(file_path.to_string()),
            name: name.to_string(),
            line_info: root.get_line_info(),
            payload: Payload::None,
            parent: None,
            children: IndexMap::new(),
            unique_counter: AtomicU64::new(0),
            block_counter: AtomicU64::new(0),
            loop_counter: AtomicU64::new(0),            
        };
        // Add to the scope pool
        let mut scope_pool = IndexMap::new();
        scope_pool.insert(id.clone(), scope);
        // Set eval state
        let mut scope_eval_state_table = IndexMap::new();
        scope_eval_state_table.insert(id.clone(), ScopeEvalState::NotVisited(ScopeNode::Object(root)));
        // Add to roots
        let mut roots = IndexMap::new();
        roots.insert(name.to_string(), id.clone());
        
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
            scope_pool,
            roots,
            scope_eval_state_table,
            current_scope_stack: vec![id],
            type_int,
            type_uint,
            type_isize,
            type_usize,
            settings,
            saved_errors: CompileError::new(),
            warnings: Vec::new()
        }
    }

    pub fn analyze(mut self) -> CompileResult<SemResult> {
        if let Err(err) = self.sem_analysis() {
            self.saved_errors.push_err(err);
            Err(self.saved_errors)
        } else if !self.saved_errors.is_empty() {
            Err(self.saved_errors)
        } else {
            Ok(SemResult {
                scope_pool: ScopePool::new(self.scope_pool),
                roots: self.roots,
                warnings: CompileError::Errors(self.warnings)
            })
        }
    }

    fn sem_analysis(&mut self) -> CompileResult<()> {
        // Get the top level declarations of every module
        let mut saved_errs = CompileError::new();
        let root_ids = self.roots.values().cloned().collect::<Vec<_>>();
        for root_id in root_ids {
            match self.get_scope_eval_state(&root_id) {
                ScopeEvalState::NotVisited(
                    ScopeNode::Object(
                        ast::Object::Module { line_info: _, decls }
                    )
                ) => {
                    self.push_current_scope(&root_id);
                    for decl in decls {
                        match self.declaration_first_stage(decl) {
                            Ok(()) => {},
                            Err(err) => saved_errs.push_err(err),
                        }
                    }
                    self.pop_current_scope();
                    self.set_scope_eval_state(&root_id, ScopeEvalState::Visited);
                }
                _ => unreachable!("not supposed to happen"),
            }
        }
        // Return errors if any
        if !saved_errs.is_empty() {
            return Err(saved_errs);
        }
        // Finally start the visitation of unfinished scopes
        loop {
            let unfinished_scopes = self.get_unfinished_scopes();
            if unfinished_scopes.is_empty() { break; }
            for scope_id in unfinished_scopes {
                match self.get_scope_eval_state(&scope_id) {
                    ScopeEvalState::NotVisited(scope_node) => match scope_node {
                        ScopeNode::Decl(decl) => {
                            self.push_current_scope(&self.get_scope(&scope_id).parent.clone().unwrap());
                            self.visit_decl(decl)?;
                            self.pop_current_scope();
                        },
                        ScopeNode::Object(_) => unreachable!("probably some analyzer bug"),
                    },
                    ScopeEvalState::VisitInProgress => {
                        unreachable!("probably some analyzer bug")
                    },
                    ScopeEvalState::Visited => {},
                }
            }
        }
        Ok(())
    }

    fn get_unfinished_scopes(&self) -> Vec<ScopeId> {
        let mut scope_ids = Vec::new();
        for (scope_id, state) in &self.scope_eval_state_table {
            match state {
                ScopeEvalState::NotVisited(_) => scope_ids.push(scope_id.clone()),
                ScopeEvalState::VisitInProgress => unreachable!("probably some analyzer bug"),
                ScopeEvalState::Visited => {},
            }
        }        
        scope_ids
    }

    // ------------------------------------------------------------
    // Declaration analysis
    // ------------------------------------------------------------

    // Declaration visit functions

    /// This function pre-declares all declarations (except declaration inside functions).
    /// This function also completes the visitation of modules (in the first stage).
    /// This function returns the scope IDs of all declarations that need to be visited in order
    /// in the next stage.
    /// The second stage of visitation will no longer bother with module declarations
    fn declaration_first_stage(&mut self, node: &'a ast::Decl) -> CompileResult<()> {
        let scope_id = self.pre_declare_decl(node)?;        
        match node {
            ast::Decl::Decl { name, taipe, eq_token, object } => {
                let Some(object) = object else { return Ok(()); };
                match object {
                    ast::Object::ExternModule { line_info: _, value } => todo!("external modules are not implemented yet"),
                    ast::Object::Module { line_info: _, decls } => {
                        // Check eq_token
                        let Some(eq_token) = eq_token else {
                            unreachable!("probably some parser bug");
                        };
                        if eq_token.kind!=TokenKind::Colon {
                            self.saved_errors.push_err(self.make_err("expected ':'",eq_token));
                        };
                        // Check if module is declared in the proper place
                        if self.get_current_function().is_some() {
                            return Err(self.make_err("module cannot be declared in a function", name));
                        }
                        if self.get_current_block().is_some() {
                            return Err(self.make_err("module cannot be declared in a block", name));
                        }
                        self.get_scope_mut(&scope_id).kind = ScopeKind::Module;
                        // Visit type
                        if let Some(taipe) = taipe {
                            return Err(errors![
                                self.make_err("modules do not have a type", taipe),
                                self.make_help("consider removing the type annotation"),
                            ]);
                        }
                        // Begin new scope
                        self.push_current_scope(&scope_id);
                        // Mark it evaluated if not already
                        if let ScopeEvalState::Visited = self.get_scope_eval_state(&scope_id) {
                        } else {
                            self.set_scope_eval_state(&scope_id, ScopeEvalState::Visited);
                        }
                        // Visit every decl
                        for decl in decls {
                            self.declaration_first_stage(decl)?;
                        }
                        // Restore old scope
                        self.pop_current_scope();
                        Ok(())
                    },
                    _ => Ok(()),
                }
            },
            ast::Decl::DeclWithDirective { name: _, taipe: _, eq_token: _, directive: _ } => Ok(()),
            ast::Decl::Using { line_info: _, items: _ } => Ok(()),
        }
    }
    
    fn visit_decl(&mut self, node: &'a ast::Decl) -> CompileResult<ScopeId> {
        macro_rules! colon_compulsory {
            ($token:expr) => {
                // Check the colon thing
                let Some(eq_token) = $token else {
                    unreachable!("probably some parser bug");
                };
                if eq_token.kind != TokenKind::Colon {
                    self.saved_errors.push_err(self.make_err("expected ':'", eq_token));
                }
            };
        }

        match node {
            ast::Decl::Decl { name, taipe, eq_token, object } => {
                let scope_id = if self.get_current_block().is_some() {
                    if let Some(object) = object {
                        self.declare_sym_with_value(node, &name, object)?
                    } else {
                        self.declare_sym(node, &name)?
                    }
                } else {
                    if let Some(child) = self.get_current_scope().children.get(&name.text) {
                        child.clone()
                    } else {
                        if let Some(object) = object {
                            self.declare_sym_with_value(node, &name, object)?
                        } else {
                            self.declare_sym(node, &name)?
                        }
                    }
                };
                // Set in progress
                match self.get_scope_eval_state(&scope_id) {
                    ScopeEvalState::NotVisited(_) => {
                        self.set_scope_eval_state(&scope_id, ScopeEvalState::VisitInProgress);
                    }
                    ScopeEvalState::VisitInProgress => unreachable!("probably some analyzer bug"),
                    ScopeEvalState::Visited => {
                        dbg!(scope_id);
                        unreachable!("probably some analyzer bug");
                    },
                };
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
                    self.get_scope_mut(&scope_id).kind = if ctx.taipe.is_typedef() {
                        ScopeKind::Typedef
                    } else if ctx.taipe.is_const() {
                        ScopeKind::Const
                    } else {
                        ScopeKind::Variable
                    };
                    // Set the context
                    self.get_scope_mut(&scope_id).payload = if ctx.taipe.is_typedef() {
                        Payload::Typedef(ctx.taipe)
                    } else if self.get_current_function().is_none() {
                        Payload::Global(GlobalInfo { ctx: ctx })
                    } else {
                        // TODO: record the assigment in code context of the block
                        Payload::Local(LocalInfo { taipe: ctx.taipe })
                    };

                    // cfg: insert variable declared node
                    //      only if it is a local variable or constant
                    let should_insert_cfg = match self.get_scope(&scope_id).kind {
                        ScopeKind::Variable => true,
                        ScopeKind::Const => true,
                        _ => false,
                    };
                    if should_insert_cfg && self.get_current_block().is_some() {
                        self.mut_current_block_data(|data| {
                            let cf_declare = data.cfg.insert_vertex(ControlNode::Info(ControlInfo::VarDeclared {
                                scope_id: scope_id.clone(),
                            }));
                            data.cfg.insert_edge(data.cf_last, cf_declare);
                            data.cf_last = cf_declare;
                        });
                    }

                    self.set_scope_eval_state(&scope_id, ScopeEvalState::Visited);
                    return Ok(scope_id);
                };
                match object {
                    ast::Object::ExternModule { line_info: _, value: _ }
                    | ast::Object::Module { line_info: _, decls: _ } => {
                        unreachable!("not supposed to come here as module is already visited")
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
                        self.get_scope_mut(&scope_id).kind = ScopeKind::Compound;
                        // Visit type
                        if let Some(taipe) = taipe {
                            let taipe = self.visit_type(taipe)?;
                            let context::Type::Typedef = taipe else {
                                return Err(self.make_err("expected 'typedef'", node));
                            };
                        }
                        self.visit_compound(scope_id, field)
                    }
                    ast::Object::Fun {
                        line_info,
                        params,
                        ret,
                        body,
                    } => {
                        colon_compulsory!(eq_token);
                        self.get_scope_mut(&scope_id).kind = ScopeKind::Function;
                        // Visit type
                        let lhs = if let Some(taipe) = taipe {
                            Some((self.visit_type(taipe)?, taipe.get_line_info()))
                        } else {
                            None
                        };
                        // --- FUNCTION CODE START
                        // Begin new scope
                        self.push_current_scope(&scope_id);
                        // Parameter visitation
                        // INFO: Parameters are iterated twice. In the first iteration we visit
                        // the ast nodes and take the useful information (name and Context).
                        // This prevents default value of a param to refer to its previous
                        // param. The second time we declare the parameter inside the function
                        // scope, once and for all.
                        let mut param_infos = Vec::new();
                        let mut prev_default_param = None;
                        let mut default_param_count = 0usize;
                        for param in params {
                            // Check type
                            let lhs = self.visit_type(&param.taipe)?;
                            let lhs_line_info = param.taipe.get_line_info();
                            let ctx = if let Some(expr) = &param.expr {
                                // Set this as previous default parameter
                                default_param_count += 1;
                                prev_default_param = Some(param.get_line_info());
                                let Some(ref eq_token) = param.eq_token else {
                                    unreachable!("probably some parser bug");
                                };
                                // Check default value
                                let rhs = self.visit_expr(expr)?;
                                let rhs_line_info = expr.get_line_info();
                                self.resolve_assign(Some((lhs, lhs_line_info)), Some(eq_token), Some((rhs, rhs_line_info)))?
                            } else {
                                // Non default parameter are not allowed after default parameter
                                if let Some(ref prev_default_param) = prev_default_param {
                                    return Err(errors![
                                        self.make_err("non-default parameter is not allowed here", param),
                                        self.make_note("previous default parameter is here", prev_default_param)
                                    ]);
                                }
                                self.resolve_assign(Some((lhs, lhs_line_info)), None, None)?
                            };
                            param_infos.push((
                                &param.name,
                                ParamInfo {
                                    taipe: ctx.taipe,
                                    default: Some(ctx.value),
                                    line_info: param.get_line_info(),
                                },
                            ));
                        }
                        // Now create the param scopes
                        let mut param_table = IndexMap::new();
                        let mut param_types = Vec::new();
                        for (name, param) in param_infos {
                            // Prepare param_types for creating function type
                            param_types.push(context::Param {
                                taipe: param.taipe.clone(),
                            });
                            // Generate the param name in the current scope
                            let param_scope_id = self.declare_param(param, ScopeEvalState::Visited, name)?;
                            param_table.insert(name.text.clone(), param_scope_id);
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
                        let taipe = context::Type::Function {
                            ret: Box::new(ret_type.clone()),
                            params: param_types,
                        };
                        let rhs = Context {
                            is_lvalue: true,
                            taipe: taipe.clone(),
                            value: context::Value::from_nil(),
                        };
                        // Resolve assignment
                        self.resolve_assign(lhs, eq_token.as_ref(), Some((rhs, *line_info)))?;
                        // Mark it visited
                        self.set_scope_eval_state(&scope_id, ScopeEvalState::Visited);
                        self.get_scope_mut(&scope_id).payload = Payload::Function(FunctionInfo {
                            taipe,
                            ctx: None,
                            param_table,
                            default_param_count,
                            loop_stack: IndexMap::new(),
                            ret_line_info: ret.as_ref().map(|ret| ret.get_line_info()),
                        });
                        if let Some(body) = body {
                            let mut ctx = self.visit_stmt(body)?;
                            // Check the return type
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
                                    self.get_scope(&scope_id),
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
                                    .unwrap_or_else(|| self.get_scope(&scope_id).get_line_info());
                                let rhs = ctx;
                                let rhs_line_info = body.get_line_info();
                                ctx = self.resolve_assign(Some((lhs, lhs_line_info)), None, Some((rhs, rhs_line_info)))?;
                            }
                            // Set the function body
                            let Payload::Function(ref mut info) = self.get_scope_mut(&scope_id).payload else {
                                unreachable!("not supposed to happen");
                            };
                            info.ctx = Some(ctx);
                        }
                        // Restore old scope
                        self.pop_current_scope();
                        Ok(scope_id)
                        // --- FUNCTION CODE END
                    }
                    ast::Object::Typedef(node) => {
                        colon_compulsory!(eq_token);
                        // Accumulate errors
                        let mut errs = CompileError::new();
                        self.get_scope_mut(&scope_id).kind = ScopeKind::Typedef;
                        // Visit lhs type
                        if let Some(taipe) = taipe {
                            match self.visit_type(taipe) {
                                Ok(taipe) => {
                                    if let context::Type::Typedef = taipe {} else {
                                        errs.push_err(self.make_err("expected 'typedef'", node));
                                    };
                                },
                                Err(err) => errs.push_err(err),
                            };
                        }
                        // Visit rhs type
                        let taipe = match self.visit_type(node) {
                            Ok(taipe) => {
                                if let context::Type::Typedef = &taipe {
                                    // context: type -> typedef, value -> typedef
                                    // this cannot happen, there is no type of a type
                                    // parser prevents this
                                    errs.push_err(self.make_err("invalid type alias", node));
                                }
                                if !errs.is_empty() { return Err(errs); }
                                taipe
                            },
                            Err(err) => {
                                errs.push_err(err);
                                return Err(errs);
                            },
                        };
                        // Complete the visit
                        self.get_scope_mut(&scope_id).payload = Payload::Typedef(taipe);
                        self.set_scope_eval_state(&scope_id, ScopeEvalState::Visited);
                        Ok(scope_id)
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
                        let mut is_global = false;
                        if self.get_current_function().is_none() {
                            rhs = self.compeval_trivial(&rhs)?;
                            is_global = true;
                        }
                        let ctx = self.resolve_assign(lhs, eq_token.as_ref(), Some((rhs, expr.get_line_info())))?;
                        // Complete the visit
                        if ctx.taipe.is_typedef() {
                            self.get_scope_mut(&scope_id).kind = ScopeKind::Typedef;
                        } else if ctx.taipe.is_const() {
                            self.get_scope_mut(&scope_id).kind = ScopeKind::Const;
                        } else {
                            self.get_scope_mut(&scope_id).kind = ScopeKind::Variable;
                        }
                        // Set the context
                        self.get_scope_mut(&scope_id).payload = if ctx.taipe.is_typedef() {
                            Payload::Typedef(ctx.taipe)
                        } else if is_global {
                            Payload::Global(GlobalInfo { ctx: ctx })
                        } else {
                            // TODO: record the assigment in code context of the block
                            Payload::Local(LocalInfo { taipe: ctx.taipe })
                        };

                        // cfg: insert variable declared node
                        //      only if it is a local variable or constant
                        let should_insert_cfg = match self.get_scope(&scope_id).kind {
                            ScopeKind::Variable => true,
                            ScopeKind::Const => true,
                            _ => false,
                        };
                        if should_insert_cfg && self.get_current_block().is_some() {
                            self.mut_current_block_data(|data| {
                                let cf_declare = data.cfg.insert_vertex(ControlNode::Info(ControlInfo::VarDeclared {
                                    scope_id: scope_id.clone(),
                                }));
                                let cf_assign = data.cfg.insert_vertex(ControlNode::Info(ControlInfo::VarAssigned {
                                    line_info: node.get_line_info(),
                                    scope_id: scope_id.clone(),
                                }));
                                data.cfg.insert_edge(data.cf_last, cf_declare);
                                data.cfg.insert_edge(cf_declare, cf_assign);
                                data.cf_last = cf_assign;
                            });
                        }
                        self.set_scope_eval_state(&scope_id, ScopeEvalState::Visited);
                        Ok(scope_id)
                    }
                }
            }
            ast::Decl::DeclWithDirective { name, taipe, eq_token, directive } => {
                fn is_directive_allowed(taipe: &context::Type) -> bool {
                    match taipe {
                        context::Type::Const(taipe) => is_directive_allowed(taipe),
                        context::Type::Module
                            | context::Type::Typedef
                            | context::Type::Void
                            | context::Type::Noreturn => false,
                        _ => true,
                    }
                }

                let scope_id = if self.get_current_block().is_some() {
                    self.declare_sym(node, &name)?
                } else {
                    if let Some(child_id) = self.get_current_scope().children.get(&name.text) {
                        child_id.clone()
                    } else {
                        self.declare_sym(node, &name)?
                    }
                };
                // Set in progress
                match self.get_scope_eval_state(&scope_id) {
                    ScopeEvalState::NotVisited(_) => {
                        self.set_scope_eval_state(&scope_id, ScopeEvalState::VisitInProgress);
                    }
                    ScopeEvalState::VisitInProgress => unreachable!("probably some analyzer bug"),
                    ScopeEvalState::Visited => {
                        if !self.get_scope(&scope_id).is_module() {
                            return Ok(scope_id);
                        }
                    }
                }
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
                        cfg_assign = true;
                        self.get_default_value(&lhs, taipe)?
                    }
                    _ => unreachable!("probably some parser bug"),
                };
                // Complete the visit
                if ctx.taipe.is_typedef() {
                    self.get_scope_mut(&scope_id).kind = ScopeKind::Typedef;
                } else if ctx.taipe.is_const() {
                    self.get_scope_mut(&scope_id).kind = ScopeKind::Const;
                } else {
                    self.get_scope_mut(&scope_id).kind = ScopeKind::Variable;
                }
                // Set the context
                self.get_scope_mut(&scope_id).payload = if ctx.taipe.is_typedef() {
                    Payload::Typedef(ctx.taipe)
                } else if self.get_current_function().is_none() {
                    Payload::Global(GlobalInfo { ctx: ctx })
                } else {
                    // TODO: record the assigment in code context of the block
                    Payload::Local(LocalInfo { taipe: ctx.taipe })
                };

                if self.get_current_block().is_some() {
                    // cfg: insert variable declared node
                    self.mut_current_block_data(|data| {
                        let cf_declare = data.cfg.insert_vertex(ControlNode::Info(ControlInfo::VarDeclared {
                            scope_id: scope_id.clone(),
                        }));
                        data.cfg.insert_edge(data.cf_last, cf_declare);
                        data.cf_last = cf_declare;
                    });
                    // cfg: insert variable assigned node
                    if cfg_assign {
                        self.mut_current_block_data(|data| {
                            let cf_assign = data.cfg.insert_vertex(ControlNode::Info(ControlInfo::VarAssigned {
                                line_info: node.get_line_info(),
                                scope_id: scope_id.clone(),
                            }));
                            data.cfg.insert_edge(data.cf_last, cf_assign);
                            data.cf_last = cf_assign;
                        });
                    }
                }

                self.set_scope_eval_state(&scope_id, ScopeEvalState::Visited);
                Ok(scope_id)
            },
            ast::Decl::Using { line_info, items } => todo!("import statements are not supported yet"),
        }
    }

    fn visit_compound(
        &mut self,
        scope_id: ScopeId,
        field: &'a ast::Field,
    ) -> CompileResult<ScopeId> {
        // Begin new scope
        self.push_current_scope(&scope_id);
        // Mark it evaluated
        self.set_scope_eval_state(&scope_id, ScopeEvalState::Visited);
        // Visit every field
        let field = self.get_fields(field)?;
        // Set the payload
        self.get_scope_mut(&scope_id).payload = Payload::Compound(CompoundInfo::new(field));
        // Eval the layout
        let layout = self.resolve_layout_scope(&scope_id)?;
        // Print the layout
        {
            let scope = self.get_scope(&scope_id);
            debug!("Memory layout of {}: {:?}", scope.id.sym_path, layout);
            let Payload::Compound(ref compound) = scope.payload else {
                unreachable!("not supposed to happen")
            };
            let mut fields = compound.field_data_table.iter().collect::<Vec<_>>();
            fields.sort_by_key(|&(_, data)| data.offset);
            for (name, field_data) in fields {
                debug!(
                    "  field '{}' = offset: {}, size: {}, alignment: {}",
                    name,
                    field_data.offset, field_data.size, field_data.alignment,
                );
            }
            debug!("");
        }
        // Restore old scope
        self.pop_current_scope();
        Ok(scope_id)
    }
    
    fn get_fields(&mut self, field: &'a ast::Field) -> CompileResult<FieldInfo> {
        self.get_fields_impl(field, false)
    }

    fn get_fields_impl(&mut self, field: &'a ast::Field, is_alone: bool) -> CompileResult<FieldInfo> {
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
                    TokenKind::Struct => Ok(FieldInfo::Struct(vec)),
                    TokenKind::Union => Ok(FieldInfo::Union(vec)),
                    _ => unreachable!("probably some parser bug"),
                }
            }
            ast::Field::Decl {
                name,
                taipe,
                eq_token,
                expr,
            } => {
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
                            return Err(errors![
                                self.make_err("inference is ambiguous, encountered cyclic references", name),
                                self.make_note_with_path("another one declared here", file_path, &line_info)
                            ]);
                        }
                        Err(err) => return Err(err),
                    };
                    let rhs = self.compeval_trivial(&rhs)?;
                    // Resolve assignment
                    self.resolve_assign(Some(lhs), eq_token.as_ref(), Some((rhs, expr.get_line_info())))?
                } else {
                    // Situation
                    // ---------------------------------
                    // name : type;
                    // ---------------------------------
                    assert!(eq_token.is_none());
                    // If no value is provided then default value should be evaluated
                    let rhs = (self.get_default_value(&lhs.0, taipe)?, name.get_line_info());
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
                Ok(FieldInfo::Field {
                    file_path: self.get_current_src_path(),
                    line_info: name.get_line_info(),
                    name: name.text.clone(),
                    taipe: field_type,
                })
            }
        }
    }

    // Declaration helpers

    /// This function declares all the symbols in `decls` without visiting them.
    /// So that symbols that are declared later are also accessible before they
    /// are introduced.
    fn pre_declare_decls(&mut self, decls: &'a [ast::Decl]) -> CompileResult<()> {
        // Accumalate the errors.
        let mut saved_err = CompileError::new();
        for decl in decls {
            if let Err(err) = self.pre_declare_decl(decl) {
                saved_err.push_err(err);
            }
        }
        // Return success (or errors if any)
        if saved_err.is_empty() {
            Ok(())
        } else {
            Err(saved_err)
        }
    }

    fn pre_declare_decl(&mut self, decl: &'a ast::Decl) -> CompileResult<ScopeId> {
        match decl {
            ast::Decl::Decl { name, taipe: _, eq_token: _, object } => {
                if let Some(object) = object {
                    self.declare_sym_with_value(decl, &name, object)
                } else {
                    self.declare_sym(decl, &name)
                }
            },
            ast::Decl::DeclWithDirective { name, taipe, eq_token, directive } => {
                self.declare_sym(decl, &name)
            },
            ast::Decl::Using { line_info, items } => todo!("import statements are not yet supported"),
        }
    }

    fn declare_sym(&mut self, node: &'a ast::Decl, name: &Token) -> CompileResult<ScopeId> {
        // Check for redeclaration
        // '_' declarations are given unique names
        if name.kind != TokenKind::Underscore 
            && let Some(prev_scope_id) = self.get_current_scope().children.get(&name.text)
        {
            return Err(errors![
                self.make_err("redeclaration of symbol", name),
                self.make_note("already declared here", self.get_scope(prev_scope_id))
            ]);
        }
        
        let sym_name = if name.kind == TokenKind::Underscore {
            format!(
                "unnamed{}$",
                self.get_current_scope()
                    .unique_counter
                    .fetch_add(1, std::sync::atomic::Ordering::SeqCst)
            )
        } else {
            name.text.clone()
        };

        Ok(self.add_child_scope(
            &self.get_current_scope_id().clone(),
            ScopeKind::None,
            &sym_name,
            ScopeEvalState::NotVisited(ScopeNode::Decl(node)),
            Payload::None,
            name,
        ))
    }
    
    fn declare_sym_with_value(
        &mut self,
        node: &'a ast::Decl,
        name: &Token,
        object: &'a ast::Object,
    ) -> CompileResult<ScopeId> {
        // Check for redeclaration
        // Except for '_' declarations
        if name.kind != TokenKind::Underscore
            && let Some(prev_scope_id) = self.get_current_scope().children.get(&name.text)
        {
            let prev_scope = self.get_scope(&prev_scope_id);
            if object.is_module() {
                let prev_scope_state = self.get_scope_eval_state(&prev_scope_id);
                // Allow merging module declarations
                if prev_scope.is_module()
                    && let ScopeEvalState::Visited = prev_scope_state {
                        return Ok(prev_scope_id.clone());
                    }
                if let ScopeEvalState::NotVisited(prev_decl) = prev_scope_state
                    && let ScopeNode::Decl(prev_decl) = prev_decl
                    && let ast::Decl::Decl {
                        name: _,
                        taipe: _,
                        eq_token: _,
                        object: prev_object,
                    } = prev_decl
                    && let Some(prev_object) = prev_object
                    && prev_object.is_module()
                {
                    return Ok(prev_scope_id.clone());
                }
            }
            // No module then error
            return Err(errors![
                self.make_err("redeclaration of symbol", name),
                self.make_note("already declared here", prev_scope)
            ]);
        }

        let sym_name = if name.kind == TokenKind::Underscore {
            format!(
                "unnamed{}$",
                self.get_current_scope()
                    .unique_counter
                    .fetch_add(1, std::sync::atomic::Ordering::SeqCst)
            )
        } else {
            name.text.clone()
        };

        Ok(self.add_child_scope(
            &self.get_current_scope_id().clone(),
            ScopeKind::None,
            &sym_name,
            ScopeEvalState::NotVisited(ScopeNode::Decl(node)),
            Payload::None,
            name,
        ))
    }

    fn declare_param(&mut self, param_info: ParamInfo, state: ScopeEvalState<'a>, name: &Token) -> CompileResult<ScopeId> {
        // Check for redeclaration
        // Except for '_' declarations
        if name.kind != TokenKind::Underscore
            && let Some(prev_scope_id) = self.get_current_scope().children.get(&name.text)
        {
            // No module then error
            return Err(errors![
                self.make_err("redeclaration of symbol", name),
                self.make_note("already declared here", self.get_scope(prev_scope_id))
            ]);
        }

        let sym_name = if name.kind == TokenKind::Underscore {
            format!(
                "unnamed{}$",
                self.get_current_scope()
                    .unique_counter
                    .fetch_add(1, std::sync::atomic::Ordering::SeqCst)
            )
        } else {
            name.text.clone()
        };

        Ok(self.add_child_scope(
            &self.get_current_scope_id().clone(),
            ScopeKind::Param,
            &sym_name,
            state,
            Payload::Param(param_info),
            name,
        ))
    }

    // Layout resolution

    fn resolve_layout(&mut self, taipe: &context::Type, line_info: &impl HasLineInfo) -> CompileResult<Layout> {
        // (usize, usize) -> (size, alignment)
        // size (in bytes) -> always a multiple of alignment
        // alignment (in bytes) -> always a power of 2
        self.resolve_layout_impl(taipe, line_info.get_line_info())
    }

    fn resolve_layout_impl(&mut self, taipe: &context::Type, line_info: LineInfo) -> CompileResult<Layout> {
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
            context::Type::Basic(scope_id) => self.resolve_layout_scope(scope_id)?,
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

    fn resolve_layout_tuple(&mut self, types: &[context::Type], line_info: LineInfo) -> CompileResult<Layout> {
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

    fn resolve_layout_scope(&mut self, scope_id: &ScopeId) -> CompileResult<Layout> {
        let compound = match &self.get_scope(scope_id).payload {
            Payload::Compound(compound) => compound.clone(),
            Payload::LayoutResolutionInProgress | Payload::None => {
                return Err(CompileError::SemCyclic {
                    file_path: self.get_src_path_of_scope(&scope_id),
                    line_info: self.get_scope(&scope_id).get_line_info(),
                });
            }
            _ => unreachable!("probably some analyzer bug"),
        };

        self.get_scope_mut(scope_id).payload = Payload::LayoutResolutionInProgress;
        let mut offsets = HashMap::<String, FieldData>::new();
        // Resolve layout info for the struct or union or field
        let layout_result = self.resolve_layout_field(&compound.field, 0, &mut offsets, &compound.field);
        let layout = match layout_result {
            Ok(layout) => layout,
            Err(CompileError::SemCyclic { file_path, line_info }) => {
                return Err(errors![
                    self.make_err(
                        "memory layout is ambiguous, encountered cyclic references",
                        self.get_scope(&scope_id),
                    ),
                    self.make_note_with_path("cycle occurs here", file_path, &line_info)
                ]);
            }
            Err(err) => return Err(err),
        };
        // Reset the payload
        self.get_scope_mut(scope_id).payload = Payload::Compound(CompoundInfo {
            field: compound.field,
            layout,
            field_data_table: offsets,
        });
        Ok(layout)
    }

    fn resolve_layout_field(
        &mut self,
        field: &FieldInfo,
        mut cur_offset: usize,
        offset_table: &mut HashMap<String, FieldData>,
        top_field: &FieldInfo,
    ) -> CompileResult<Layout> {
        fn eval_padding(offset: usize, alignment: usize) -> usize {
            // Calculate the misalignment
            let misalignment = offset % alignment;
            // Add the padding
            let padding = if misalignment > 0 { alignment - misalignment } else { 0 };
            padding
        }

        match field {
            FieldInfo::Struct(fields) => {
                let mut struct_alignment = 1usize;
                let offset_start = cur_offset;
                for field in fields {
                    // Set the offset of field
                    let layout = self.resolve_layout_field(field, cur_offset, offset_table, top_field)?;
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
            FieldInfo::Union(fields) => {
                let mut union_alignment = 1usize;
                let mut union_size = 0usize;
                // Calculate
                for field in fields.iter() {
                    // Set the offset of field
                    let layout = self.resolve_layout_field(field, cur_offset, offset_table, top_field)?;
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
            FieldInfo::Field {
                file_path,
                line_info,
                name,
                taipe,
            } => {
                let layout = self.resolve_layout_impl(
                    &taipe,
                    top_field.get_line_info_of(name).expect("probably some analyzer bug")
                );
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
                    FieldData {
                        name: name.clone(),
                        taipe: taipe.clone(),
                        file_path: file_path.clone(),
                        line_info: *line_info,
                        offset: cur_offset,
                        size: layout.size,
                        alignment: layout.alignment,
                    },
                );
                Ok(layout)
            }
        }
    }

    // ------------------------------------------------------------
    // Statement analysis
    // ------------------------------------------------------------
    fn visit_stmt(&mut self, node: &'a ast::Stmt) -> CompileResult<Context> {
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
                let _ = self.visit_decl(decl)?;
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

    fn visit_return(&mut self, token: &Token, expr: Option<&'a ast::Expr>) -> CompileResult<Context> {
        let Some(function) = self.get_current_function() else {
            return Err(self.make_err("'return' is allowed in functions only", token));
        };
        // Get the return type and line_info of the return type of the function
        let Payload::Function(ref fun_data) = function.payload else {
            unreachable!("probably some analyzer bug");
        };
        let ret_line_info = fun_data.ret_line_info
            .unwrap_or_else(|| function.get_line_info());
        let ret = fun_data.get_return_type().clone();
        // Cannot return from a noreturn function
        if ret.is_noreturn() {
            return Err(self.make_err(
                format!(
                    "cannot return from a '{}' function",
                    context::Type::Noreturn
                ),
                token,
            ));
        }
        // Check return
        if let Some(expr) = expr {
            if ret.is_void() {
                return Err(errors![
                    self.make_err("invalid expression", expr),
                    self.make_note(
                        format!("function expects return type '{}'", ret),
                        &ret_line_info,
                    ),
                ]);
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
                return Err(errors![
                    self.make_err("expected <expression> for 'return'", token),
                    self.make_note(
                        format!("function expects return type '{}'", ret),
                        &ret_line_info,
                    ),
                ]);
            }
            Ok(Context {
                is_lvalue: false,
                taipe: context::Type::Noreturn,
                value: context::Value::RetVoid,
            })
        }
    }

    fn visit_break(&mut self, token: &Token, label: Option<&Token>) -> CompileResult<Context> {
        let function = self.get_current_function().expect("not in a function");
        let Payload::Function(ref data) = function.payload else {
            unreachable!("probably some analyzer bug");
        };
        let cf_break = if let Some(label) = label {
            if let Some(loop_info) = data.loop_stack.get(&label.text) {
                loop_info.cf_break
            } else {
                let mut searched_names = HashSet::new();
                for (name, _) in &data.loop_stack {
                    searched_names.insert(name.clone());
                }
                return Err(errors![
                    self.make_err(format!("undefined loop label '{}'", label.text), label),
                    self.make_did_you_mean_help(&label.text, &searched_names)
                ]);
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
    }

    fn visit_continue(&mut self, token: &Token, label: Option<&Token>) -> CompileResult<Context> {
        let function = self.get_current_function().expect("not in a function");
        let Payload::Function(ref data) = function.payload else {
            unreachable!("probably some analyzer bug");
        };
        let cf_continue = if let Some(label) = label {
            if let Some(loop_info) = data.loop_stack.get(&label.text) {
                loop_info.cf_continue
            } else {
                let mut searched_names = HashSet::new();
                for (name, _) in &data.loop_stack {
                    searched_names.insert(name.clone());
                }
                return Err(errors![
                    self.make_err(format!("undefined loop label '{}'", label.text), label),
                    self.make_did_you_mean_help(&label.text, &searched_names)
                ]);
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
    }

    fn visit_while_stmt(
        &mut self,
        label: Option<&Token>,
        expr: &'a ast::Expr,
        then_body: &'a ast::Stmt,
        line_info: LineInfo,
    ) -> Result<Context, CompileError> {
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

        let loop_name = if let Some(label) = label {
            label.text.clone()
        } else {
            format!(
                "loop{}$",
                self.get_current_scope()
                    .loop_counter
                    .fetch_add(1, std::sync::atomic::Ordering::SeqCst)
            )
        };
        let loop_info = LoopInfo { cf_break, cf_continue };

        let function = self.get_current_function_mut().expect("not in a function");
        let Payload::Function(ref mut data) = function.payload else {
            unreachable!("probably some analyzer bug");
        };
        if let Some(label) = label {
            data.loop_stack.insert(label.text.clone(), loop_info);
        } else {
            data.loop_stack.insert(loop_name, loop_info);
        }
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
    ) -> Result<Context, CompileError> {
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

        let then_body_ctx = self.visit_stmt(then_body)?;

        // cfg: Get the then branch flow
        let cf_then = self.use_current_block_data(|data| data.cf_last);

        if let Some(else_body) = else_body {
            // cfg: Let the flow before else branch descend from cf_cond
            self.mut_current_block_data(|data| {
                data.cf_last = cf_cond;
            });

            let else_body_ctx = self.visit_stmt(else_body)?;

            // cfg: Get the else branch flow
            let cf_else = self.use_current_block_data(|data| data.cf_last);

            // cfg: Stitch them together
            self.mut_current_block_data(|data| {
                let cf_join = data.cfg.insert_vertex(ControlNode::Junction);
                data.cfg.insert_edge(cf_then, cf_join);
                data.cfg.insert_edge(cf_else, cf_join);
                data.cf_last = cf_join;
            });

            if then_body_ctx.taipe.is_noreturn() {
                Ok(Context {
                    is_lvalue: else_body_ctx.is_lvalue,
                    taipe: else_body_ctx.taipe.clone(),
                    value: context::Value::IfElse {
                        line_info,
                        cond: Box::new(cond),
                        then_ctx: Box::new(then_body_ctx),
                        else_ctx: Box::new(else_body_ctx),
                    },
                })
            } else if else_body_ctx.taipe.is_noreturn() {
                Ok(Context {
                    is_lvalue: then_body_ctx.is_lvalue,
                    taipe: then_body_ctx.taipe.clone(),
                    value: context::Value::IfElse {
                        line_info,
                        cond: Box::new(cond),
                        then_ctx: Box::new(then_body_ctx),
                        else_ctx: Box::new(else_body_ctx),
                    },
                })
            } else if then_body_ctx.taipe == else_body_ctx.taipe {
                // TODO: allow mixing of compatible values
                Ok(Context {
                    is_lvalue: then_body_ctx.is_lvalue && else_body_ctx.is_lvalue,
                    taipe: then_body_ctx.taipe.clone(),
                    value: context::Value::IfElse {
                        line_info,
                        cond: Box::new(cond),
                        then_ctx: Box::new(then_body_ctx),
                        else_ctx: Box::new(else_body_ctx),
                    },
                })
            } else {
                return Err(errors![
                    self.make_err(format!("expected '{}' but got '{}'", then_body_ctx, else_body_ctx), &else_body.get_line_info()),
                    self.make_note(format!("then body of if statement returns a different type"), &then_body.get_line_info())
                ]);
            }
        } else {
            // cfg: Stitch them together
            self.mut_current_block_data(|data| {
                let cf_join = data.cfg.insert_vertex(ControlNode::Junction);
                data.cfg.insert_edge(cf_then, cf_join);
                data.cfg.insert_edge(cf_cond, cf_join);
                data.cf_last = cf_join;
            });

            if then_body_ctx.taipe.is_void() || then_body_ctx.taipe.is_noreturn() {
                Ok(Context {
                    is_lvalue: false,
                    taipe: context::Type::Void,
                    value: context::Value::IfElse {
                        line_info,
                        cond: Box::new(cond),
                        then_ctx: Box::new(then_body_ctx),
                        else_ctx: Box::new(Context::from_void()),
                    },
                })
            } else {
                Err(self.make_err(format!("expected '{}' but got '{}'", context::Type::Void, then_body_ctx), then_body))
            }
        }
    }

    fn create_block_scope(&mut self, line_info: LineInfo) -> ScopeId {
        // Generate unique block name
        let block_name = format!(
            "block{}$",
            self.get_current_scope()
                .block_counter
                .fetch_add(1, std::sync::atomic::Ordering::SeqCst)
        );
        // Create its own control graph
        let mut cfg = ControlGraph::new();
        let cf_start = cfg.insert_vertex(ControlNode::Start);
        let cf_unreachable = cfg.insert_vertex(ControlNode::Unreachable);
        let cf_end = cfg.insert_vertex(ControlNode::End);
        // Create a block scope
        let scope_id = self.add_child_scope(
            &self.get_current_scope_id().clone(),
            ScopeKind::Block,
            &block_name,
            ScopeEvalState::VisitInProgress,
            Payload::Block(BlockInfo {
                cfg,
                cf_start,
                cf_end,
                cf_last: cf_start,
                cf_unreachable,
            }),
            &line_info
        );
        scope_id
    }

    fn visit_block(&mut self, line_info: LineInfo, stmts: &'a [ast::Stmt]) -> CompileResult<Context> {
        let scope_id = self.create_block_scope(line_info);
        // Begin new scope
        self.push_current_scope(&scope_id);
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
            // before pushing just change ctx
            if let context::Value::Eval(ctx) = ctx.value {
                items.push(*ctx);
            } else {
                items.push(ctx);
            }
            last_stmt_index = i + 1;
            if block_ret_type.is_noreturn() {
                break;
            }
            if block_ret_type.is_void() {
                continue;
            }
            break;
        }
        if block_ret_type.is_void() {
            items.push(Context::from_void());
        }
        // For better error output change the line info of the block scope
        if !stmts.is_empty() {
            self.get_scope_mut(&scope_id).line_info = stmts[last_stmt_index - 1].get_line_info();
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
            self.warnings.push(self.make_warning("unreachable code", &&stmts[last_stmt_index..]));
        }
        // Restore old scope
        self.pop_current_scope();
        // cfg: now traverse the cfg
        // Track all variables by checking their initialization and usage (by performing DFS on the CFG)
        if let Err(err) = self.traverse_cfg(&scope_id) {
            self.saved_errors.push_err(err);
        }
        // Mark the block scope visited
        self.set_scope_eval_state(&scope_id, ScopeEvalState::Visited);
        // Create the context
        Ok(Context {
            is_lvalue,
            taipe: block_ret_type.add_const(),
            value: context::Value::Block(items),
        })
    }

    // Control flow analysis

    fn traverse_cfg(&mut self, scope_id: &ScopeId) -> CompileResult<()> {
        // debug!("in: {}", self.current_scope_id.sym_path);
        let Payload::Block(ref data) = self.get_scope(scope_id).payload else {
            unreachable!("probably some analyzer bug");
        };
        let result = self.traverse_cfg_impl(scope_id, data.cf_start, &mut HashSet::new(), HashMap::new(), 0);
        // debug!("");
        result
    }
    fn get_cfg(&self, block_scope_id: &ScopeId) -> &ControlGraph {
        let Payload::Block(ref data) = self.get_scope(&block_scope_id).payload else {
            unreachable!("probably some analyzer bug");
        };
        &data.cfg
    }
    fn traverse_cfg_impl(
        &mut self,
        scope_id: &ScopeId,
        node_id: ControlNodeId,
        visited: &mut HashSet<ControlNodeId>,
        mut declared_vars: HashMap<SymbolPath, ControlInfo>,
        mut depth: usize,
    ) -> CompileResult<()> {        
        // Mark as visited
        visited.insert(node_id);
        let mut errs = CompileError::new();
        // Track variables
        let mut is_end = false;
        let node = self.get_cfg(&scope_id).get_vertex(node_id).cloned().unwrap();
        match node {
            ControlNode::Start => {
                // debug!("{}start", " ".repeat(depth));
                depth += 1;
            }
            ControlNode::Junction => {
                // debug!("{}junction", " ".repeat(depth));
            }
            ControlNode::Info(info) => match info {
                ControlInfo::VarDeclared { ref scope_id } => {
                    // debug!(
                    //     "{}declared variable -> {}:{}",
                    //     " ".repeat(depth),
                    //     line_info.line_start,
                    //     line_info.col_start
                    // );
                    declared_vars.insert(self.get_scope(scope_id).id.sym_path.clone(), info.clone());
                }
                ControlInfo::VarUsed { line_info, scope_id } => {
                    // debug!(
                    //     "{}variable used -> {}:{}",
                    //     " ".repeat(depth),
                    //     line_info.line_start,
                    //     line_info.col_start
                    // );
                    let scope = self.get_scope(&scope_id);
                    if let Some(prev_cf_info) = declared_vars.get(&scope.id.sym_path) {
                        match prev_cf_info {
                            ControlInfo::VarDeclared { scope_id: _ } => {
                                let msg = format!("'{}' may be uninitialized", scope.name);
                                errs = errors![
                                    errs,
                                    self.make_err(msg, &line_info),
                                    self.make_note("declared here", scope),
                                ];
                            }
                            _ => {}
                        }
                    } else {
                        // probably the declaration is outside of this scope
                        let Payload::Block(ref mut data) = self.get_current_block_mut().expect("not in a block").payload else {
                            unreachable!("probably some analyzer bug");
                        };
                        let cf_node = data.cfg.insert_vertex(ControlNode::Info(ControlInfo::VarUsed {
                            line_info,
                            scope_id: scope_id,
                        }));
                        data.cfg.insert_edge(data.cf_last, cf_node);
                        data.cf_last = cf_node;
                    }
                }
                ControlInfo::VarAssigned { line_info, ref scope_id } => {
                    // debug!(
                    //     "{}declared assigned -> {}:{}",
                    //     " ".repeat(depth),
                    //     line_info.line_start,
                    //     line_info.col_start
                    // );
                    if let Some(prev_cf_info) = declared_vars.get_mut(&self.get_scope(scope_id).id.sym_path) {
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
                        let Payload::Block(ref mut data) = self.get_current_block_mut().expect("not in a block").payload else {
                            unreachable!("probably some analyzer bug");
                        };
                        let cf_node = data.cfg.insert_vertex(ControlNode::Info(ControlInfo::VarAssigned {
                            line_info,
                            scope_id: scope_id.clone(),
                        }));
                        data.cfg.insert_edge(data.cf_last, cf_node);
                        data.cf_last = cf_node;
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
        let outgoing = self.get_cfg(&scope_id).outgoing(node_id);
        for dest_node_id in outgoing {
            assert!(!is_end);
            if !visited.contains(&dest_node_id) {
                if let Err(dest_err) = self.traverse_cfg_impl(scope_id, dest_node_id, visited, declared_vars.clone(), depth)
                {
                    // Accumulate errors
                    errs.push_err(dest_err)
                };
            }
        }
        // Return the accumulated errors
        if errs.is_empty() { Ok(()) } else { Err(errs) }
    }
    
    // ------------------------------------------------------------
    // Compile time evaluation
    // ------------------------------------------------------------

    fn compeval_trivial(
        &self,
        ctx: &Context,
    ) -> CompileResult<Context> {
        self.compeval_trivial_impl(ctx.is_lvalue, &ctx.taipe, &ctx.value, &mut HashMap::new())
    }
    fn compeval_trivial_impl(
        &self,
        is_lvalue: bool,
        taipe: &context::Type,
        value: &context::Value,
        var_state: &mut HashMap<SymbolPath, Context>,
    ) -> CompileResult<Context> {
        macro_rules! return_err {
            (compeval_not_trivial: $line_info:expr) => {
                return Err(self.make_err(
                    "could not evaluate expression trivially at compile time",
                    $line_info,
                ))
            };
            (integer_overflow: $line_info:expr) => {
                return Err(self.make_err("detected integer overflow", $line_info));
            };
        }
        // Only returns
        // - Value::Imm
        // - Value::Array
        // - Value::Tuple
        // - noreturn
        // - void
        match value {
            context::Value::Imm(_) => Ok(Context {
                is_lvalue,
                taipe: taipe.clone(),
                value: value.clone(),
            }),
            context::Value::Array(values) => {
                let context::Type::Array { count, taipe } = taipe else {
                    unreachable!("probably some analyzer bug");
                };
                let mut new_values = Vec::new();
                for value in values {
                    let new_value = self.compeval_trivial_impl(false, taipe, value, var_state)?.value;
                    new_values.push(new_value);
                }
                Ok(Context {
                    is_lvalue,
                    taipe: context::Type::Array {
                        count: *count,
                        taipe: Box::clone(taipe),
                    },
                    value: context::Value::Array(new_values),
                })
            }
            context::Value::Tuple(values) => {
                let context::Type::Tuple(types) = taipe else {
                    unreachable!("probably some analyzer bug");
                };
                assert!(types.len() == values.len());
                let mut new_values = Vec::new();
                for (taipe, value) in types.iter().zip(values.into_iter()) {
                    let new_value = self.compeval_trivial_impl(false, taipe, value, var_state)?.value;
                    new_values.push(new_value);
                }
                Ok(Context {
                    is_lvalue: is_lvalue,
                    taipe: context::Type::Tuple(types.clone()),
                    value: context::Value::Tuple(new_values),
                })
            }
            
            context::Value::GetGlobal { line_info, scope_id } => {
                let scope = self.get_scope(scope_id);
                if !scope.is_const() {
                    return Err(errors![
                        self.make_err("accessing global variables is not allowed in trivial compeval context", line_info),
                        self.make_note_no_path("only accessing global constants is allowed"),
                    ]);
                }
                let Payload::Global(info) = &scope.payload else { unreachable!("probably some analyzer bug"); };
                Ok(info.ctx.clone())
            },
            context::Value::GetLocal { line_info, scope_id } => todo!(),
            context::Value::GetField { line_info, lhs, scope_id } => todo!(),
            context::Value::SetGlobal { line_info, scope_id: _, rhs: _ } => Err(errors![
                self.make_err("could not evaluate expression trivially at compile time", line_info),
                self.make_note_no_path("setting global variables may produce side effects")
            ]),
            context::Value::SetLocal { line_info, scope_id, rhs } => Err(errors![
                self.make_err("could not evaluate expression trivially at compile time", line_info),
                self.make_note_no_path("setting local variables may produce side effects")
            ]),
            context::Value::SetField { line_info, lhs, scope_id, rhs } => Err(errors![
                self.make_err("could not evaluate expression trivially at compile time", line_info),
                self.make_note_no_path("setting fields may produce side effects")
            ]),

            context::Value::Negate { line_info, ctx } => {
                let ctx = self.compeval_trivial_impl(ctx.is_lvalue, &ctx.taipe, &ctx.value, var_state)?;
                assert!(ctx.taipe.is_signed_integer() || ctx.taipe.is_float());
                if let context::Value::Imm(imm) = ctx.value {
                    Ok(Context {
                        is_lvalue: false,
                        taipe: ctx.taipe.remove_const(),
                        value: context::Value::Imm(imm.negate()),
                    })
                } else {
                    return_err!(compeval_not_trivial: line_info);
                }
            }
            context::Value::FlipBits { line_info, ctx } => {
                let ctx = self.compeval_trivial_impl(ctx.is_lvalue, &ctx.taipe, &ctx.value, var_state)?;
                assert!(ctx.taipe.is_integer());
                if let context::Value::Imm(imm) = ctx.value {
                    Ok(Context {
                        is_lvalue: false,
                        taipe: ctx.taipe.remove_const(),
                        value: context::Value::Imm(imm.flip_bits()),
                    })
                } else {
                    return_err!(compeval_not_trivial: line_info);
                }
            }
            context::Value::Deref { line_info, ctx } => todo!(),
            context::Value::AddrOf { line_info, ctx } => todo!(),
            context::Value::Not { line_info, ctx } => {
                let ctx = self.compeval_trivial_impl(ctx.is_lvalue, &ctx.taipe, &ctx.value, var_state)?;
                assert!(ctx.taipe.is_bool());
                if let context::Value::Imm(context::Imm::Bool(b)) = ctx.value {
                    Ok(Context {
                        is_lvalue: false,
                        taipe: ctx.taipe.remove_const(),
                        value: context::Value::Imm(context::Imm::Bool(!b)),
                    })
                } else {
                    return_err!(compeval_not_trivial: line_info);
                }
            }
            context::Value::Add { line_info, lhs, rhs } => {
                let lhs = self.compeval_trivial_impl(lhs.is_lvalue, &lhs.taipe, &lhs.value, var_state)?;
                let rhs = self.compeval_trivial_impl(rhs.is_lvalue, &rhs.taipe, &rhs.value, var_state)?;
                assert!(lhs.taipe.remove_const() == rhs.taipe.remove_const());
                let res_type = lhs.taipe.remove_const();
                if let context::Value::Imm(lhs) = lhs.value
                    && let context::Value::Imm(rhs) = rhs.value
                {
                    let Some(value) = lhs.add(rhs) else {
                        return_err!(integer_overflow: line_info);
                    };
                    Ok(Context {
                        is_lvalue: false,
                        taipe: res_type,
                        value: context::Value::Imm(value),
                    })
                } else {
                    return_err!(compeval_not_trivial: line_info);
                }
            }
            context::Value::Sub { line_info, lhs, rhs } => {
                let lhs = self.compeval_trivial_impl(lhs.is_lvalue, &lhs.taipe, &lhs.value, var_state)?;
                let rhs = self.compeval_trivial_impl(rhs.is_lvalue, &rhs.taipe, &rhs.value, var_state)?;
                assert!(lhs.taipe.remove_const() == rhs.taipe.remove_const());
                let res_type = lhs.taipe.remove_const();
                if let context::Value::Imm(lhs) = lhs.value
                    && let context::Value::Imm(rhs) = rhs.value
                {
                    let Some(value) = lhs.sub(rhs) else {
                        return_err!(integer_overflow: line_info);
                    };
                    Ok(Context {
                        is_lvalue: false,
                        taipe: res_type,
                        value: context::Value::Imm(value),
                    })
                } else {
                    return_err!(compeval_not_trivial: line_info);
                }
            }
            context::Value::Mul { line_info, lhs, rhs } => {
                let lhs = self.compeval_trivial_impl(lhs.is_lvalue, &lhs.taipe, &lhs.value, var_state)?;
                let rhs = self.compeval_trivial_impl(rhs.is_lvalue, &rhs.taipe, &rhs.value, var_state)?;
                assert!(lhs.taipe.remove_const() == rhs.taipe.remove_const());
                let res_type = lhs.taipe.remove_const();
                if let context::Value::Imm(lhs) = lhs.value
                    && let context::Value::Imm(rhs) = rhs.value
                {
                    let Some(value) = lhs.mul(rhs) else {
                        return_err!(integer_overflow: line_info);
                    };
                    Ok(Context {
                        is_lvalue: false,
                        taipe: res_type,
                        value: context::Value::Imm(value),
                    })
                } else {
                    return_err!(compeval_not_trivial: line_info);
                }
            }
            context::Value::Div { line_info, lhs, rhs } => {
                let lhs = self.compeval_trivial_impl(lhs.is_lvalue, &lhs.taipe, &lhs.value, var_state)?;
                let rhs = self.compeval_trivial_impl(rhs.is_lvalue, &rhs.taipe, &rhs.value, var_state)?;
                assert!(lhs.taipe.remove_const() == rhs.taipe.remove_const());
                let res_type = lhs.taipe.remove_const();
                if let context::Value::Imm(lhs) = lhs.value
                    && let context::Value::Imm(rhs) = rhs.value
                {
                    let Some(value) = lhs.div(rhs) else {
                        return_err!(integer_overflow: line_info);
                    };
                    Ok(Context {
                        is_lvalue: false,
                        taipe: res_type,
                        value: context::Value::Imm(value),
                    })
                } else {
                    return_err!(compeval_not_trivial: line_info);
                }
            }
            context::Value::Rem { line_info, lhs, rhs } => {
                let lhs = self.compeval_trivial_impl(lhs.is_lvalue, &lhs.taipe, &lhs.value, var_state)?;
                let rhs = self.compeval_trivial_impl(rhs.is_lvalue, &rhs.taipe, &rhs.value, var_state)?;
                assert!(lhs.taipe.remove_const() == rhs.taipe.remove_const());
                let res_type = lhs.taipe.remove_const();
                if let context::Value::Imm(lhs) = lhs.value
                    && let context::Value::Imm(rhs) = rhs.value
                {
                    let Some(value) = lhs.modulo(rhs) else {
                        return_err!(integer_overflow: line_info);
                    };
                    Ok(Context {
                        is_lvalue: false,
                        taipe: res_type,
                        value: context::Value::Imm(value),
                    })
                } else {
                    return_err!(compeval_not_trivial: line_info);
                }
            }
            context::Value::Shl { line_info, lhs, rhs } => {
                let lhs = self.compeval_trivial_impl(lhs.is_lvalue, &lhs.taipe, &lhs.value, var_state)?;
                let rhs = self.compeval_trivial_impl(rhs.is_lvalue, &rhs.taipe, &rhs.value, var_state)?;
                assert!(lhs.taipe.is_integer() && rhs.taipe.is_unsigned_integer());
                // TODO: to be changed
                assert!(rhs.taipe == context::Type::Uint32);
                let res_type = lhs.taipe.remove_const();
                if let context::Value::Imm(lhs) = lhs.value
                    && let context::Value::Imm(rhs) = rhs.value
                {
                    Ok(Context {
                        is_lvalue: false,
                        taipe: res_type,
                        value: context::Value::Imm(lhs.shl(rhs)),
                    })
                } else {
                    return_err!(compeval_not_trivial: line_info);
                }
            }
            context::Value::Shr { line_info, lhs, rhs } => {
                let lhs = self.compeval_trivial_impl(lhs.is_lvalue, &lhs.taipe, &lhs.value, var_state)?;
                let rhs = self.compeval_trivial_impl(rhs.is_lvalue, &rhs.taipe, &rhs.value, var_state)?;
                assert!(lhs.taipe.is_integer() && rhs.taipe.is_unsigned_integer());
                // TODO: to be changed
                assert!(rhs.taipe == context::Type::Uint32);
                let res_type = lhs.taipe.remove_const();
                if let context::Value::Imm(lhs) = lhs.value
                    && let context::Value::Imm(rhs) = rhs.value
                {
                    Ok(Context {
                        is_lvalue: false,
                        taipe: res_type,
                        value: context::Value::Imm(lhs.shr(rhs)),
                    })
                } else {
                    return_err!(compeval_not_trivial: line_info);
                }
            }
            context::Value::BitAnd { line_info, lhs, rhs } => {
                let lhs = self.compeval_trivial_impl(lhs.is_lvalue, &lhs.taipe, &lhs.value, var_state)?;
                let rhs = self.compeval_trivial_impl(rhs.is_lvalue, &rhs.taipe, &rhs.value, var_state)?;
                assert!(lhs.taipe.remove_const() == rhs.taipe.remove_const());
                assert!(lhs.taipe.is_integer() && rhs.taipe.is_integer());
                let res_type = lhs.taipe.remove_const();
                if let context::Value::Imm(lhs) = lhs.value
                    && let context::Value::Imm(rhs) = rhs.value
                {
                    Ok(Context {
                        is_lvalue: false,
                        taipe: res_type,
                        value: context::Value::Imm(lhs.bit_and(rhs)),
                    })
                } else {
                    return_err!(compeval_not_trivial: line_info);
                }
            }
            context::Value::BitXor { line_info, lhs, rhs } => {
                let lhs = self.compeval_trivial_impl(lhs.is_lvalue, &lhs.taipe, &lhs.value, var_state)?;
                let rhs = self.compeval_trivial_impl(rhs.is_lvalue, &rhs.taipe, &rhs.value, var_state)?;
                assert!(lhs.taipe.remove_const() == rhs.taipe.remove_const());
                assert!(lhs.taipe.is_integer() && rhs.taipe.is_integer());
                let res_type = lhs.taipe.remove_const();
                if let context::Value::Imm(lhs) = lhs.value
                    && let context::Value::Imm(rhs) = rhs.value
                {
                    Ok(Context {
                        is_lvalue: false,
                        taipe: res_type,
                        value: context::Value::Imm(lhs.bit_xor(rhs)),
                    })
                } else {
                    return_err!(compeval_not_trivial: line_info);
                }
            }
            context::Value::BitOr { line_info, lhs, rhs } => {
                let lhs = self.compeval_trivial_impl(lhs.is_lvalue, &lhs.taipe, &lhs.value, var_state)?;
                let rhs = self.compeval_trivial_impl(rhs.is_lvalue, &rhs.taipe, &rhs.value, var_state)?;
                assert!(lhs.taipe.remove_const() == rhs.taipe.remove_const());
                assert!(lhs.taipe.is_integer() && rhs.taipe.is_integer());
                let res_type = lhs.taipe.remove_const();
                if let context::Value::Imm(lhs) = lhs.value
                    && let context::Value::Imm(rhs) = rhs.value
                {
                    Ok(Context {
                        is_lvalue: false,
                        taipe: res_type,
                        value: context::Value::Imm(lhs.bit_or(rhs)),
                    })
                } else {
                    return_err!(compeval_not_trivial: line_info);
                }
            }
            context::Value::Lt { line_info, lhs, rhs } => todo!(),
            context::Value::Le { line_info, lhs, rhs } => todo!(),
            context::Value::Eq { line_info, lhs, rhs } => todo!(),
            context::Value::Ne { line_info, lhs, rhs } => todo!(),
            context::Value::Ge { line_info, lhs, rhs } => todo!(),
            context::Value::Gt { line_info, lhs, rhs } => todo!(),
            context::Value::LogicAnd { line_info, lhs, rhs } => {
                assert!(lhs.taipe.is_bool() && rhs.taipe.is_bool());
                let lhs = self.compeval_trivial_impl(lhs.is_lvalue, &lhs.taipe, &lhs.value, var_state)?;
                assert!(lhs.taipe.is_bool());
                if let context::Value::Imm(context::Imm::Bool(lhs)) = lhs.value {
                    if lhs {
                        let rhs = self.compeval_trivial_impl(rhs.is_lvalue, &rhs.taipe, &rhs.value, var_state)?;
                        assert!(rhs.taipe.is_bool());
                        if let context::Value::Imm(context::Imm::Bool(rhs)) = rhs.value {
                            if rhs {
                                Ok(Context::from_bool(true))
                            } else {
                                Ok(Context::from_bool(false))
                            }
                        } else {
                            return_err!(compeval_not_trivial: line_info);
                        }
                    } else {
                        Ok(Context::from_bool(false))
                    }
                } else {
                    return_err!(compeval_not_trivial: line_info);
                }
            }
            context::Value::LogicOr { line_info, lhs, rhs } => {
                assert!(lhs.taipe.is_bool() && rhs.taipe.is_bool());
                let lhs = self.compeval_trivial_impl(lhs.is_lvalue, &lhs.taipe, &lhs.value, var_state)?;
                assert!(lhs.taipe.is_bool());
                if let context::Value::Imm(context::Imm::Bool(lhs)) = lhs.value {
                    if lhs {
                        Ok(Context::from_bool(true))
                    } else {
                        let rhs = self.compeval_trivial_impl(rhs.is_lvalue, &rhs.taipe, &rhs.value, var_state)?;
                        assert!(rhs.taipe.is_bool());
                        if let context::Value::Imm(context::Imm::Bool(rhs)) = rhs.value {
                            if rhs {
                                Ok(Context::from_bool(true))
                            } else {
                                Ok(Context::from_bool(false))
                            }
                        } else {
                            return_err!(compeval_not_trivial: line_info);
                        }
                    }
                } else {
                    return_err!(compeval_not_trivial: line_info);
                }
            }
            context::Value::Index { line_info, lhs, index } => {
                let lhs = self.compeval_trivial_impl(lhs.is_lvalue, &lhs.taipe, &lhs.value, var_state)?;
                let index_ctx = self.compeval_trivial_impl(index.is_lvalue, &index.taipe, &index.value, var_state)?;
                let context::Value::Imm(index_imm) = index_ctx.value else {
                    return_err!(compeval_not_trivial: line_info);
                };
                let Some(index) = index_imm.to_usize() else {
                    unreachable!("probably some analyzer bug");
                };
                match lhs.value {
                    context::Value::Array(values) => {
                        debug!("{}", line_info);
                        debug!("{}", lhs.taipe);
                        let taipe = match lhs.taipe {
                            context::Type::Array { count: _, taipe } => taipe,
                            context::Type::Fat(taipe) => taipe,
                            context::Type::Const(taipe) => match *taipe {
                                context::Type::Array { count: _, taipe } => taipe,
                                context::Type::Fat(taipe) => taipe,
                                _ => unreachable!("probably some analyzer bug"),
                            },
                            _ => unreachable!("probably some analyzer bug"),
                        };
                        let Some(value) = values.into_iter().nth(index) else {
                            unreachable!("probably some analyzer bug");
                        };
                        Ok(self.compeval_trivial_impl(is_lvalue, &taipe, &value, var_state)?)
                    }
                    context::Value::Tuple(values) => {
                        let types = match lhs.taipe {
                            context::Type::Tuple(types) => types,
                            context::Type::Const(taipe) => match *taipe {
                                context::Type::Tuple(types) => types,
                                _ => unreachable!("probably some analyzer bug"),
                            },
                            _ => unreachable!("probably some analyzer bug"),
                        };
                        let Some(taipe) = types.into_iter().nth(index) else {
                            unreachable!("probably some analyzer bug");
                        };
                        let Some(value) = values.into_iter().nth(index) else {
                            unreachable!("probably some analyzer bug");
                        };
                        Ok(self.compeval_trivial_impl(is_lvalue, &taipe, &value, var_state)?)
                    }
                    _ => return_err!(compeval_not_trivial: line_info),
                }
            }
            context::Value::DirectCall { line_info, fun_scope_id: _, args: _ }
            | context::Value::IndirectCall { line_info, lhs: _, args: _ } => Err(errors![
                self.make_err("could not evaluate expression trivially at compile time", line_info),
                self.make_note_no_path("function call may have side effects")
            ]),
            context::Value::IfElse {
                line_info,
                cond,
                then_ctx,
                else_ctx,
            } => {
                let cond = self.compeval_trivial_impl(cond.is_lvalue, &cond.taipe, &cond.value, var_state)?;
                assert!(cond.taipe.is_bool());
                if let context::Value::Imm(context::Imm::Bool(cond)) = cond.value {
                    if cond {
                        self.compeval_trivial_impl(then_ctx.is_lvalue, &then_ctx.taipe, &then_ctx.value, var_state)
                    } else {
                        self.compeval_trivial_impl(else_ctx.is_lvalue, &else_ctx.taipe, &else_ctx.value, var_state)
                    }
                } else {
                    return_err!(compeval_not_trivial: line_info);
                }
            }
            context::Value::While {
                line_info,
                cond,
                body_ctx,
            } => {
                loop {
                    let cond_result = self.compeval_trivial_impl(cond.is_lvalue, &cond.taipe, &cond.value, var_state)?;
                    assert!(cond_result.taipe.is_bool());
                    if let context::Value::Imm(context::Imm::Bool(cond)) = cond_result.value {
                        if cond {
                            self.compeval_trivial_impl(body_ctx.is_lvalue, &body_ctx.taipe, &body_ctx.value, var_state)?;
                        } else {
                            break;
                        }
                    } else {
                        return_err!(compeval_not_trivial: line_info);
                    }
                }
                Ok(Context::from_void())
            }
            context::Value::Block(ctxs) => {
                let ctx_count = ctxs.len();
                for (i, ctx) in ctxs.iter().enumerate() {
                    let ctx = self.compeval_trivial_impl(ctx.is_lvalue, &ctx.taipe, &ctx.value, var_state)?;
                    if i >= ctx_count - 1 {
                        return Ok(ctx);
                    }
                }
                Ok(Context::from_void())
            }
            context::Value::Ret(ctx) => {
                let _ = self.compeval_trivial_impl(ctx.is_lvalue, &ctx.taipe, &ctx.value, var_state)?;
                Ok(Context::from_noreturn())
            }
            context::Value::RetVoid => Ok(Context::from_noreturn()),
            context::Value::Eval(ctx) => {
                let _ = self.compeval_trivial_impl(ctx.is_lvalue, &ctx.taipe, &ctx.value, var_state)?;
                Ok(Context::from_void())
            }
            context::Value::Cast(from) => {
                let from = self.compeval_trivial_impl(from.is_lvalue, &from.taipe, &from.value, var_state)?;
                let to = taipe.clone();

                if from.taipe.is_signed_integer() {
                    let context::Value::Imm(ref from_imm) = from.value else {
                        unreachable!("probably some analyzer bug")
                    };
                    let from_value: i128 = match from_imm {
                        context::Imm::Int8(value) => *value as i128,
                        context::Imm::Int16(value) => *value as i128,
                        context::Imm::Int32(value) => *value as i128,
                        context::Imm::Int64(value) => *value as i128,
                        context::Imm::Int128(value) => *value as i128,
                        _ => unreachable!("probably some analyzer bug")
                    };
                    let to_imm = match to.remove_const() {
                        context::Type::Int8 => context::Imm::Int8(from_value as i8),
                        context::Type::Int16 => context::Imm::Int16(from_value as i16),
                        context::Type::Int32 => context::Imm::Int32(from_value as i32),
                        context::Type::Int64 => context::Imm::Int64(from_value as i64),
                        context::Type::Int128 => context::Imm::Int128(from_value as i128),
                        context::Type::Uint8 => context::Imm::Uint8(from_value as u8),
                        context::Type::Uint16 => context::Imm::Uint16(from_value as u16),
                        context::Type::Uint32 => context::Imm::Uint32(from_value as u32),
                        context::Type::Uint64 => context::Imm::Uint64(from_value as u64),
                        context::Type::Uint128 => context::Imm::Uint128(from_value as u128),
                        context::Type::Float32 => context::Imm::Float32(from_value as f32),
                        context::Type::Float64 => context::Imm::Float64(from_value as f64),
                        _ => unreachable!("probably some analyzer bug")
                    };
                    Ok(Context {
                        is_lvalue: false,
                        taipe: to,
                        value: context::Value::Imm(to_imm)
                    })
                } else if from.taipe.is_unsigned_integer() {
                    let context::Value::Imm(ref from_imm) = from.value else {
                        unreachable!("probably some analyzer bug")
                    };
                    let from_value: u128 = match from_imm {
                        context::Imm::Uint8(value) => *value as u128,
                        context::Imm::Uint16(value) => *value as u128,
                        context::Imm::Uint32(value) => *value as u128,
                        context::Imm::Uint64(value) => *value as u128,
                        context::Imm::Uint128(value) => *value as u128,
                        _ => unreachable!("probably some analyzer bug")
                    };
                    let to_imm = match to.remove_const() {
                        context::Type::Int8 => context::Imm::Int8(from_value as i8),
                        context::Type::Int16 => context::Imm::Int16(from_value as i16),
                        context::Type::Int32 => context::Imm::Int32(from_value as i32),
                        context::Type::Int64 => context::Imm::Int64(from_value as i64),
                        context::Type::Int128 => context::Imm::Int128(from_value as i128),
                        context::Type::Uint8 => context::Imm::Uint8(from_value as u8),
                        context::Type::Uint16 => context::Imm::Uint16(from_value as u16),
                        context::Type::Uint32 => context::Imm::Uint32(from_value as u32),
                        context::Type::Uint64 => context::Imm::Uint64(from_value as u64),
                        context::Type::Uint128 => context::Imm::Uint128(from_value as u128),
                        context::Type::Float32 => context::Imm::Float32(from_value as f32),
                        context::Type::Float64 => context::Imm::Float64(from_value as f64),
                        _ => unreachable!("probably some analyzer bug")
                    };
                    Ok(Context {
                        is_lvalue: false,
                        taipe: to,
                        value: context::Value::Imm(to_imm)
                    })
                } else if from.taipe.is_float() {
                    let context::Value::Imm(ref from_imm) = from.value else {
                        unreachable!("probably some analyzer bug")
                    };
                    let from_value: f64 = match from_imm {
                        context::Imm::Float32(value) => *value as f64,
                        context::Imm::Float64(value) => *value as f64,
                        _ => unreachable!("probably some analyzer bug")
                    };
                    let to_imm = match to.remove_const() {
                        context::Type::Int8 => context::Imm::Int8(from_value as i8),
                        context::Type::Int16 => context::Imm::Int16(from_value as i16),
                        context::Type::Int32 => context::Imm::Int32(from_value as i32),
                        context::Type::Int64 => context::Imm::Int64(from_value as i64),
                        context::Type::Int128 => context::Imm::Int128(from_value as i128),
                        context::Type::Uint8 => context::Imm::Uint8(from_value as u8),
                        context::Type::Uint16 => context::Imm::Uint16(from_value as u16),
                        context::Type::Uint32 => context::Imm::Uint32(from_value as u32),
                        context::Type::Uint64 => context::Imm::Uint64(from_value as u64),
                        context::Type::Uint128 => context::Imm::Uint128(from_value as u128),
                        context::Type::Float32 => context::Imm::Float32(from_value as f32),
                        context::Type::Float64 => context::Imm::Float64(from_value as f64),
                        _ => unreachable!("probably some analyzer bug")
                    };
                    Ok(Context {
                        is_lvalue: false,
                        taipe: to,
                        value: context::Value::Imm(to_imm)
                    })
                } else if from.taipe.is_array() && to.is_fat_ptr() {
                    Ok(Context {
                        is_lvalue: false,
                        taipe: to,
                        value: from.value
                    })
                } else {
                    unreachable!("probably some analyzer bug")
                }
            },
        }
    }
    
    // ------------------------------------------------------------
    // Expression analysis
    // ------------------------------------------------------------
    fn visit_expr(&mut self, node: &'a ast::Expr) -> CompileResult<Context> {
        let ctx = self.visit_expr_impl(node)?;
        if let context::Value::GetLocal { line_info: _, ref scope_id } = ctx.value {
            // cfg: insert variable used node
            //      only if it is a local variable or constant
            let should_insert_cfg = match self.get_scope(scope_id).kind {
                ScopeKind::Variable => true,
                ScopeKind::Const => true,
                _ => false,
            };
            if should_insert_cfg {
                assert!(self.get_current_block().is_some());
                assert!(self.get_enclosing_block(&scope_id).is_some());
                self.mut_current_block_data(|data| {
                    let cf_node = data.cfg.insert_vertex(ControlNode::Info(ControlInfo::VarUsed {
                        line_info: node.get_line_info(),
                        scope_id: scope_id.clone(),
                    }));
                    data.cfg.insert_edge(data.cf_last, cf_node);
                    data.cf_last = cf_node;
                });
            }
        }
        Ok(ctx)
    }
    fn visit_expr_lhs_of_assign(&mut self, node: &'a ast::Expr) -> CompileResult<Context> {
        let ctx = self.visit_expr_impl(node)?;
        if let context::Value::GetLocal { line_info: _, ref scope_id } = ctx.value {
            // cfg: insert variable assigned node
            //      only if it is a local variable or constant
            let should_insert_cfg = match self.get_scope(scope_id).kind {
                ScopeKind::Variable => true,
                ScopeKind::Const => true,
                _ => false,
            };
            if should_insert_cfg {
                assert!(self.get_current_block().is_some());
                assert!(self.get_enclosing_block(&scope_id).is_some());
                self.mut_current_block_data(|data| {
                    let cf_node = data.cfg.insert_vertex(ControlNode::Info(ControlInfo::VarAssigned {
                        line_info: node.get_line_info(),
                        scope_id: scope_id.clone(),
                    }));
                    data.cfg.insert_edge(data.cf_last, cf_node);
                    data.cf_last = cf_node;
                });
            }
        }
        Ok(ctx)
    }
    fn visit_expr_impl(&mut self, node: &'a ast::Expr) -> CompileResult<Context> {
        match node {
            ast::Expr::Block { line_info, stmts } => {
                // TODO: Block expressions should never create a block scope
                self.visit_block(*line_info, stmts)
            },
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
                let mut assigns = Vec::new();
                for i in 0..rhses.len() {
                    // Visit rhs of assign
                    let rhs_node = &rhses[i];
                    let rhs_line_info = rhs_node.get_line_info();
                    let mut rhs = self.visit_expr(rhs_node)?;
                    // Visit lhs of assign
                    let lhs_node = &lhses[i];
                    let lhs_line_info = lhs_node.get_line_info();
                    let lhs = self.visit_expr_lhs_of_assign(lhs_node)?;
                    // do lvalue checking
                    if !lhs.is_lvalue {
                        return Err(self.make_err("cannot assign to a prvalue (pure rvalue)", &lhs_line_info));
                    }
                    // check assignment
                    rhs = self.resolve_assign(Some((lhs.taipe, lhs_line_info)), None, Some((rhs, rhs_line_info)))?;
                    // now transform get to set
                    let line_info = node.get_line_info();
                    assigns.push(Context {
                        is_lvalue: false,
                        taipe: context::Type::Void,
                        value: match lhs.value {
                            context::Value::GetGlobal { line_info: _, scope_id } => context::Value::SetGlobal {
                                line_info, scope_id, rhs: Box::new(rhs),
                            },
                            context::Value::GetLocal { line_info: _, scope_id } => context::Value::SetLocal {
                                line_info, scope_id, rhs: Box::new(rhs),
                            },
                            context::Value::GetField { line_info: _, lhs, scope_id } => context::Value::SetField {
                                line_info, lhs, scope_id, rhs: Box::new(rhs),
                            },
                            _ => unreachable!("probably some analyzer bug"),
                        }
                    });
                }
                if assigns.len() == 1 {
                    Ok(assigns.into_iter().next().unwrap())
                } else {
                    Ok(Context {
                        is_lvalue: false,
                        taipe: context::Type::Void,
                        value: context::Value::Block(assigns),
                    })
                }
            }
            ast::Expr::Binary { left, op, right } => self.visit_binary(left, op, right),
            ast::Expr::Cast { expr, taipe } => {
                let ctx = self.visit_expr(expr)?;
                let taipe = self.visit_type(taipe)?;
                
                // Conversions that are defined:
                // * from: {integer} to: iX
                // * from: {integer} to: uX
                // * from: {integer} to: fX
                // * from: uX        to: iX
                // * from: iX        to: uX
                // * from: iX        to: fX
                // * from: uX        to: fX
                // * from: fX        to: iX
                // * from: fX        to: uX
                // * from: [N]T      to: []T

                // directly change varint and do not keep it for later
                if ctx.taipe.is_varint() && (taipe.is_integer() || taipe.is_float()) {
                    let context::Value::Imm(ref imm) = ctx.value else {
                        unreachable!("probably some analyzer bug")
                    };
                    let new_imm = self.transform_varint(&taipe, imm, expr, None)?;
                    return Ok(Context {
                        is_lvalue: false,
                        taipe,
                        value: context::Value::Imm(new_imm)
                    })
                }

                let result = self.is_castable(&ctx.taipe, &taipe);
                if result {
                    Ok(Context {
                        is_lvalue: false,
                        taipe,
                        value: context::Value::Cast(Box::new(ctx))
                    })
                } else {
                    Err(self.make_err(format!("cannot cast expression of type '{}' to type '{}'", ctx, taipe), node))
                }
            }
            ast::Expr::Unary { op, expr } => self.visit_unary(op, expr),
            ast::Expr::Member { expr, name } => {
                let ctx = self.visit_expr(expr)?;
                let keep_lvalue = ctx.is_lvalue;
                let (keep_const, taipe) = match ctx.taipe {
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
                    context::Type::Basic(scope_id) => {
                        let mut ctx = self.get_member(&scope_id, &name)?;
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
                        let Some(TokenValue::Int { integral: index, suffix }) = name.value.clone() else {
                            unreachable!("probably some lexer bug");
                        };
                        if suffix.is_some() {
                            return Err(self.make_err("suffix is not allowed in this context", name));
                        }
                        // comptime: bounds checking
                        if index >= items.len().to_bigint().unwrap() {
                            return Err(self.make_err(
                                format!("index out of bounds, tuple length: {}, index: '{}'", items.len(), index),
                                name,
                            ));
                        }
                        // Get the type
                        let mut taipe = items[index.to_usize().unwrap()].clone();
                        if keep_const {
                            taipe = taipe.add_const();
                        }
                        // comptime: tuple indexing
                        let index = Context {
                            is_lvalue: false,
                            taipe: self.type_usize.clone(),
                            value: context::Value::Imm(
                                self.transform_varint_to_usize(&context::Imm::VarInt(index), name)?,
                            ),
                        };
                        Ok(Context {
                            is_lvalue: keep_lvalue,
                            taipe,
                            value: context::Value::Index {
                                line_info: node.get_line_info(),
                                lhs: Box::new(Context {
                                    is_lvalue: keep_lvalue,
                                    taipe: context::Type::Tuple(items),
                                    value: ctx.value,
                                }),
                                index: Box::new(index),
                            },
                        })
                    }
                    context::Type::Module => {
                        let context::Value::Imm(context::Imm::Module(module)) = ctx.value else {
                            unreachable!("probably some analyzer bug");
                        };
                        self.get_member(&module, &name)
                    }
                    // TODO: implement this after struct functions
                    // context::Type::Typedef => todo!(),
                    taipe => Err(self.make_err(format!("cannot use '.' operator on '{}'", taipe), expr)),
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
                    return Err(errors![
                        self.make_err("argument of index operator should be an integer type", node),
                        self.make_note(format!("but got '{}'", index.taipe), index_node)
                    ]);
                }
                match ctx.taipe.remove_const() {
                    context::Type::Array { count: _, taipe } => Ok(Context {
                        is_lvalue: false,
                        taipe: *taipe,
                        value: context::Value::Index {
                            line_info: node.get_line_info(),
                            lhs: Box::new(ctx),
                            index: Box::new(index),
                        },
                    }),
                    context::Type::Fat(taipe) => Ok(Context {
                        is_lvalue: false,
                        taipe: *taipe,
                        value: context::Value::Index {
                            line_info: node.get_line_info(),
                            lhs: Box::new(ctx),
                            index: Box::new(index),
                        },
                    }),
                    _ => {
                        return Err(self.make_err(format!("cannot use index operator on type '{}'", ctx.taipe), expr));
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
                    let TokenValue::Int { integral, suffix } = tok_val else {
                        unreachable!("probably some lexer bug");
                    };
                    let imm = context::Imm::VarInt(integral.clone());
                    let (taipe, name) = match suffix {
                        Some(suffix) => match suffix {
                            TokenSuffix::I8 => (&context::Type::Int8, None),
                            TokenSuffix::I16 => (&context::Type::Int16, None),
                            TokenSuffix::I32 => (&context::Type::Int32, None),
                            TokenSuffix::I64 => (&context::Type::Int64, None),
                            TokenSuffix::I128 => (&context::Type::Int128, None),
                            TokenSuffix::U8 => (&context::Type::Uint8, None),
                            TokenSuffix::U16 => (&context::Type::Uint16, None),
                            TokenSuffix::U32 => (&context::Type::Uint32, None),
                            TokenSuffix::U64 => (&context::Type::Uint64, None),
                            TokenSuffix::U128 => (&context::Type::Uint128, None),
                            TokenSuffix::ISize => (&self.type_isize, Some("isize")),
                            TokenSuffix::USize => (&self.type_usize, Some("usize")),
                            _ => unreachable!("probably some lexer bug"),
                        },
                        None => (&context::Type::VarInt, None),
                    };
                    let imm = self.transform_varint(taipe, &imm, token, name)?;
                    Ok(Context {
                        is_lvalue: false,
                        taipe: taipe.clone(),
                        value: context::Value::Imm(imm),
                    })
                }
                TokenKind::FloatLit => {
                    let Some(tok_val) = token.value.as_ref() else {
                        unreachable!("probably some lexer bug");
                    };
                    let TokenValue::Float { integral, fractional, mantissa, suffix } = tok_val else {
                        unreachable!("probably some lexer bug");
                    };
                    let Some(mantissa) = mantissa.to_i64() else {
                        return Err(self.make_err(
                            format!(
                                "'{}' cannot hold this value: '{}' as mantissa of the floating point literal",
                                context::Type::Int64,
                                mantissa,
                            ),
                            token,
                        ))
                    };
                    let num = {
                        let mut num_str = integral.to_string();
                        num_str.push_str(&fractional.to_string());
                        BigInt::from_str(&num_str).expect("not supposed to happen")
                    };
                    let scale = fractional.to_string().len() as i64 - mantissa;
                    let decimal = BigDecimal::from_bigint(num, scale);
                    let (taipe, imm) = match suffix {
                        Some(suffix) => match suffix {
                            TokenSuffix::F32 => if let Some(value) = decimal.to_f32() {
                                (context::Type::Float32, context::Imm::Float32(value))
                            } else {
                                return Err(self.make_err(
                                    format!(
                                        "'{}' cannot hold this value: '{}'",
                                        context::Type::Float32,
                                        decimal,
                                    ),
                                    token,
                                ))
                            },
                            TokenSuffix::F64 => if let Some(value) = decimal.to_f64() {
                                (context::Type::Float64, context::Imm::Float64(value))
                            } else {
                                return Err(self.make_err(
                                    format!(
                                        "'{}' cannot hold this value: '{}'",
                                        context::Type::Float64,
                                        decimal,
                                    ),
                                    token,
                                ))
                            },
                            _ => unreachable!("probably some lexer bug"),
                        },
                        None => if let Some(value) = decimal.to_f64() {
                            (context::Type::Float64, context::Imm::Float64(value))
                        } else {
                            return Err(self.make_err(
                                format!(
                                    "'{}' cannot hold this value: '{}'",
                                    context::Type::Float64,
                                    decimal,
                                ),
                                token,
                            ))
                        },
                    };
                    Ok(Context {
                        is_lvalue: false,
                        taipe,
                        value: context::Value::Imm(imm),
                    })
                },
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
            ast::Expr::Compeval {
                line_info: _,
                trivial,
                expr,
            } => {
                let mut ctx = self.visit_expr(expr)?;
                if let Some(trivial) = trivial {
                    assert!(trivial.kind == TokenKind::DirectiveTrivial);
                    ctx = self.compeval_trivial(&ctx)?;
                } else {
                    // TODO: change this to non_trivial
                    ctx = self.compeval_trivial(&ctx)?;
                }
                Ok(ctx)
            }
        }
    }

    fn is_castable(&self, from: &context::Type, to: &context::Type) -> bool {
        // TODO: Casting of non-primitive types should be based on
        // size, alignment and offset of individual members
        if from.is_integer() && to.is_integer() {
            true
        } else if from.is_integer() && to.is_float() {
            true
        } else if from.is_float() && to.is_integer() {
            true
        } else if from.is_array() && to.is_fat_ptr() {
            let context::Type::Array { count: _, taipe: arr_type } = from.remove_const() else {
                unreachable!("not supposed to happen")
            };
            let context::Type::Fat(fat_type) = to.remove_const() else {
                unreachable!("not supposed to happen")
            };
            arr_type == fat_type
        } else {
            false
        }
    }

    fn visit_call(
        &mut self,
        node: &'a ast::Expr,
        expr: &'a ast::Expr,
        args: &'a [ast::Arg],
    ) -> CompileResult<Context> {
        let ctx = self.visit_expr(expr)?;
        if !ctx.taipe.is_function() {
            return Err(self.make_err(format!("expected function but got value of type '{}'", ctx), expr));
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
                    return Err(errors![
                        self.make_err("duplicate named argument", name),
                        self.make_note("previous named argument is here", &line_info)
                    ]);
                }
            } else {
                if let Some(ref prev_named_arg) = prev_named_arg {
                    return Err(errors![
                        self.make_err("unnamed argument is not allowed here", arg),
                        self.make_note("previous named argument is here", prev_named_arg)
                    ]);
                }
                pos_arg_infos.push((arg_ctx, arg.get_line_info()));
            }
        }
        assert!(pos_arg_infos.len() + named_arg_infos.len() == args.len());
        self.resolve_call(ctx, pos_arg_infos, named_arg_infos, node.get_line_info())
    }

    fn resolve_call(
        &mut self,
        fun_ctx: Context,
        pos_arg_infos: Vec<(Context, LineInfo)>,
        named_arg_infos: IndexMap<String, (Context, LineInfo, LineInfo)>,
        call_line_info: LineInfo,
    ) -> CompileResult<Context> {
        // Accumulate errors
        let mut errs = CompileError::Errors(Vec::new());
        // If the function scope can be resolved and is a lvalue
        let scope_id = match fun_ctx.value {
            context::Value::GetGlobal { line_info: _, scope_id }
            | context::Value::GetLocal { line_info: _, scope_id } => Some(scope_id),
            _ => None,
        };
        if let Some(scope_id) = scope_id {
            let Payload::Function(ref data) = self.get_scope(&scope_id).payload else {
                unreachable!("probably some analyzer bug");
            };
            // Check argument count
            let arg_count = pos_arg_infos.len() + named_arg_infos.len();
            let total_param_count = data.get_total_param_count();
            if data.has_default_params() {
                let min_param_count = data.get_min_param_count();
                if arg_count < min_param_count || arg_count > total_param_count {
                    errs.push_err(self.make_err(
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
                    errs.push_err(self.make_err(
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
            let param_table = &data.param_table;
            let mut args_info = IndexMap::new();
            // Check positional argument expression types
            for (i, (arg_ctx, arg_line_info)) in pos_arg_infos.into_iter().enumerate() {
                let result = param_table.get_index(i).unwrap();
                let param_name = result.0;
                let param_scope_id = result.1;
                let Payload::Param(ref param) = self.get_scope(param_scope_id).payload else {
                    unreachable!("probably some analyzer bug");
                };
                let lhs = param.taipe.clone();
                let lhs_line_info = param.line_info;
                let rhs = arg_ctx;
                let rhs_line_info = arg_line_info;
                let mut ctx = match self.resolve_assign(Some((lhs, lhs_line_info)), None, Some((rhs, rhs_line_info))) {
                    Ok(it) => it,
                    Err(err) => {
                        errs.push_err(err);
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
                let Some(param_scope_id) = self.get_scope(&scope_id).children.get(&name) else {
                    let searched_names = param_table.keys().cloned().collect::<HashSet<_>>();
                    return Err(errors![
                        self.make_err(format!("unknown argument: '{}'", name), &arg_line_info),
                        self.make_did_you_mean_help(&name, &searched_names)
                    ]);
                };
                let Payload::Param(ref param) = self.get_scope(param_scope_id).payload else {
                    unreachable!("probably some analyzer bug");
                };
                let lhs = param.taipe.clone();
                let lhs_line_info = param.line_info;
                let rhs = arg_ctx;
                let rhs_line_info = arg_expr_info;
                let mut ctx = match self.resolve_assign(Some((lhs, lhs_line_info)), None, Some((rhs, rhs_line_info))) {
                    Ok(it) => it,
                    Err(err) => {
                        errs.push_err(err);
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
                    errs.push_err(self.make_err("duplicate named argument", &arg_line_info));
                    errs.push_err(self.make_note("previous positional argument is here", &line_info));
                }
            }
            let mut args_info = args_info
                .into_iter()
                .map(|(name, (ctx, _))| (name, ctx))
                .collect::<IndexMap<_, _>>();
            // Check if any value is left out
            for name in param_table.keys() {
                let param_scope_id = self.get_scope(&scope_id).children.get(name).unwrap();
                let Payload::Param(ref param) = self.get_scope(param_scope_id).payload else {
                    unreachable!("probably some analyzer bug");
                };
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
                        errs.push_err(self.make_err(format!("value of argument '{}' is not provided", name), &call_line_info));
                        errs.push_err(self.make_note("declared here", &param.line_info));
                    }
                }
            }
            // Return the accumulated errors
            if !errs.is_empty() {
                return Err(errs);
            }
            println!("Call to function {}: {}", self.get_scope(&scope_id).id.sym_path, fun_ctx.taipe);
            let line_info = call_line_info.begin();
            println!(
                "    at {}:{}:{}",
                self.get_current_src_path(),
                line_info.line_start,
                line_info.col_start
            );
            for (name, arg_ctx) in args_info.iter() {
                println!("  Argument => {}: {}", name, arg_ctx)
            }
            println!();
            let context::Type::Function {
                ret: return_type,
                params: _,
            } = fun_ctx.taipe
            else {
                unreachable!("probably some analyzer bug")
            };
            Ok(Context {
                is_lvalue: false,
                taipe: (*return_type).clone(),
                value: context::Value::DirectCall {
                    line_info: call_line_info,
                    fun_scope_id: scope_id,
                    args: args_info,
                },
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
        lhs: &mut Context,
        left: &'a ast::Expr,
        rhs: &mut Context,
        right: &'a ast::Expr,
    ) -> CompileResult<()> {
        self.resolve_value_promotion_impl(lhs, left, rhs, right, true)
    }

    fn resolve_value_promotion_impl(
        &self,
        lhs: &mut Context,
        left: &'a ast::Expr,
        rhs: &mut Context,
        right: &'a ast::Expr,
        should_check_another_time: bool,
    ) -> CompileResult<()> {
        if lhs.taipe.is_varint() && rhs.taipe.is_varint() {
            lhs.taipe = self.type_int.clone();
            rhs.taipe = self.type_int.clone();
            let context::Value::Imm(ref lhs_value) = lhs.value else {
                unreachable!("probably some analyzer bug");
            };
            let context::Value::Imm(ref rhs_value) = rhs.value else {
                unreachable!("probably some analyzer bug");
            };
            lhs.value = context::Value::Imm(self.transform_varint_to_int(lhs_value, left)?);
            rhs.value = context::Value::Imm(self.transform_varint_to_int(rhs_value, right)?);
            Ok(())
        } else if lhs.taipe.is_varint() {
            if rhs.taipe.is_integer() || rhs.taipe.is_float() {
                let context::Value::Imm(ref lhs_value) = lhs.value else {
                    unreachable!("probably some analyzer bug");
                };
                // Convert varint to respective type if it is worth it
                lhs.value = context::Value::Imm(self.transform_varint(&rhs.taipe, lhs_value, left, None)?);
                lhs.taipe = rhs.taipe.clone();
                return Ok(());
            }
            Ok(())
        } else if should_check_another_time {
            self.resolve_value_promotion_impl(rhs, right, lhs, left, false)
        } else {
            Ok(())
        }
    }

    fn visit_binary(&mut self, left: &'a ast::Expr, op: &Token, right: &'a ast::Expr) -> CompileResult<Context> {
        let line_info = LineInfo::from_range(left, right);
        let mut lhs = self.visit_expr(left)?;
        let mut rhs = self.visit_expr(right)?;

        macro_rules! return_err {
            () => {
                return Err(self.make_err(
                    format!(
                        "cannot apply '{}' operator on values of types '{}' and '{}'",
                        &op.text, lhs.taipe, rhs.taipe
                    ),
                    &line_info,
                ));
            };
            (integer_overflow) => {
                return Err(self.make_err(
                    format!(
                        "detected integer overflow: '{}' {} '{}'",
                        lhs.value.unwrap(),
                        &op.text,
                        rhs.value.unwrap()
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
                    value: context::Value::LogicAnd {
                        line_info,
                        lhs: Box::new(lhs),
                        rhs: Box::new(rhs),
                    },
                })
            }
            // Binary logical or operator
            //    result = (value1) or (value2)
            // Description:
            //    Returns the result of logical short-circuiting or of two bools
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
                    value: context::Value::LogicOr {
                        line_info,
                        lhs: Box::new(lhs),
                        rhs: Box::new(rhs),
                    },
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
                                    TokenKind::EqEq => context::Value::Eq {
                                        line_info,
                                        lhs: Box::new(lhs),
                                        rhs: Box::new(rhs),
                                    },
                                    TokenKind::LAngle => context::Value::Lt {
                                        line_info,
                                        lhs: Box::new(lhs),
                                        rhs: Box::new(rhs),
                                    },
                                    TokenKind::RAngle => context::Value::Gt {
                                        line_info,
                                        lhs: Box::new(lhs),
                                        rhs: Box::new(rhs),
                                    },
                                    TokenKind::LessEq => context::Value::Le {
                                        line_info,
                                        lhs: Box::new(lhs),
                                        rhs: Box::new(rhs),
                                    },
                                    TokenKind::GreaterEq => context::Value::Ge {
                                        line_info,
                                        lhs: Box::new(lhs),
                                        rhs: Box::new(rhs),
                                    },
                                    TokenKind::NotEq => context::Value::Ne {
                                        line_info,
                                        lhs: Box::new(lhs),
                                        rhs: Box::new(rhs),
                                    },
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
                        value: context::Value::BitAnd {
                            line_info,
                            lhs: Box::new(lhs),
                            rhs: Box::new(rhs),
                        },
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
                        value: context::Value::BitXor {
                            line_info,
                            lhs: Box::new(lhs),
                            rhs: Box::new(rhs),
                        },
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
                        value: context::Value::BitOr {
                            line_info,
                            lhs: Box::new(lhs),
                            rhs: Box::new(rhs),
                        },
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
                        return Err(self.make_err(format!("expected unsigned integer but got '{}'", rhs.taipe), right));
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
                        value: context::Value::Shl {
                            line_info,
                            lhs: Box::new(lhs),
                            rhs: Box::new(rhs),
                        },
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
                        return Err(self.make_err(format!("expected unsigned integer but got '{}'", rhs.taipe), right));
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
                        value: context::Value::Shr {
                            line_info,
                            lhs: Box::new(lhs),
                            rhs: Box::new(rhs),
                        },
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
                        value: context::Value::Add {
                            line_info,
                            lhs: Box::new(lhs),
                            rhs: Box::new(rhs),
                        },
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
                        value: context::Value::Sub {
                            line_info,
                            lhs: Box::new(lhs),
                            rhs: Box::new(rhs),
                        },
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
                        value: context::Value::Mul {
                            line_info,
                            lhs: Box::new(lhs),
                            rhs: Box::new(rhs),
                        },
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
                        value: context::Value::Div {
                            line_info,
                            lhs: Box::new(lhs),
                            rhs: Box::new(rhs),
                        },
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
                        value: context::Value::Rem {
                            line_info,
                            lhs: Box::new(lhs),
                            rhs: Box::new(rhs),
                        },
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

    fn visit_unary(&mut self, op: &Token, expr: &'a ast::Expr) -> CompileResult<Context> {
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
                        value: context::Value::Negate {
                            line_info: expr.get_line_info(),
                            ctx: Box::new(ctx),
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
                                ctx.taipe
                            ),
                            expr,
                        ));
                    }
                _ => {
                    return Err(self.make_err(format!("cannot apply '-' operator on type '{}'", ctx.taipe), expr));
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
                        value: context::Value::FlipBits {
                            line_info: expr.get_line_info(),
                            ctx: Box::new(ctx),
                        },
                    }),
                _ => {
                    return Err(self.make_err(format!("cannot apply '~' operator on type '{}'", ctx.taipe), expr));
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
                    value: context::Value::Deref {
                        line_info: expr.get_line_info(),
                        ctx: Box::new(ctx),
                    },
                }),
                _ => {
                    return Err(self.make_err(format!("cannot dereference type '{}'", ctx.taipe), expr));
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
                fn is_addressable(taipe: &context::Type) -> bool {
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
                    return Err(self.make_err(format!("cannot take address of value of type '{}'", ctx.taipe), expr));
                }
                if !ctx.is_lvalue {
                    return Err(self.make_err("cannot take address of a prvalue (pure rvalue)", expr));
                }
                assert!(!ctx.taipe.is_varint());
                Ok(Context {
                    is_lvalue: false,
                    taipe: context::Type::Pointer(Box::new(ctx.taipe.clone())),
                    value: context::Value::AddrOf {
                        line_info: expr.get_line_info(),
                        ctx: Box::new(ctx),
                    },
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
                fn is_sizeof_permitted(taipe: &context::Type) -> bool {
                    match taipe {
                        context::Type::VarInt => false,
                        context::Type::Const(taipe) => is_sizeof_permitted(taipe),
                        context::Type::Module | context::Type::Void | context::Type::Noreturn => false,
                        _ => true,
                    }
                }
                if !is_sizeof_permitted(&ctx.taipe) {
                    return Err(self.make_err(format!("cannot take sizeof value of type '{}'", ctx.taipe), expr));
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
                fn is_alignof_permitted(taipe: &context::Type) -> bool {
                    match taipe {
                        context::Type::VarInt => false,
                        context::Type::Const(taipe) => is_alignof_permitted(taipe),
                        context::Type::Module | context::Type::Void | context::Type::Noreturn => false,
                        _ => true,
                    }
                }
                if !is_alignof_permitted(&ctx.taipe) {
                    return Err(self.make_err(format!("cannot take alignof value of type '{}'", ctx.taipe), expr));
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
                fn is_typeof_permitted(taipe: &context::Type) -> bool {
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
                    return Err(self.make_err(format!("cannot use typeof operator on type '{}'", ctx.taipe), expr));
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
                    return Err(self.make_err(format!("cannot use not operator on type '{}'", ctx.taipe), expr));
                }
                Ok(Context {
                    is_lvalue: false,
                    taipe: context::Type::Bool,
                    value: context::Value::Not {
                        line_info: expr.get_line_info(),
                        ctx: Box::new(ctx),
                    },
                })
            }
            _ => unreachable!("probably some parser bug"),
        }
    }

    fn get_sizeof(&mut self, taipe: &context::Type, line_info: &impl HasLineInfo) -> CompileResult<usize> {
        Ok(self.resolve_layout(taipe, line_info)?.size)
    }

    fn get_alignof(&mut self, taipe: &context::Type, line_info: &impl HasLineInfo) -> CompileResult<usize> {
        Ok(self.resolve_layout(taipe, line_info)?.alignment)
    }

    // Type expression functions
    fn visit_type(&mut self, node: &'a ast::Type) -> CompileResult<context::Type> {
        match node {
            ast::Type::Path { items } => {
                let mut index = 0;
                let mut ctx = self.get_name(&items[index])?;
                index += 1;
                while index < items.len() {
                    let name = &items[index];
                    ctx = match ctx.taipe.remove_const() {
                        context::Type::Module => {
                            let context::Value::Imm(context::Imm::Module(module)) = ctx.value else {
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
                    debug!("line_info: {}", node.get_line_info());
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
                            self.warnings.push(self.make_warning(
                                format!(
                                    "'const' is redundant here, '{}' is always a constant",
                                    taipe
                                ),
                                token,
                            ));
                            self.warnings.push(self.make_help("remove const qualifier"));
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
                let length_ctx = self.compeval_trivial(&length_ctx)?;
                if !length_ctx.taipe.is_unsigned_integer() {
                    return Err(errors![
                        self.make_err("argument of index operator should be an unsigned integer type", expr),
                        self.make_note(format!("but got '{}'", length_ctx.taipe), expr),
                    ]);
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

    fn validate_fun_ret_type(&mut self, taipe: &context::Type, line_info: &impl HasLineInfo) -> CompileResult<()> {
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

    // Expression helpers
    
    fn get_default_value(&self, taipe: &context::Type, line_info: &impl HasLineInfo) -> CompileResult<Context> {
        self.get_default_value_impl(taipe, taipe, line_info)
    }

    fn get_default_value_impl(
        &self,
        top_type: &context::Type,
        cur_type: &context::Type,
        line_info: &impl HasLineInfo,
    ) -> CompileResult<Context> {
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
            _ => Err(errors![
                self.make_err(
                    format!("type does not have a default value: '{}'", top_type),
                    line_info,
                ),
                self.make_note_no_path(format!(
                    "error occured because this type does not have a default value: '{}'",
                    cur_type
                ))
            ])
        }
    }

    fn get_zero_value(&self, taipe: &context::Type, line_info: &impl HasLineInfo) -> CompileResult<Context> {
        self.get_zero_value_impl(taipe, taipe, line_info)
    }

    fn get_zero_value_impl(
        &self,
        top_type: &context::Type,
        cur_type: &context::Type,
        line_info: &impl HasLineInfo,
    ) -> CompileResult<Context> {
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
            _ => Err(errors![
                self.make_err(
                    format!("type does not have a zero value: '{}'", top_type),
                    line_info,
                ),
                self.make_note_no_path(format!(
                    "error occured because this type does not have a zero value: '{}'",
                    cur_type
                ))
            ]),
        }
    }
    
    /// This function resolves assignment by doing type checking.
    /// - In case of declaration, `eq_token` is the token that separates lhs and rhs.
    /// - In case of assignment, `eq_token` should always be None
    fn resolve_assign(
        &self,
        lhs: Option<(context::Type, LineInfo)>,
        eq_token: Option<&Token>,
        mut rhs: Option<(Context, LineInfo)>,
    ) -> CompileResult<Context> {
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
        &self,
        mut lhs: context::Type,
        lhs_line_info: LineInfo,
        mut rhs: Context,
        rhs_line_info: LineInfo,
        allow_assign_to_const: bool,
    ) -> CompileResult<Context> {
        macro_rules! return_err_const {
            () => {
                return Err(errors![
                    self.make_err(
                        format!("cannot assign to a constant of type: '{}'", lhs),
                        &lhs_line_info,
                    ),
                    self.make_note(format!("type of value is '{}'", rhs), &rhs_line_info)
                ]);
            };
        }
        macro_rules! return_err {
            () => {
                return Err(errors![
                    self.make_err(
                        format!("cannot assign value of type '{}'", rhs),
                        &rhs_line_info,
                    ),
                    self.make_note(format!("cannot assign to '{}'", lhs), &lhs_line_info)
                ]);
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

    // Value transformations

    fn usize2usize(&self, val: usize, line_info: &impl HasLineInfo) -> CompileResult<Context> {
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
    
    fn transform_imm(
        &self,
        lhs: &context::Type,
        rhs: &context::Imm,
        line_info: &impl HasLineInfo,
        type_name: Option<&str>,
    ) -> CompileResult<context::Imm> {
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
        value: &context::Imm,
        line_info: &impl HasLineInfo,
    ) -> CompileResult<context::Imm> {
        self.transform_imm(&self.type_usize, value, line_info, Some("usize"))
    }

    fn transform_varint(
        &self,
        lhs: &context::Type,
        rhs: &context::Imm,
        line_info: &impl HasLineInfo,
        type_name: Option<&str>,
    ) -> CompileResult<context::Imm> {
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
        value: &context::Imm,
        line_info: &impl HasLineInfo,
    ) -> CompileResult<context::Imm> {
        self.transform_varint(&self.type_usize, value, line_info, Some("usize"))
    }

    fn transform_varint_to_int(
        &self,
        value: &context::Imm,
        line_info: &impl HasLineInfo,
    ) -> CompileResult<context::Imm> {
        self.transform_varint(&self.type_int, value, line_info, Some("int"))
    }

    fn get_member(&mut self, scope_id: &ScopeId, name: &Token) -> CompileResult<Context> {
        let mut searched_names = HashSet::new();
        if let Some(ctx) = self.resolve_member(scope_id, &name.text, name.get_line_info(), &mut searched_names)? {
            Ok(ctx)
        } else {
            Err(errors![
                self.make_err(
                    format!(
                        "'{}' has no member named '{}'",
                        self.get_scope(scope_id).id.sym_path,
                        &name.text
                    ),
                    name,
                ),
                self.make_did_you_mean_help(&name.text, &searched_names)
            ])
        }
    }

    fn resolve_member(
        &mut self,
        scope_id: &ScopeId,
        name: &str,
        line_info: LineInfo,
        searched_names: &mut HashSet<String>,
    ) -> CompileResult<Option<Context>> {
        if let Some(child_id) = self.get_scope(scope_id).children.get(name) {
            // Get the scope id of the evaluated child scope
            let child_id = match self.get_scope_eval_state(child_id) {
                ScopeEvalState::NotVisited(scope_node) => match scope_node {
                    ScopeNode::Decl(decl) => {
                        // Begin new scope
                        self.push_current_scope(scope_id);
                        // Visit the decl
                        let child_id = self.visit_decl(decl)?;
                        self.pop_current_scope();
                        child_id
                    },
                    ScopeNode::Object(_) => unreachable!("probably some analyzer bug"),
                },
                ScopeEvalState::VisitInProgress => {
                    return Err(CompileError::SemCyclic {
                        file_path: self.get_src_path_of_scope(child_id),
                        line_info: self.get_scope(child_id).get_line_info(),
                    });
                },
                ScopeEvalState::Visited => child_id.clone(),
            };
            Ok(Some(match &self.get_scope(&child_id).payload {
                Payload::Compound(_) => Context {
                    is_lvalue: true,
                    taipe: context::Type::Typedef,
                    value: context::Value::Imm(context::Imm::Type(context::Type::Basic(child_id))),
                },
                Payload::Typedef(taipe) => Context {
                    is_lvalue: true,
                    taipe: context::Type::Typedef,
                    value: context::Value::Imm(context::Imm::Type(taipe.clone())),
                },
                Payload::Function(_) | Payload::Global(_) | Payload::Local(_) | Payload::Param(_) | Payload::None => {
                    if self.get_scope(&child_id).is_module() {
                        return Ok(Some(Context {
                            is_lvalue: true,
                            taipe: context::Type::Module,
                            value: context::Value::from_module(child_id),
                        }));
                    }
                    if self.is_global(&child_id) {
                        Context {
                            is_lvalue: true,
                            taipe: self.get_scope(&child_id).get_type().clone(),
                            value: context::Value::GetGlobal {
                                line_info,
                                scope_id: child_id,
                            },
                        }
                    } else {
                        assert!(self.is_local(&child_id));
                        Context {
                            is_lvalue: true,
                            taipe: self.get_scope(&child_id).get_type().clone(),
                            value: context::Value::GetLocal {
                                line_info,
                                scope_id: child_id,
                            },
                        }
                    }
                },
                Payload::Block(_) => panic!("accessing block members not allowed"),
                Payload::LayoutResolutionInProgress => unreachable!("probably some analyzer bug"),
            }))
        } else {
            // For better errors
            for name in self.get_scope(scope_id).children.keys() {
                searched_names.insert(name.clone());
            }
            Ok(None)
        }
    }

    fn get_name(&mut self, name: &Token) -> CompileResult<Context> {
        let mut searched_names = HashSet::new();
        if let Some(ctx) = self.resolve_name(&name.text, name.get_line_info(), &mut searched_names)? {
            Ok(ctx)
        } else {
            Err(errors![
                self.make_err("undefined reference", name),
                self.make_did_you_mean_help(&name.text, &searched_names)
            ])
        }
    }

    fn resolve_name(
        &mut self,
        name: &str,
        line_info: LineInfo,
        searched_names: &mut HashSet<String>,
    ) -> CompileResult<Option<Context>> {
        // Check in the current scope and go upwards
        let mut scope_id = self.get_current_scope_id().clone();
        let mut inner_fn: Option<ScopeId> = None;
        loop {
            match self.resolve_member(&scope_id, name, line_info, searched_names) {
                Ok(Some(ctx)) => {
                    if ctx.taipe.is_typedef() {
                        // Typedef is encoded by Type::Basic so ignore that case
                        return Ok(Some(ctx));
                    } else {
                        let scope_id = match ctx.value {
                            context::Value::Imm(context::Imm::Module(ref scope_id)) => scope_id,
                            context::Value::GetGlobal { line_info: _, ref scope_id } => scope_id,
                            context::Value::GetLocal { line_info: _, ref scope_id } => scope_id,
                            _ => unreachable!("probably some bug in resolve_member"),
                        };

                        if let Some(inner_fn) = inner_fn {
                            let scope = self.get_scope(scope_id);
                            if scope.is_variable()
                                && let Some(outer_fn) = self.get_enclosing_function(scope_id)
                            {
                                return Err(errors![
                                    self.make_err(
                                        "cannot use local variable of outer function from inner function context",
                                        &line_info,
                                    ),
                                    self.make_note("variable is declared here", scope),
                                    self.make_note("inner function is declared here", self.get_scope(&inner_fn)),
                                    self.make_note("outer function is declared here", self.get_scope(&outer_fn))
                                ]);
                            }
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
            if self.get_scope(&scope_id).is_function() {
                inner_fn = Some(scope_id.clone());
            }
            if let Some(ref parent) = self.get_scope(&scope_id).parent {
                scope_id = parent.clone();
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

    // ------------------------------------------------------------
    // Scope operations
    // ------------------------------------------------------------

    /// Returns a reference to the current scope
    fn push_current_scope(&mut self, scope_id: &ScopeId) {
        self.current_scope_stack.push(scope_id.clone());
    }

    fn pop_current_scope(&mut self) {
        self.current_scope_stack.pop();
    }
    
    fn get_current_scope_id(&self) -> &ScopeId {
        self.current_scope_stack.last().unwrap()
    }
    
    fn get_current_scope(&self) -> &Scope {
        self.get_scope(&self.get_current_scope_id())
    }

    fn get_current_block(&self) -> Option<&Scope> {
        let scope = self.get_current_scope();
        if scope.is_block() {
            Some(scope)
        } else {
            if let Some(scope_id) = self.get_enclosing_block(self.get_current_scope_id()) {
                Some(self.get_scope(&scope_id))
            } else { None }
        }
    }

    fn get_current_block_mut(&mut self) -> Option<&mut Scope> {
        let id = self.get_current_block()?.id.clone();
        Some(self.get_scope_mut(&id))
    }
    
    fn get_current_function(&self) -> Option<&Scope> {
        let scope = self.get_current_scope();
        if scope.is_function() {
            Some(scope)
        } else {
            if let Some(scope_id) = self.get_enclosing_function(self.get_current_scope_id()) {
                Some(self.get_scope(&scope_id))
            } else { None }
        }
    }

    fn get_current_function_mut(&mut self) -> Option<&mut Scope> {
        let id = self.get_current_function()?.id.clone();
        Some(self.get_scope_mut(&id))
    }

    /// Returns a reference to the scope given the scope id
    fn get_scope(&self, scope_id: &ScopeId) -> &Scope {
        if let Some(scope) = self.scope_pool.get(scope_id) {
            scope
        } else {
            panic!("invalid scope id")
        }
    }

    fn get_scope_mut(&mut self, scope_id: &ScopeId) -> &mut Scope {
        if let Some(scope) = self.scope_pool.get_mut(scope_id) {
            scope
        } else {
            panic!("invalid scope id")
        }
    }

    fn get_enclosing_block(&self, scope_id: &ScopeId) -> Option<ScopeId> {
        if let Some(ref parent) = self.get_scope(scope_id).parent {
            if self.get_scope(parent).is_block() {
                Some(parent.clone())
            } else {
                self.get_enclosing_block(parent)
            }
        } else { None }
    }

    fn get_enclosing_function(&self, scope_id: &ScopeId) -> Option<ScopeId> {
        if let Some(ref parent) = self.get_scope(scope_id).parent {
            if self.get_scope(parent).is_function() {
                Some(parent.clone())
            } else {
                self.get_enclosing_function(parent)
            }
        } else { None }
    }

    /// Returns the evaluation state of the specified scope
    fn get_scope_eval_state(&self, scope_id: &ScopeId) -> ScopeEvalState<'a> {
        if let Some(eval_state) = self.scope_eval_state_table.get(scope_id) {
            *eval_state
        } else {
            panic!("invalid scope id")
        }
    }

    /// Sets the evaluation state of the specified scope
    fn set_scope_eval_state(&mut self, scope_id: &ScopeId, eval_state: ScopeEvalState<'a>) {
        self.scope_eval_state_table.insert(scope_id.clone(), eval_state);
    }

    fn is_global(&mut self, scope_id: &ScopeId) -> bool {
        self.get_enclosing_function(scope_id).is_none()
    }

    fn is_local(&mut self, scope_id: &ScopeId) -> bool {
        self.get_enclosing_function(scope_id).is_some()
    }

    fn use_current_function_data<F, T>(&self, handler: F) -> T
    where
        F: FnOnce(&FunctionInfo) -> T,
    {
        let function = self.get_current_function().expect("not in a function");
        let Payload::Function(ref data) = function.payload else {
            unreachable!("probably some analyzer bug");
        };
        handler(data)
    }

    fn mut_current_function_data<F, T>(&mut self, handler: F) -> T
    where
        F: FnOnce(&mut FunctionInfo) -> T,
    {
        let function = self.get_current_function_mut().expect("not in a function");
        let Payload::Function(ref mut data) = function.payload else {
            unreachable!("probably some analyzer bug");
        };
        handler(data)
    }

    fn use_current_block_data<F, T>(&self, handler: F) -> T
    where
        F: FnOnce(&BlockInfo) -> T,
    {
        let block = self.get_current_block().expect("not in a block");
        let Payload::Block(ref data) = block.payload else {
            unreachable!("probably some analyzer bug");
        };
        handler(data)
    }

    fn mut_current_block_data<F, T>(&mut self, handler: F) -> T
    where
        F: FnOnce(&mut BlockInfo) -> T,
    {
        let block = self.get_current_block_mut().expect("not in a block");
        let Payload::Block(ref mut data) = block.payload else {
            unreachable!("probably some analyzer bug");
        };
        handler(data)
    }

    /// Adds a child scope to `parent` with the specified parameters
    fn add_child_scope(&mut self, parent: &ScopeId, kind: ScopeKind, name: &str, eval_state: ScopeEvalState<'a>, payload: Payload, line_info: &impl HasLineInfo) -> ScopeId {
        // Create the symbol path and id
        let mut sym_path = self.get_scope(parent).id.sym_path.clone();
        sym_path.push_name(name);
        let id = ScopeId { index: self.scope_pool.len(), sym_path };
        // Create the child scope
        let child = Scope {
            id: id.clone(),
            kind,
            file_path: None,
            name: name.to_string(),
            line_info: line_info.get_line_info(),
            payload,
            parent: Some(parent.clone()),
            children: IndexMap::new(),
            unique_counter: AtomicU64::new(0),
            block_counter: AtomicU64::new(0),
            loop_counter: AtomicU64::new(0),
        };
        // Add to the scope pool
        self.scope_pool.insert(id.clone(), child);
        // Add to children of the parent scope
        self.get_scope_mut(parent).children.insert(name.to_string(), id.clone());
        // Set eval state
        self.set_scope_eval_state(&id, eval_state);
        // Return the id
        id
    }

    // ------------------------------------------------------------
    // Error operations
    // ------------------------------------------------------------
    
    /// Returns the source file path of the given scope
    fn get_src_path_of_scope(&self, scope_id: &ScopeId) -> String {
        let scope = self.get_scope(scope_id);
        if let Some(ref path) = scope.file_path {
            path.clone()
        } else if let Some(ref parent_id) = scope.parent {
            self.get_src_path_of_scope(parent_id)
        } else {
            panic!("all scopes must designated to some source file")
        }
    }

    /// Returns the source file path of the current scope
    fn get_current_src_path(&self) -> String {
        self.get_src_path_of_scope(self.get_current_scope_id())
    }
    
    fn make_err(&self, msg: impl ToString, obj: &impl HasLineInfo) -> CompileError {
        CompileError::SemError {
            file_path: self.get_current_src_path(),
            line_info: obj.get_line_info(),
            msg: msg.to_string(),
        }
    }

    fn make_warning(&self, msg: impl ToString, obj: &impl HasLineInfo) -> CompileError {
        CompileError::SemWarning {
            file_path: self.get_current_src_path(),
            line_info: obj.get_line_info(),
            msg: msg.to_string(),
        }
    }

    fn make_note(&self, msg: impl ToString, obj: &impl HasLineInfo) -> CompileError {
        self.make_note_with_path(msg, self.get_current_src_path(), obj)
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

    fn make_help(&self, msg: impl ToString) -> CompileError {
        CompileError::SemHelp { msg: msg.to_string() }
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
}
