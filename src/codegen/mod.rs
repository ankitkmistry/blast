use std::{cell::RefCell, collections::HashMap, fs::File, io::Write, rc::Rc};

use cranelift::codegen;
use cranelift::prelude::{self as cl, Configurable, FunctionBuilder, InstBuilder, types};
use cranelift_module::{Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};
use log::{debug, info};

use crate::context::Context;
use crate::scope::{Scope, SymbolPath};
use crate::{context, scope};

#[derive(Clone)]
struct FunData {
    id: cranelift_module::FuncId,
    signature: cl::Signature,
}

struct Emitter<'a, 'b> {
    roots: HashMap<String, Rc<RefCell<Scope<'a>>>>,
    module: &'b mut ObjectModule,
    fun_datas: HashMap<SymbolPath, FunData>,
}

impl<'a, 'b> Emitter<'a, 'b> {
    pub fn emit(&mut self) {
        // Forward declare all functions
        for root in self.roots.values() {
            forward_declare_all_funs(&mut self.module, &mut self.fun_datas, root);
        }
        // Now define them
        for root in self.roots.values() {
            define_all_funs(&mut self.module, &self.fun_datas, root);
        }
    }
}

fn gen_imm<'a>(imm: &context::Imm<'a>, builder: &mut cl::FunctionBuilder, module: &ObjectModule) -> codegen::ir::Value {
    match imm {
        context::Imm::Bool(b) => builder.ins().iconst(types::I8, if *b { 1 } else { 0 }),
        context::Imm::Char(c) => builder.ins().iconst(types::I32, *c as u32 as i64),
        context::Imm::Int8(v) => builder.ins().iconst(types::I8, *v as i64),
        context::Imm::Int16(v) => builder.ins().iconst(types::I16, *v as i64),
        context::Imm::Int32(v) => builder.ins().iconst(types::I32, *v as i64),
        context::Imm::Int64(v) => builder.ins().iconst(types::I64, *v as i64),
        context::Imm::Int128(v) => builder.ins().iconst(types::I128, *v as i64),
        context::Imm::Uint8(v) => builder.ins().iconst(types::I8, *v as i64),
        context::Imm::Uint16(v) => builder.ins().iconst(types::I16, *v as i64),
        context::Imm::Uint32(v) => builder.ins().iconst(types::I32, *v as i64),
        context::Imm::Uint64(v) => builder.ins().iconst(types::I64, *v as i64),
        context::Imm::Uint128(v) => builder.ins().iconst(types::I128, *v as i64),
        context::Imm::Float32(v) => builder.ins().f32const(*v),
        context::Imm::Float64(v) => builder.ins().f64const(*v),
        context::Imm::Nil => builder.ins().iconst(module.isa().pointer_type(), 0),
        _ => unreachable!("probably some analyzer bug"),
    }
}

fn gen_ctx<'a>(
    ctx: &Context<'a>,
    builder: &mut cl::FunctionBuilder,
    module: &ObjectModule,
) -> Option<codegen::ir::Value> {
    match &ctx.value {
        context::Value::Imm(imm) => Some(gen_imm(imm, builder, module)),
        context::Value::Array(values) => todo!(),
        context::Value::Tuple(values) => todo!(),
        context::Value::Reference(ref_cell) => todo!(),
        context::Value::Negate { line_info, ctx } => {
            let value = gen_ctx(ctx, builder, module);
            if let Some(value) = value {
                if ctx.taipe.is_float() {
                    Some(builder.ins().fneg(value))
                } else {
                    Some(builder.ins().ineg(value))
                }
            } else {
                None
            }
        }
        context::Value::FlipBits { line_info, ctx } => {
            let value = gen_ctx(ctx, builder, module);
            if let Some(value) = value {
                Some(builder.ins().bnot(value))
            } else {
                None
            }
        }
        context::Value::Deref { line_info, ctx } => todo!(),
        context::Value::AddrOf { line_info, ctx } => todo!(),
        context::Value::Not { line_info, ctx } => {
            // z -> nz
            // nz -> z
            todo!()
        }
        context::Value::Add { line_info, lhs, rhs } => {
            let lhs = gen_ctx(lhs, builder, module);
            let rhs = gen_ctx(rhs, builder, module);
            if let Some(lhs) = lhs
                && let Some(rhs) = rhs
            {
                Some(builder.ins().iadd(lhs, rhs))
            } else {
                None
            }
        }
        context::Value::Sub { line_info, lhs, rhs } => {
            let lhs = gen_ctx(lhs, builder, module);
            let rhs = gen_ctx(rhs, builder, module);
            if let Some(lhs) = lhs
                && let Some(rhs) = rhs
            {
                Some(builder.ins().isub(lhs, rhs))
            } else {
                None
            }
        }
        context::Value::Mul { line_info, lhs, rhs } => {
            let lhs = gen_ctx(lhs, builder, module);
            let rhs = gen_ctx(rhs, builder, module);
            if let Some(lhs) = lhs
                && let Some(rhs) = rhs
            {
                Some(builder.ins().imul(lhs, rhs))
            } else {
                None
            }
        }
        context::Value::Div { line_info, lhs, rhs } => {
            todo!()
        }
        context::Value::Rem { line_info, lhs, rhs } => {
            todo!()
        }
        context::Value::Shl { line_info, lhs, rhs } => {
            let lhs = gen_ctx(lhs, builder, module);
            let rhs = gen_ctx(rhs, builder, module);
            if let Some(lhs) = lhs
                && let Some(rhs) = rhs
            {
                Some(builder.ins().ishl(lhs, rhs))
            } else {
                None
            }
        }
        context::Value::Shr { line_info, lhs, rhs } => {
            let lhs_type = &lhs.taipe;
            let lhs = gen_ctx(lhs, builder, module);
            let rhs = gen_ctx(rhs, builder, module);
            if let Some(lhs) = lhs
                && let Some(rhs) = rhs
            {
                if lhs_type.is_unsigned_integer() {
                    Some(builder.ins().ushr(lhs, rhs))
                } else {
                    Some(builder.ins().sshr(lhs, rhs))
                }
            } else {
                None
            }
        }
        context::Value::BitAnd { line_info, lhs, rhs } => {
            let lhs = gen_ctx(lhs, builder, module);
            let rhs = gen_ctx(rhs, builder, module);
            if let Some(lhs) = lhs
                && let Some(rhs) = rhs
            {
                Some(builder.ins().band(lhs, rhs))
            } else {
                None
            }
        }
        context::Value::BitXor { line_info, lhs, rhs } => {
            let lhs = gen_ctx(lhs, builder, module);
            let rhs = gen_ctx(rhs, builder, module);
            if let Some(lhs) = lhs
                && let Some(rhs) = rhs
            {
                Some(builder.ins().bxor(lhs, rhs))
            } else {
                None
            }
        }
        context::Value::BitOr { line_info, lhs, rhs } => {
            let lhs = gen_ctx(lhs, builder, module);
            let rhs = gen_ctx(rhs, builder, module);
            if let Some(lhs) = lhs
                && let Some(rhs) = rhs
            {
                Some(builder.ins().bor(lhs, rhs))
            } else {
                None
            }
        }
        context::Value::Lt { line_info, lhs, rhs } => todo!(),
        context::Value::Le { line_info, lhs, rhs } => todo!(),
        context::Value::Eq { line_info, lhs, rhs } => todo!(),
        context::Value::Ne { line_info, lhs, rhs } => todo!(),
        context::Value::Ge { line_info, lhs, rhs } => todo!(),
        context::Value::Gt { line_info, lhs, rhs } => todo!(),
        context::Value::LogicAnd { line_info, lhs, rhs } => todo!(),
        context::Value::LogicOr { line_info, lhs, rhs } => todo!(),
        context::Value::Index(context, context1) => todo!(),
        context::Value::Call(ref_cell, index_map) => todo!(),
        context::Value::Assign(contexts, contexts1) => todo!(),
        context::Value::IfElse(context, context1, context2) => todo!(),
        context::Value::If(context, context1) => todo!(),
        context::Value::While(context, context1) => todo!(),
        context::Value::Block(ctxs) => {
            let block = builder.create_block();
            builder.switch_to_block(block);
            builder.seal_block(block);
            for ctx in ctxs {
                gen_ctx(ctx, builder, module);
            }
            None
        }
        context::Value::Ret(ctx) => {
            let value = gen_ctx(ctx, builder, module);
            if let Some(value) = value {
                builder.ins().return_(&[value]);
            } else {
                builder.ins().return_(&[]);
            }
            None
        }
        context::Value::Eval(context) => todo!(),
        context::Value::RetVoid => todo!(),
        context::Value::Cast(context) => todo!(),
    }
}

fn define_fun<'a>(scope: &Scope<'a>, builder: &mut cl::FunctionBuilder, module: &ObjectModule) {
    let scope::State::Visited(ctx) = &scope.children.get("block0$").unwrap().borrow().state else {
        unreachable!("probably some analyzer bug");
    };

    gen_ctx(ctx, builder, module);
}

fn define_all_funs<'a>(
    module: &mut ObjectModule,
    fun_sigs: &HashMap<SymbolPath, FunData>,
    scope: &Rc<RefCell<Scope<'a>>>,
) {
    let mut ctx = codegen::Context::new();
    let mut fctx = cl::FunctionBuilderContext::new();
    define_all_funs_impl(module, fun_sigs, scope, &mut ctx, &mut fctx)
}

fn define_all_funs_impl<'a>(
    module: &mut ObjectModule,
    fun_sigs: &HashMap<SymbolPath, FunData>,
    scope_rc: &Rc<RefCell<Scope<'a>>>,
    ctx: &mut codegen::Context,
    fctx: &mut cl::FunctionBuilderContext,
) {
    let scope = scope_rc.borrow();
    if scope.is_function() {
        let Some(fun_data) = fun_sigs.get(&scope.sym_path).cloned() else {
            unreachable!("probably some codegen bug");
        };
        {
            let mut builder = cl::FunctionBuilder::new(&mut ctx.func, fctx);
            builder.func.signature = fun_data.signature;

            define_fun(&*scope, &mut builder, module);

            codegen::verify_function(&builder.func, module.isa()).unwrap();
            builder.finalize();
            print!("fun {}:\n{}", &scope.sym_path, &ctx.func);

            module.define_function(fun_data.id, ctx).unwrap();
            ctx.clear();
        }
        debug!("Defined function: {}", scope.sym_path);
    }
    for child in scope.children.values() {
        define_all_funs(module, fun_sigs, child);
    }
}

fn forward_declare_all_funs<'a>(
    module: &mut ObjectModule,
    fun_sigs: &mut HashMap<SymbolPath, FunData>,
    scope: &Rc<RefCell<Scope<'a>>>,
) {
    let scope = scope.borrow();
    if scope.is_function() {
        let scope::State::Visited(ctx) = &scope.state else {
            unreachable!("probably some analyzer bug");
        };
        let context::Type::Function { ret, params } = &ctx.taipe else {
            unreachable!("probably some analyzer bug");
        };
        let sig = make_fun_sig(module, ret, params);
        let sym_path = scope.sym_path.clone();
        let mangled_name = sym_path.to_string();
        // TODO: allow different kind of linkage
        let fun_id = module.declare_function(&mangled_name, Linkage::Export, &sig).unwrap();
        debug!("Declared function: {}", sym_path);
        fun_sigs.insert(
            sym_path,
            FunData {
                id: fun_id,
                signature: sig,
            },
        );
    }
    for child in scope.children.values() {
        forward_declare_all_funs(module, fun_sigs, child);
    }
}

// HELPER LOGIC

fn get_cl_type<'a>(module: &ObjectModule, taipe: &context::Type<'a>) -> cl::Type {
    match taipe {
        context::Type::Bool => types::I8,
        context::Type::Char => types::I32,
        context::Type::Int8 => types::I8,
        context::Type::Int16 => types::I16,
        context::Type::Int32 => types::I32,
        context::Type::Int64 => types::I64,
        context::Type::Int128 => types::I128,
        context::Type::Uint8 => types::I8,
        context::Type::Uint16 => types::I16,
        context::Type::Uint32 => types::I32,
        context::Type::Uint64 => types::I64,
        context::Type::Uint128 => types::I128,
        context::Type::Float32 => types::F32,
        context::Type::Float64 => types::F64,
        context::Type::Const(taipe) => get_cl_type(module, taipe),
        context::Type::Basic(ref_cell) => todo!(),
        context::Type::Function { ret, params } => todo!(),
        context::Type::Pointer(_) => module.isa().pointer_type(),
        context::Type::Array { count, taipe } => todo!(),
        context::Type::Fat(_) => todo!(),
        context::Type::Tuple(items) => todo!(),
        _ => unreachable!("probably some analyzer bug"),
    }
}

fn make_fun_sig<'a>(module: &ObjectModule, ret: &context::Type<'a>, params: &[context::Param<'a>]) -> cl::Signature {
    let call_conv = module.isa().default_call_conv();
    let mut cl_params = Vec::new();
    for param in params {
        cl_params.push(cl::AbiParam::new(get_cl_type(module, &param.taipe)));
    }
    cl::Signature {
        params: cl_params,
        returns: if ret.is_void() {
            vec![]
        } else {
            vec![cl::AbiParam::new(get_cl_type(module, ret))]
        },
        call_conv,
    }
}

pub fn generate_code<'a>(filename: &str, roots: HashMap<String, Rc<RefCell<Scope<'a>>>>) {
    info!("--- codegen ---");
    // Setup ISA
    let isa = {
        let mut builder = cl::settings::builder();
        builder.set("opt_level", "none").unwrap();
        builder.enable("is_pic").unwrap();

        let flags = cl::settings::Flags::new(builder);
        cl::isa::lookup(target_lexicon::HOST).unwrap().finish(flags).unwrap()
    };
    info!("Target triple: {}", isa.triple());
    info!("Selected ISA: {}", isa.name());
    info!("Machine endianness: {:?}", isa.endianness());
    info!("Pointer size: {}", isa.pointer_bytes());
    info!("Default calling convention: {}", isa.default_call_conv());
    // Setup object module
    let mut module = {
        let name: Vec<u8> = filename.bytes().collect();
        let libcall_names = cranelift_module::default_libcall_names();
        let builder = ObjectBuilder::new(isa, name, libcall_names).unwrap();
        ObjectModule::new(builder)
    };
    let mut emitter = Emitter {
        module: &mut module,
        fun_datas: HashMap::new(),
        roots,
    };
    emitter.emit();
    // Do work
    // Finish compilation
    let product = module.finish();
    // Generate the object file
    let bytes = product.emit().unwrap();
    let fname = format!("{filename}.o");
    let mut f = File::create(&fname).unwrap();
    f.write_all(&bytes).unwrap();
    info!("Wrote binary output to {fname}");
}

fn main_fn_sign(isa: &dyn cl::isa::TargetIsa) -> cl::Signature {
    let call_conv = isa.default_call_conv();
    cl::Signature {
        params: Vec::new(),
        returns: vec![cl::AbiParam::new(types::I32)],
        call_conv,
    }
}

pub fn example_output_program() {
    // Refer to: https://github.com/simvux/cranelift-examples/blob/master/examples/output-a-binary/main.rs

    println!("--- codegen ---");

    let isa = {
        let mut builder = cl::settings::builder();
        builder.set("opt_level", "none").unwrap();
        builder.enable("is_pic").unwrap();

        let flags = cl::settings::Flags::new(builder);
        cl::isa::lookup(target_lexicon::HOST).unwrap().finish(flags).unwrap()
    };

    let mut module = {
        let name = b"hello";
        let libcall_names = cranelift_module::default_libcall_names();
        let builder = ObjectBuilder::new(isa.clone(), name, libcall_names).unwrap();
        ObjectModule::new(builder)
    };

    let main_decl = {
        let sig: cl::Signature = main_fn_sign(&*isa);
        module.declare_function("main", Linkage::Export, &sig).unwrap()
    };

    // fn main
    {
        // It's a lot more efficient to construct them once, and then re-use them for all functions.
        let mut ctx = codegen::Context::new();
        let mut fctx = cl::FunctionBuilderContext::new();

        let mut builder = cl::FunctionBuilder::new(&mut ctx.func, &mut fctx);
        builder.func.signature = main_fn_sign(&*isa);

        let block0 = builder.create_block();
        builder.switch_to_block(block0);

        // When we know that there are no more blocks to be written which may jump to this block, we want to seal
        // it. This improves the quality of code generation.
        builder.seal_block(block0);

        let one = builder.ins().iconst(types::I32, 1);
        let two = builder.ins().iconst(types::I32, 2);
        let sum = builder.ins().iadd(one, two);
        builder.ins().return_(&[sum]);

        if let Err(err) = codegen::verify_function(&builder.func, isa.as_ref()) {
            panic!("verifier error: {err}");
        }
        builder.finalize();
        println!("fn main:\n{}", &ctx.func);

        module.define_function(main_decl, &mut ctx).unwrap();
        ctx.clear();
    }

    let product = module.finish();
    // Generate the object file
    let bytes = product.emit().unwrap();
    let fname = "main.o";
    let mut f = File::create(fname).unwrap();
    f.write_all(&bytes).unwrap();

    info!("wrote output to {fname}");
}
