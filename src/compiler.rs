use std::collections::HashMap;
use std::process::Command;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::passes::PassManager;
use inkwell::types::{AnyType, BasicMetadataTypeEnum, BasicTypeEnum};
use inkwell::values::{BasicValue, BasicMetadataValueEnum, FloatValue, IntValue, FunctionValue, PointerValue, BasicValueEnum, AnyValue, AnyValueEnum};
use inkwell::{OptimizationLevel, FloatPredicate, IntPredicate};
use inkwell::targets::{CodeModel, FileType, InitializationConfig, RelocMode, Target, TargetMachine};
use crate::ast::{BinOpcode, Block, Expr, FuncDef, LocExpr, Program, Stmt, Type, UnOpcode, Var};


pub struct Compiler<'a, 'ctx> {
    pub context: &'ctx Context,
    pub builder: &'a Builder<'ctx>,
    pub fpm: &'a PassManager<FunctionValue<'ctx>>,
    pub module: &'a Module<'ctx>,

    pub program: Program,

    variables: HashMap<Var, PointerValue<'ctx>>,
    functions: HashMap<String, FunctionValue<'ctx>>,
    fn_value_opt: Option<FunctionValue<'ctx>>,
    verbose: bool,
}

impl<'a, 'ctx> Compiler<'a, 'ctx> {
    /// Gets a defined function given its name.
    #[inline]
    fn get_function(&self, name: &str) -> Option<FunctionValue<'ctx>> {
        self.module.get_function(name)
    }

    /// Returns the `FunctionValue` representing the function being compiled.
    #[inline]
    fn fn_value(&self) -> FunctionValue<'ctx> {
        self.fn_value_opt.unwrap()
    }

    /// Creates a new stack allocation instruction in the entry block of the function.
    fn create_entry_block_alloca(&self, name: &str) -> PointerValue<'ctx> {
        let builder = self.context.create_builder();

        let entry = self.fn_value().get_first_basic_block().unwrap();

        match entry.get_first_instruction() {
            Some(first_instr) => builder.position_before(&first_instr),
            None => builder.position_at_end(entry)
        }

        builder.build_alloca(self.context.i64_type(), name)
    }

    fn compile_ty(&mut self, t: &Type) -> BasicMetadataTypeEnum<'ctx> {
        match t {
            Type::Int => self.context.i64_type().into(),
            Type::Bool => self.context.bool_type().into(),
            // TODO: handle Unit in Typechecker?
            // Type::Unit => self.context.void_type().into(),
            _ => panic!("Unsupported type: {:?}", t)
        }
    }

    fn compile_exp(&mut self, exp: &Expr) -> BasicValueEnum<'ctx> {
        match exp {
            Expr::IntLit(i) => {
                let i64_type = self.context.i64_type();
                let i64_val = i64_type.const_int(*i as u64, false);
                i64_val.into()
            },
            Expr::BoolLit(b) => {
                let bool_type = self.context.bool_type();
                let bool_val = bool_type.const_int(*b as u64, false);
                bool_val.into()
            },
            Expr::Var(v) => {
                let ptr = self.variables.get(v).unwrap();
                self.builder.build_load(*ptr, v.as_str())
            },
            Expr::BinOp(op, left, right) => {
                let left = self.compile_exp(left);
                let right = self.compile_exp(right);

                match &**op {
                    BinOpcode::Add => {
                        self.builder.build_int_add(left.into_int_value(), right.into_int_value(), "addtmp").into()
                    }
                    BinOpcode::Sub => {
                        self.builder.build_int_sub(left.into_int_value(), right.into_int_value(), "subtmp").into()
                    }
                    BinOpcode::Mul => {
                        self.builder.build_int_mul(left.into_int_value(), right.into_int_value(), "multmp").into()
                    }
                    BinOpcode::Div => {
                        self.builder.build_int_signed_div(left.into_int_value(), right.into_int_value(), "divtmp").into()
                    }
                    BinOpcode::Mod => {
                        self.builder.build_int_signed_rem(left.into_int_value(), right.into_int_value(), "modtmp").into()
                    }
                    BinOpcode::Lt => {
                        self.builder.build_int_compare(IntPredicate::SLT, left.into_int_value(), right.into_int_value(), "cmptmp").into()
                    }
                    BinOpcode::Le => {
                        self.builder.build_int_compare(IntPredicate::SLE, left.into_int_value(), right.into_int_value(), "cmptmp").into()
                    }
                    BinOpcode::Gt => {
                        self.builder.build_int_compare(IntPredicate::SGT, left.into_int_value(), right.into_int_value(), "cmptmp").into()
                    }
                    BinOpcode::Ge => {
                        self.builder.build_int_compare(IntPredicate::SGE, left.into_int_value(), right.into_int_value(), "cmptmp").into()
                    }
                    BinOpcode::Eq => {
                        self.builder.build_int_compare(IntPredicate::EQ, left.into_int_value(), right.into_int_value(), "cmptmp").into()
                    }
                    BinOpcode::Ne => {
                        self.builder.build_int_compare(IntPredicate::NE, left.into_int_value(), right.into_int_value(), "cmptmp").into()
                    }
                    BinOpcode::And => {
                        self.builder.build_and(left.into_int_value(), right.into_int_value(), "andtmp").into()
                    }
                    BinOpcode::Or => {
                        self.builder.build_or(left.into_int_value(), right.into_int_value(), "ortmp").into()
                    }
                    // op => panic!("Unsupported binop: {:?}", op)
                }
            },
            Expr::UnOp(op, inner) => {
                let inner = self.compile_exp(inner);

                match &**op {
                    UnOpcode::Neg => {
                        self.builder.build_int_neg(inner.into_int_value(), "negtmp").into()
                    }
                    UnOpcode::Not => {
                        self.builder.build_not(inner.into_int_value(), "nottmp").into()
                    }
                }
            }
            Expr::Call(name, args) => {
                let args = args.iter().map(|e| self.compile_exp(e).into()).collect::<Vec<_>>();
                let func = self.functions.get(name.as_str()).unwrap();
                let call_res = self.builder.build_call(*func, &args[..], name.as_str());
                // if we typecheck correctly and do not allow void functions to be in expression calls, then this will always work
                call_res.try_as_basic_value().unwrap_left().into()
            }
            // Expr::Array(els) => {
            //     // TODO: Add type to WithLoc
            //     let els = els.iter().map(|e| self.compile_exp(e)).collect::<Vec<_>>();
            //     let array_type = self.context.i32_type().array_type(els.len() as u32);
            //     let array_ptr = self.builder.build_alloca(array_type, "arraytmp");
            //     for (i, el) in els.iter().enumerate() {
            //         let el_ptr = self.builder.build_gep(array_ptr, &[self.context.i32_type().const_int(i as u64, false)], "elptr");
            //         self.builder.build_store(el_ptr, el.into_pointer_value());
            //     }
            //     array_ptr.into()
            // }
            e => panic!("Unsupported expression: {:?}", e)
        }
    }

    fn compile_stmt(&mut self, stmt: &Stmt) {
        match stmt {
            Stmt::Return(None) => {
                self.builder.build_return(None);
            },
            Stmt::Return(Some(exp)) => {
                let val = self.compile_exp(exp);
                self.builder.build_return(Some(&val));
            },
            Stmt::Decl(v, e) => {
                let val = self.compile_exp(e);

                let alloca = self.create_entry_block_alloca(v.as_str());
                self.builder.build_store(alloca, val);

                self.variables.insert(v.elem.clone(), alloca);
            },
            Stmt::Assn(le, e) => {
                match &le.elem {
                    LocExpr::Var(v) => {
                        let val = self.compile_exp(e);
                        let var = self.variables.get(v).unwrap();
                        // TODO: If we add other types than Int/Bool, we will need to handle these .into_int_values() differently.
                        // currently everything works out, because bools are ints in LLVM
                        self.builder.build_store(*var, val.into_int_value());
                    }
                    LocExpr::Index(_, _) => { todo!("handle index assns") }
                }
            },
            Stmt::IfElse { cond, if_branch, else_branch } => {
                let cond = self.compile_exp(cond).into_int_value();
                // let cond_val = self.builder.build_int_compare(IntPredicate::NE, cond.into_int_value(), self.context.i32_type().const_int(0, false), "condtmp");

                let if_bb = self.context.append_basic_block(self.fn_value(), "if_true");
                let else_bb = self.context.append_basic_block(self.fn_value(), "if_false");
                let merge_bb = self.context.append_basic_block(self.fn_value(), "if_end");

                self.builder.build_conditional_branch(cond, if_bb, else_bb);

                self.builder.position_at_end(if_bb);
                let returns = self.compile_block(if_branch);
                if !returns {
                    self.builder.build_unconditional_branch(merge_bb);
                }

                self.builder.position_at_end(else_bb);
                let returns = self.compile_block(else_branch);
                if !returns {
                    self.builder.build_unconditional_branch(merge_bb);
                }

                self.builder.position_at_end(merge_bb);
            },
            Stmt::While { cond, block } => {
                let cond_bb = self.context.append_basic_block(self.fn_value(), "cond_bb");
                let body_bb = self.context.append_basic_block(self.fn_value(), "body_bb");
                let after_bb = self.context.append_basic_block(self.fn_value(), "after_bb");

                self.builder.build_unconditional_branch(cond_bb);
                self.builder.position_at_end(cond_bb);

                let cond = self.compile_exp(cond).into_int_value();
                self.builder.build_conditional_branch(cond, body_bb, after_bb);

                self.builder.position_at_end(body_bb);
                let returns = self.compile_block(block);
                if !returns {
                    self.builder.build_unconditional_branch(cond_bb);
                }

                self.builder.position_at_end(after_bb);
            },
            s => panic!("Unsupported statement: {:?}", s)
        }
    }

    fn compile_block(&mut self, block: &Block) -> bool {
        let stmts = block.0.clone();
        // let mut returns = false;
        for stmt in stmts {
            self.compile_stmt(&*stmt);
            if let Stmt::Return(_) = *stmt {
                // returns = true;
                // early abort, okay because we will never reach the later statements in the block anyway.
                return true;
            }
        }

        return false;
        // returns
    }

    fn compile_fndef(&mut self, f: &FuncDef) -> FunctionValue<'ctx> {
        let args_types = f.params.iter()
            .map(|(_, t)| {
                self.compile_ty(t)
            })
            .collect::<Vec<BasicMetadataTypeEnum>>();
        let args_types = args_types.as_slice();

        // let ret_type = match *f.retty {
        //     Type::Unit => self.context.void_type().as_any_type_enum(),
        //     Type::Int => self.context.i64_type().into(),
        //     Type::Bool => self.context.bool_type().into(),
        //     _ => panic!("Unsupported type: {:?}", t)
        // };
        let fn_type = match &*f.retty {
            Type::Unit => self.context.void_type().fn_type(args_types, false),
            Type::Int => self.context.i64_type().fn_type(args_types, false),
            Type::Bool => self.context.bool_type().fn_type(args_types, false),
            t => panic!("Unsupported type: {:?}", t)
        };

        let fn_val = self.module.add_function(f.name.as_str(), fn_type, None);

        // set arguments names
        for (i, arg) in fn_val.get_param_iter().enumerate() {
            // match *f.params[i].1 {
            //     Type::Int => arg.into_int_value().set_name(f.params[i].0.as_str()),
            //     Type::Bool => arg.into().set_name(f.params[i].0.as_str()),
            //     Type::Unit => arg.set_name(f.params[i].0.as_str()),
            //     _ => panic!("Unsupported type: {:?}", f.params[i].1)
            // }
            // TODO: if we add floats, adjust here
            arg.into_int_value().set_name(f.params[i].0.as_str());
        }

        // finally return built prototype
        fn_val
    }

    fn compile_fn(&mut self, f: &FuncDef) {
        self.variables.clear();

        // let function = self.compile_fndef(f);
        let function = self.functions.get(f.name.as_str()).unwrap().clone();
        if self.verbose {
            println!("{:?}", function);
        }

        let entry = self.context.append_basic_block(function, "entry");

        self.builder.position_at_end(entry);

        // update fn field
        self.fn_value_opt = Some(function);

        // build variables map
        self.variables.reserve(f.params.len());

        for (i, arg) in function.get_param_iter().enumerate() {
            let arg_name = f.params[i].0.as_str();
            let alloca = self.create_entry_block_alloca(arg_name);

            self.builder.build_store(alloca, arg);

            self.variables.insert(f.params[i].0.elem.clone(), alloca);

            // // if we are main and second argument, i.e. argv, then store it in global variable
            // if f.name.as_str() == "main" && i == 1 {
            //     self.builder.build_global_string()
            // }
        }

        self.compile_block(&*f.body);
        if self.verbose {
            println!("{}", format!("{:?}", function).replace("\\n", "\n"));
        }

        if function.verify(true) {
            self.fpm.run_on(&function);
        } else {
            panic!("invalid generated function {:?}", function);
        }
    }

    fn compile_prog(&mut self) {
        let print_int = self.context.i64_type().fn_type(&[self.context.i64_type().into()], false);
        let print_int_fn = self.module.add_function("print_int", print_int, None);
        self.functions.insert("print_int".to_string(), print_int_fn);

        let int_arg = self.context.i64_type().fn_type(&[self.context.i64_type().into()], false);
        let int_arg_fn = self.module.add_function("int_arg", int_arg, None);
        self.functions.insert("int_arg".to_string(), int_arg_fn);

        let funcdefs = self.program.0.clone();
        // Build decl map
        for f in funcdefs.iter() {
            let function = self.compile_fndef(&*f);
            self.functions.insert(f.name.elem.clone(), function);
        }

        for f in funcdefs {
            self.compile_fn(&*f);
        }
    }

    pub fn compile(
        context: &'ctx Context,
        builder: &'a Builder<'ctx>,
        pass_manager: &'a PassManager<FunctionValue<'ctx>>,
        module: &'a Module<'ctx>,
        program: Program,
        verbose: bool,
    ) {
        let mut compiler = Compiler {
            context: context,
            builder: builder,
            fpm: pass_manager,
            module: module,
            program: program,
            fn_value_opt: None,
            variables: HashMap::new(),
            functions: HashMap::new(),
            verbose: verbose,
        };

        compiler.compile_prog();
    }
}

pub fn compile(prog: Program, output: &str, verbose: bool) {
    let context = Context::create();
    let module = context.create_module("repl");
    let builder = context.create_builder();

    let fpm = PassManager::create(&module);

    fpm.add_instruction_combining_pass();
    fpm.add_reassociate_pass();
    fpm.add_gvn_pass();
    fpm.add_cfg_simplification_pass();
    fpm.add_basic_alias_analysis_pass();
    fpm.add_promote_memory_to_register_pass();
    fpm.add_instruction_combining_pass();
    fpm.add_reassociate_pass();

    fpm.initialize();

    Compiler::compile(
        &context,
        &builder,
        &fpm,
        &module,
        prog,
        verbose,
    );

    // Build module into executable
    Target::initialize_all(&InitializationConfig::default());

    let target_triple = TargetMachine::get_default_triple();

    let target = Target::from_triple(&target_triple).map_err(|e| format!("{:?}", e)).unwrap();
    let target_machine = target
        .create_target_machine(
            &target_triple,
            "generic",
            "",
            OptimizationLevel::Default,
            RelocMode::Default,
            CodeModel::Default,
        )
        .ok_or_else(|| "Unable to create target machine!".to_string()).unwrap();

    let output_filename = output.to_string() + ".s";
    target_machine
        .write_to_file(&module, FileType::Assembly, output_filename.as_ref())
        .map_err(|e| format!("{:?}", e)).unwrap();

    println!("{:?}", Command::new("clang-13")
        .args(["runtime.c", &output_filename, "-o", output])
        .output()
        .expect("failed to execute process")
    );
}