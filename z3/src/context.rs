use std::ffi::CString;
use z3_sys::*;
use Config;
use Context;
use ContextHandle;

use crate::{Symbol, Sort, FuncDecl, ast::{Bool, self, Ast}};

impl Context {
    pub fn new(cfg: &Config) -> Context {
        Context {
            z3_ctx: unsafe {
                let p = Z3_mk_context_rc(cfg.z3_cfg);
                debug!("new context {:p}", p);
                Z3_set_error_handler(p, None);
                p
            },
        }
    }

    /// Interrupt a solver performing a satisfiability test, a tactic processing a goal, or simplify functions.
    pub fn interrupt(&self) {
        self.handle().interrupt()
    }

    /// Obtain a handle that can be used to interrupt computation from another thread.
    ///
    /// # See also:
    ///
    /// - [`ContextHandle`]
    /// - [`ContextHandle::interrupt()`]
    pub fn handle(&self) -> ContextHandle {
        ContextHandle { ctx: self }
    }

    /// Update a global parameter.
    ///
    /// # See also
    ///
    /// - [`Context::update_bool_param_value()`]
    pub fn update_param_value(&mut self, k: &str, v: &str) {
        let ks = CString::new(k).unwrap();
        let vs = CString::new(v).unwrap();
        unsafe { Z3_update_param_value(self.z3_ctx, ks.as_ptr(), vs.as_ptr()) };
    }

    /// Update a global parameter.
    ///
    /// This is a helper function.
    ///
    /// # See also
    ///
    /// - [`Context::update_param_value()`]
    pub fn update_bool_param_value(&mut self, k: &str, v: bool) {
        self.update_param_value(k, if v { "true" } else { "false" })
    }
    
    /**
       Parse a `sentence` in SMT 2.0 format.

    The function takes five arguments:
    - `sentence`: a string slice or vector of bytes representing the input sentence in SMT 2.0 format.
    - `sort_names`: a slice of string slices representing the names of sorts used in the sentence.
    - `sorts`: a slice of references to `Sort` objects representing the sorts used in the sentence.
    - `decl_names`: a slice of string slices representing the names of declarations used in the sentence.
    - `decls`: a slice of references to `FuncDecl` objects representing the function declarations used in the sentence.
    # Examples
    ```
    # use z3::{ast, Config, Context, FuncDecl, Sort}; 
    # use z3::ast::Ast;
     let cfg = Config::new();
     let ctx = Context::new(&cfg);

     let x = ast::Int::fresh_const(&ctx, "x");
     let y = ast::Int::fresh_const(&ctx, "y");
     
     let int = Sort::int(&ctx);
     let f = FuncDecl::new(&ctx, "f", &[&int], &int);
     let probs = ctx.from_string("(assert (> (+ foo (g bar)) 0))", &[], &[], &["foo", "bar", "g"], &[&x.decl(), &y.decl(), &f]);
       
     assert_eq!(probs.first().unwrap(), &(x + f.apply(&[&y]).as_int().unwrap()).gt(&ast::Int::from_i64(&ctx, 0)));    
    */
    pub fn from_string<T: Into<Vec<u8>>, S: Into<Symbol> + Clone>(&self, sentence: T, sort_names: &[S], sorts: &[&Sort], decl_names: &[S], decls: &[&FuncDecl]) -> Vec<Bool> {
        let str = CString::new(sentence).unwrap();

        let z3_vec = unsafe {
            let sort_names:Vec<_> = sort_names.iter().map(|s|
                (*s).clone().into().as_z3_symbol(self)).collect();
            let decl_names:Vec<_> = decl_names.into_iter().map(|s| s.clone().into().as_z3_symbol(self)).collect();
            let sorts:Vec<_> = sorts.into_iter().map(|s| s.z3_sort).collect();
            let decls:Vec<_> = decls.into_iter().map(|x| x.z3_func_decl).collect();
            Z3_parse_smtlib2_string(self.z3_ctx, 
                str.as_ptr(),
                sort_names.len() as u32, 
                sort_names.as_ptr(), 
                sorts.as_ptr(),
                decl_names.len() as u32,
                decl_names.as_ptr(),
                decls.as_ptr(),
            )
        };

        (0..unsafe { Z3_ast_vector_size(self.z3_ctx, z3_vec) })
            .map(|i| unsafe {
                let z3_ast = Z3_ast_vector_get(self.z3_ctx, z3_vec, i);
                ast::Bool::wrap(self, z3_ast)
            })
            .collect()
    }
}
impl<'ctx> ContextHandle<'ctx> {
    /// Interrupt a solver performing a satisfiability test, a tactic processing a goal, or simplify functions.
    pub fn interrupt(&self) {
        unsafe {
            Z3_interrupt(self.ctx.z3_ctx);
        }
    }
}

unsafe impl<'ctx> Sync for ContextHandle<'ctx> {}
unsafe impl<'ctx> Send for ContextHandle<'ctx> {}

impl Drop for Context {
    fn drop(&mut self) {
        unsafe { Z3_del_context(self.z3_ctx) };
    }
}
