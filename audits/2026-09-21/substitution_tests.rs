// Appended to a temporary copy of src/eval.rs by run-internal.sh.
#[cfg(test)]
mod audit_substitution {
    use super::*;
    #[test]
    fn reference_shared_substitution() {
        check(false);
    }
    #[test]
    fn optimized_shared_substitution() {
        check(true);
    }
    fn check(optimized: bool) {
        {
            let program = Program::default();
            let mut e = Engine::new(&program, optimized, 100_000, 100_000);
            let u = e.alloc(Val::U(0));
            let bool_ty = e.alloc(Val::Bool);
            let k = e.fresh_dim();
            let pt = e.alloc(Val::Path(Binder { var: k, body: u }, bool_ty, bool_ty));
            let p = e.variable(pt);
            let i = e.fresh_dim();
            let j = e.fresh_dim();
            let face = e.faces.eq(Dim::Var(i), Dim::Var(j));
            let a = e.at(p, Dim::Var(i));
            let b = e.at(p, Dim::Var(j));
            let s = e.substitution(Sub {
                terms: vec![],
                dims: vec![(i, Dim::Zero)],
                compose: None,
            });
            let a = e.sub(a, s);
            let b = e.sub(b, s);
            let lazy = e.conv(a, b, Some(u), face).unwrap();
            let aa = e.force(a, face).unwrap();
            let bb = e.force(b, face).unwrap();
            let forced = e.conv(aa, bb, Some(u), face).unwrap();
            eprintln!("optimized={optimized}: lazy={lazy}, forced={forced}");
            assert_eq!(lazy, forced, "conversion changed after forcing");
        }
    }
}
