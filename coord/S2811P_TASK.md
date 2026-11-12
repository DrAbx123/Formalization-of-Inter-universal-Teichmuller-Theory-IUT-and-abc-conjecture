# S2811P iso/sheaf task

Lean 4.32.2 + Mathlib v4.32.2, D:/lean.

Existing:
- tmp/sheaf/xif/paper/S2811P5Actual.lean (ACTUAL): P definition + P_subsingleton.
- tmp/sheaf/xif/paper/S2811IsPrestackActual.lean (ACTUAL): schemeEtaleTopologySubcanonical, schemeOverFieldEtaleTopologySubcanonical, S2811_yoneda_isSheaf.

Goal:
1. Prove presheafHom M N is isomorphic to P m n for m=M.as, n=N.as:
   - use @[simps!] lemmas generated for Functor.toPseudofunctor':
     Functor.toPseudofunctor'_obj, Functor.toPseudofunctor'_map (check exact names with #check)
   - unfold schemeRepresentableFiberFunctor, schemeRepresentableEtalePseudofunctor
   - on T: Discrete hom from Discrete.mk (T.hom ≫ m) to Discrete.mk (T.hom ≫ n);
     P T = ULift {* // T.hom ≫ m = T.hom ≫ n}; both subsingleton.
2. Prove P is a sheaf for etale topology:
   - for covering sieve R, compatible family gives local equalities;
   - use S2811_yoneda_isSheaf / IsSheafFor.hom_ext on yoneda(X) with maps yoneda.map (T.hom ≫ m) and yoneda.map (T.hom ≫ n);
   - get global equality, take id_T.
3. Use Presheaf.isSheaf_of_iso_iff to get presheafHom sheaf; assemble IsPrestack.
4. Compile with lake env lean -j1 -R 'D:/lean' -o .lake/build/lib/lean/tmp/sheaf/xif/paper/<File>.olean tmp/sheaf/xif/paper/<File>.lean
Report EXIT, first error, src/olean SHA, axioms. No sorry/extra axioms.
