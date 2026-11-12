# S2501: strictified fiber and sigma^2 = id actual

Date: 2026-11-02. Serialized lake env lean -j1.

ACTUAL:
- S2501StrictFiber C := C x Discrete Bool;
- S2501BoolSwap : Discrete Bool -> Discrete Bool, obj b = mk (!b);
- S2501Sigma C := id_C x S2501BoolSwap;
- S2501Sigma_sq : S2501Sigma C ;; S2501Sigma C = id (S2501StrictFiber C).
Proof: Functor.ext h_obj by cases Bool; h_map by cases b/c and Product.ext; Discrete components by Subsingleton; C components by convert eq_conj_eqToHom using 2 <;> rfl.

EXIT=0, olean 297600, SHA256 fbbf62e992576779cedc30b087895c5132de7c1dd29f65cb2fc3dd97296560a7, axioms propext/Classical.choice/Quot.sound.

Next: with strict sigma^2=id, action groupoid Category assoc should close; then quotient fiber/pseudofunctor/IsStack. No fake.