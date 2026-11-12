# S2464: unitor probe actual — named a/b args fix elaboration

Date: 2026-11-02. Serialized lake env lean -j1.

ACTUAL:
noncomputable def testLeft : (1 Xf >> S2482EllipticInvolution) ~ S2482EllipticInvolution := Bicategory.leftUnitor (a := Xf) (b := Xf) S2482EllipticInvolution.
noncomputable def testRight : (S2482EllipticInvolution >> 1 Xf) ~ S2482EllipticInvolution := Bicategory.rightUnitor (a := Xf) (b := Xf) S2482EllipticInvolution.
where Xf := S2482Orbicurve.stack.fiber.

EXIT=0, olean 120... bytes (see build path), SHA256 source bed5b6942d07c3e56cc01b4d5bd19d85897bc0d951ecd6ef06fd96356d6ea843, axioms propext/Classical.choice/Quot.sound.

KEY: supplying a and b explicitly makes Bicategory.leftUnitor/rightUnitor elaborate; the previous hangs were due to implicit object inference.

Full S2461 diagram still exceeds 5 min (likely cat_disch coherence obligations after mapComp, not mapComp unitor inference). Next: replace coherence by explicit bicategory/simp proofs or isolate mapComp as a standalone lemma first. No fake.