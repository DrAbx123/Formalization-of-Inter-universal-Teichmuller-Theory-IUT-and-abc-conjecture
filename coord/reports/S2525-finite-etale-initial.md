# S2525 FiniteEtale algebra PreGalois partial: INITIAL actual

## BUILT (EXIT=0)
S2525FiniteEtalePreGaloisAlgebra.lean:
- S2525HasInitial : HasInitial (CommAlgCat.FiniteEtale R).
  Initial object is R itself (Algebra.ofId R -), which is terminal in the opposite category.
Axioms: propext, Classical.choice, Quot.sound; no sorryAx.

## Important correction
We initially attempted HasTerminal (FiniteEtale R), but the zero ring/terminal object is not finite etale;
the natural object is INITIAL R in FiniteEtale, i.e. TERMINAL in (FiniteEtale R)^op.

## Still missing
- pullback in (FiniteEtale R)^op = coproduct of finite etale algebras (product algebra);
- finite coproduct in op = pullback/tensor product over R;
- finite group quotients/invariants and mono direct summands;
- PreGaloisCategory instance and cover-equivalence transport.
No fake.

## Artifacts
Lean: tmp/sheaf/xif/paper/S2525FiniteEtalePreGaloisAlgebra.lean
EXIT=0; SHA256 EC19454B815CB01C3E7A42C3D07261A189DDAC45EC386811158BF8DAF1DF4274
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2525FiniteEtalePreGaloisAlgebra.olean
olean SHA256: AB023920572523B8AD203C4ED750B93610140488A057CD8E5C00C039C20077F0
axioms: trio