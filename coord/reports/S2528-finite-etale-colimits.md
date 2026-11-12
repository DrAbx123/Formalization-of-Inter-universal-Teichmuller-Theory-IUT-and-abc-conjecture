# S2528 FiniteEtale finite coproducts/pullbacks: ACTUAL

## BUILT (EXIT=0)
S2528FiniteEtaleColimitsActual.lean:
- S2528HasFiniteCoproducts (R) : HasFiniteCoproducts ((CommAlgCat.FiniteEtale R)^op).
- S2528HasPullbacks (R) : HasPullbacks ((CommAlgCat.FiniteEtale R)^op).
Imported from actual no-sorry S1779ClosureProbe; wrapper instances.
Axioms trio; no sorryAx.

## Meaning
Finite coproducts in the opposite category = finite products of finite etale algebras;
pullbacks in op = pushouts/tensor products. This gives the PreGalois coproduct/pullback structure at algebra level.

## Still missing
finite limits (terminal done via HasInitial), finite group quotients/invariants, mono summands,
fiber functor, equivalence to cover category, PreGaloisCategory assembly.
No fake.

## Artifacts
Lean: tmp/sheaf/xif/paper/S2528FiniteEtaleColimitsActual.lean
EXIT=0; SHA256 FF857A4974815956AFAF541274A5CAA98898C0036959721E15F8ED99B22A8C77
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2528FiniteEtaleColimitsActual.olean
olean SHA256: 20C73A4B1E6FB73329582E528D80274A1F026489288F50644DCD1AFC9BD5B179
axioms: trio