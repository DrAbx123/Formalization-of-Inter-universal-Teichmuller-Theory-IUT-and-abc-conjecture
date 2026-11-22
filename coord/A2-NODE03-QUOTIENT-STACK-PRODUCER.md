# A2 node03 quotient-stack producer plan (2026-11-15)

Task: produce actual `Iut.OrbicurveSignQuotientWitness` for the sign quotient `C=[U/G]`, `G=C₂`, consumed by `SourceSignQuotientData.quotientWitness`; do not replace the quotient by a coarse point/x-coordinate quotient and do not use a degenerate partial point stack.

## Inputs / existing donors
- `Mzk1A2QuotientMorphismActual`: degenerate `signActionSimplified`, `quotientMorphismSimplified` (cocycle `rfl`); witness remains explicit gap.
- `Mzk1A2InvolutionCandidateActual`, `Mzk1A2GeometricCorePartialActual`: point/curve correction route.
- `PermutationTorsorQuotient.fixedPointsEquivOrbitFunctions`: `(R^I)^G ≃ R^(I/G)`.
- `fixedPoints_finiteEtale_orbits`: fixed points of finite étale action are orbits.
- `descOfCompatible` + bicategorical descent: existing 2-categorical gluing API.
- `OrbicurveSignQuotientWitness` fields (vendor `Iut/Foundations/Orbicurve.lean:712`): `descend`, `factor`, `descendTwoCell`, `descendTwoCell_factor`, `twoCell_ext`.

## Construction (four steps)
1. Actual sign action: take open curve `U` with inversion `[-1]`; `inversionSquared := Iso.refl`, coherence from group structure; represent as étale stack `X`.
2. Local quotient at a finite étale trivialization: local algebra `R^I`, action becomes permutation on `I`; use `fixedPointsEquivOrbitFunctions` to identify invariants with `R^(I/G)`; étale descent for torsor/equivariant maps.
3. Assemble `C=[U/G]` and invariant morphism `quotient : X → C`; `descend Y invariant` glues invariant maps on trivial torsors via `descOfCompatible`; `factor` is the local comparison 2-isomorphism; `descendTwoCell` and `twoCell_ext` from descent uniqueness.
4. Prove finite-étale Galois category colimits: `HasColimitsOfShape (SingleObj G)` from existing terminal/pullback/coproduct/clopen and the quotient descent; no new `affineBaseG2` parameter.

## Exact missing Lean donors / interfaces
- no existing `Iut`-level construction of `C` as an étale stack with a chosen `quotient` invariant morphism; the degenerate `xFOfStackPoint` route is not the quotient.
- no `HasColimitsOfShape (SingleObj G)` producer for the finite-étale category; `descOfCompatible` only gives cocone gluing after the quotient local data exist.
- no packaged `PermutationTorsorQuotient` bridge from `fixedPointsEquivOrbitFunctions` to `OrbicurveSignQuotientWitness.descend`.
- `OrbicurveSignQuotientWitness` itself is a `Prop`-free structure with bicategorical fields; construction needs the actual finite-étale quotient stack API, not a new axiom.

## Acceptance
- Lean file owner: TBD (A2 lane, not WQuotient/stepxi lane).
- Must compile under watchdog, no sorry/axiom; `SourceSignQuotientData.quotientWitness` inhabited from actual `C`.
- If only local quotient data is available, deliver exact interface `SignQuotientStackProducerData` with `descend/factor/...` fields and no inhabitant.

## Status
- This document is a plan only; no Lean file added/changed in this step. No fake.
