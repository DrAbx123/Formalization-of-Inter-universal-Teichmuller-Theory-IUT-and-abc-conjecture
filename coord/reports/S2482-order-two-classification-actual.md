# S2482 order-two algebra automorphism classification: ACTUAL

## BUILT (independently recompiled, EXIT=0)
S2482OrderTwoAlgAutClassificationAltActual.lean:
  S2482OrderTwoAlgAutClassification_actual : S2482OrderTwoAlgAutClassification
where the Prop is imported from S2482QiNontrivialActual:
  forall phi : R ~= F-algebra R, phi^2=id -> phi=id or phi.toAlgHom = S2482CoordinateRingInvolution.
Axioms: propext, Classical.choice, Quot.sound; no sorryAx.

## Proof route (kernel-checked)
1. Explicit e : R ~= WeierstrassCurve.Affine.CoordinateRing S2482Curve with e x=xC, e y=yC.
2. Transfer phi to psi on Coord; psi^2=id.
3. X=psi xC: rank/norm argument using finrank_quotient_span_eq_natDegree_norm and
   CoordinateRing.degree_norm_smul_basis forces X=p(x) with natDegree p=1.
4. Y^2=X^3-X gives Y=r+s*y with natDegree r<=1 and s constant nonzero.
5. signC conjugation and domain factorization force r=0, Y=sg*y.
6. Coefficient comparison gives sg^2=alpha, alpha^2=1; psi^2 on y gives sg^2=1, so alpha=1,sg=±1.
7. Transfer back: phi=id or phi=sign involution.

## Related actual nearby files
- S2482WeightStrictActual.lean: strict weight additivity W_add_eq_of_lt and max formula.
- S2482WeightZeroConstantActual.lean: d a=0 -> a is a constant (aeval of C c).
- S2482QiNontrivialActual.lean: nontriviality/refutation baseline.

## Next
Use classification + corrected TwoIso uniqueness to prove the corrected uniqueness field; then OrbicurveSignAction, cF quotient/witness, xK/cK scalar extensions, epsilon.

## Artifacts
Lean: tmp/sheaf/xif/paper/S2482OrderTwoAlgAutClassificationAltActual.lean
EXIT=0; SHA256 406B9E872B7418AABE462C72E4E08C62A562EB4D54D42ECAB93D5D99504E628A
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2482OrderTwoAlgAutClassificationAltActual.olean
olean SHA256: D6492DF199BB5EC6536B14D292FE046F1DCEC79EF8983B754F3E1985DC8D6B5C
axioms: trio