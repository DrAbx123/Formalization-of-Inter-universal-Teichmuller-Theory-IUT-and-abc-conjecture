# Spec extraction, F-linearity, phi^2=id: ACTUAL

## BUILT (EXIT=0)
S2482SpecPhiActual.lean:
- S2482AffineOver_left.
- S2482UnderlyingLeft, S2482UnderlyingLeft_eq, S2482Phi, S2482Phi_spec.
- S2482Phi_commutes: (S2482Phi eta).comp (algebraMap F R) = algebraMap F R.
- S2482UnderlyingLeft_comp: g'^2=1.
- S2482Phi_comp: phi^2=id.
Axioms trio; no sorryAx.

## Remaining
Construct S2482PhiAlgEquiv from phi (self-inverse); apply classification; id-case -> eta 2-iso id
contradicts nontriviality; sign-case -> S2482TwoIso_of_hom_eq. Then fill corrected Hom field; sign action/cF/cK/epsilon.
No fake.

## Artifacts
Lean: tmp/sheaf/xif/paper/S2482SpecPhiActual.lean
EXIT=0; SHA256 F974467C9A4208E792F9E4EF457392C9252580BF0F062BD18DA7C0FAF5E764C6
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2482SpecPhiActual.olean
olean SHA256: 6D9E86F4EC22E2C0953AD8C689699ECE53BC79D64E54633D9BDFF4B2E2F1775D
axioms: trio