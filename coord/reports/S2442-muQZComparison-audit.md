# muQZComparison: construction audit (local Artin on colimit)

## Actual pre-existing ingredients
- S2102TorsionArtinActual: actual `localArtinTorsionEquiv U : mu p U ≃* torsion Gal(maxAb_U/L_U)` and `localArtinTorsion_holds`/`localArtinTorsionTopological_holds`.
- S2113M2bTransferActual: actual `localArtinTorsionEquiv_apply` (computation through `PadicField.artin`), `kappa U : Abelianization U ->* Gal(maxAb_U/L_U)`, S2119's `verS2027`/`artinTransfer_S2027`.
- S2017: actual `muQZ`/`muQZof` universal property and `muQZComparison` statement.

## Proposed actual map and exact obstruction
For each U define the stage map
  f_U : Stage U -> Additive (torsion (Otri p)^x)
  f_U(v) := muInGlobal U ((localArtinTorsionEquiv U).symm (torsionMap (kappa U) v)).
To descend to the colimit `muQZ -> Additive torsion(Otri)^x` via `muQZ_lift`, one must prove the cocone compatibility
  forall {H K} (h : H <= K) (v : Stage K),
    f_H (toStage h v) = f_K v.
This is exactly the transfer square: the abstract `verlagerungOpen` transported by `kappa` must agree with the Galois norm/Artin transfer. No such theorem is present in the tree. S2119 closes only the carrier side (`verCarrierComparison`, `verS2027`, `artinTransfer_S2027`), not the abstract-to-Galois naturality.

## Consequence
- `muQZComparison` is NOT constructed; equivalently `muHatComparivalence` is not constructed.
- The exact first missing is the same `kappa`-naturality square as in `S2442-kappa-transfer-naturality.md`:
    torsionMap (kappa H) (torsionMap (verlagerungOpen h) v)
      = torsionMap (verS2027 h) (torsionMap (kappa K) v),
  plus the identification of `localArtinTorsionEquiv` with the local Artin map on the resulting torsion elements (already available pointwise by S2113).
- No M2c-free construction was found. The natural route uses `canonicalTorsionComparison` (M2c) to relate `torsion (Abelianization U)` and `torsion (TopologicalAbelianization G_U)`; without it the cocone compatibility is the missing transfer square.

## Action compatibility
Even after `muQZComparison`, the two actions (`S2442MuQZAction` and `S2046G1PsiCnsAction`/`PsiCnsCoefficientAction`) still require an equivariance proof `heq`; the module equivalence from `muHatComparison` alone does not provide it. No construction/refutation in this file.

## Status
No new Lean file compiled; no build/cache command. No fake or interface-only data was introduced. The concrete first missing is the colimit cocone compatibility / kappa-transfer naturality above.