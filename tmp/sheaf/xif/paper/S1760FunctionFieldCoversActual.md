# S1760 — function-field comparison for finite étale covers

File: `tmp/sheaf/xif/paper/S1760FunctionFieldCoversActual.lean`

## Evidence

- EXIT = 0.
- Source: 402 lines, 17995 bytes, SHA256 `40FF81116EC9BC28D8ED2CD5A7E65D0AD6C6B1191A2078E0BDE25CBC20889FFA`.
- Olean: `D:\lean\.lake\build\lib\lean\tmp\sheaf\xif\paper\S1760FunctionFieldCoversActual.olean`
  - 327872 bytes, SHA256 `EE2167E298A3974A8473DB0F7D4B8381E34AEF1CFEB9E12D17B7A18EA7691CF4`.
- Imports the olean successfully.
- Axiom probes on the main theorems: only `propext`, `Classical.choice`, `Quot.sound`.
- No `sorry`, `admit`, new axiom, `Shrink`, or `ULift`.

## Proved unconditionally

1. For an integral scheme `X` and `K = X.functionField`, the canonical generic point map
   `S1760GenericPointMap : Spec K ⟶ X` and the generic-fibre comparison functor
   `S1760GenericFiberFunctor : FiniteEtaleCover X ⥤ (FiniteEtale K)^op`.
   The latter is base change along the generic point followed by the proved field-case
   Spec/Gamma equivalence `(FiniteEtale K)^op ≌ FiniteEtaleCover (Spec K)`.
2. For a domain `R` with fraction field `K`, the algebraic base-change functor
   `(FiniteEtale R)^op ⥤ (FiniteEtale K)^op` is faithful.
   This is the concrete form of the comparison at the coordinate-ring level.
3. For any field `K`, every finite étale `K`-algebra is a finite product of finite
   separable field extensions (Mathlib classification), i.e. the disconnected-to-finite-products
   half of the asserted correspondence.
4. Specializations to the actual affine once-punctured Weierstrass curve
   `curveScheme F' = Spec F'[x,y]/(y^2-x^3+x)` and its function field.

## Missing / corrected boundary

- General affine Spec/Gamma equivalence `FiniteEtaleCover (Spec R) ≌ (FiniteEtale R)^op`
  for a non-field base `R`: only the field case is in the project/Mathlib.  Frozen as
  `S1760AffineCoverAlgebraEquivalence`.
- Normal-base integral descent: for normal `R`, `x ∈ K ⊗_R B` integral over `R` lies in
  `B`; this is the exact input for fullness.  Frozen as `S1760BaseIntegralDescent`.
- Normal scheme API: Mathlib 4.32.2 has no `IsNormal` scheme predicate; only relative
  normalization.  Recorded in the file and via `S1760CurveNormalityMissing`.
- Connected cover ↔ field generic fibre is not proved; frozen as
  `S1760ConnectedGenericFiberIsField` / `S1760FieldGenericFiberConnected`.
- Essential surjectivity for all finite étale `K`-algebras is mathematically FALSE:
  ramification at a finite point of the punctured curve is an obstruction.  The corrected
  target is the full subcategory of finite étale `K`-algebras unramified over the curve,
  which requires normalization of the curve in a finite extension.  The file records this as
  `S1760UnramifiedFiniteEtaleSubcategory` with no inhabitant.
- No category equivalence is asserted.  The file only gives the exact decomposition
  `IsEquivalence ↔ Faithful ∧ Full ∧ EssSurj` for the generic-fibre and algebraic
  comparisons.
