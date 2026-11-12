# S2449 q-side plan (BUILD HOLD: no compilation performed)

## 0. Build incident
All builds stopped on lead instruction (missing Mathlib artifacts from concurrent
lake builds). This plan is text-only; no xif_parallel_build/lake/lean was run.

## 1. S2432Layer1SplitActual.lean: import/name diagnosis

Real declarations:
- `S2040QVPlaceSplitPackage` is declared in
  `tmp/sheaf/xif/paper/S2040QVPlaceSplitActual.lean` (structure, line 60).
  S2432 already imports it directly (fixed).
- `SourceNativeInitialThetaData` is declared in
  `LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean`,
  namespace `LeanFormal.IUT.InitialThetaSource`, line 1681.
  S2432 now uses the fully qualified name with `.{0}`; the earlier universe
  error is gone.
- `Bad` is declared in `SourcePlacePartitionReduction.lean` line 188,
  namespace `LeanFormal.IUT.InitialThetaSource`.
- `nativePlaceSelection` is declared in
  `SourceDefinition31NativeContractBridgeReduction.lean` line 108,
  namespace `LeanFormal.IUT`.

Remaining failure (pre-hold): the binder line
`(b : Bad (nativePlaceSelection T))` is not elaborated; Lean then reports
`Unknown identifier b` at every use. The unresolved piece is the
`Bad`/`nativePlaceSelection` combination, not S2040.

### Proposed fix (execute after build resumes)
1. Add explicit imports (not rely on transitive):
   ```lean
   import LeanFormal.IUT.IUTI.InitialTheta.SourcePlacePartitionReduction
   import LeanFormal.IUT.IUTI.HodgeTheater.SourceDefinition31NativeContractBridgeReduction
   ```
2. Keep `open LeanFormal.IUT` and `open LeanFormal.IUT.InitialThetaSource`.
3. If the `Bad` sigma still fails, write the binder as
   `(b : LeanFormal.IUT.InitialThetaSource.Bad (nativePlaceSelection T))`
   and inspect with `#check @LeanFormal.IUT.InitialThetaSource.Bad`.
4. Replace the `obtain ⟨P⟩ := ...` (Nonempty -> Type) by the concrete
   `s2195_primeAlignedSplitPackage` route, or use `Classical.choice` only.
   S2232 already has `s2232_package_of_paperArithmeticConditions` and
   `s2232_paperArithmeticConditions_iff_package`; S2195 has
   `s2195_toPackage`.
5. Target theorem:
   ```lean
   theorem S2432Layer1Split_of_paperConditions
       (h : S2232PaperArithmeticConditions T b) :
       S2040QVPlaceSplitPackage T b
   ```
   Proof: strip from h, choose actual qVFamTensorP place, call
   `s2195_primeAlignedSplitPackage` then `s2195_toPackage`.

## 2. S1493 point transport proof steps

Declarations:
- `S1493KSideTateTransportActual.baseChange_curve_map_eq` identifies
  `((T.arithmetic.curve.baseChange Fv).curve).map completionMap` with
  `(kSideCurve).baseChange Kv` (curve level).
- `S1493CurveTransport`/`s1493CurveTransport` package the algebraic data.
- `S1550TatePointComparisonFromClosureActual.WFproj/WKproj/SideFPoint/SideKPoint`
  and `pointTransport : SideFPoint T b ≃+ SideKPoint T b`.

Missing link: S2412 points live on
`W.map (algebraMap R (AlgebraicClosure R))`,
whereas pointTransport starts on `SideFPoint T b` over `LF T b`.
Need a point-level map from the algebraic closure used by S2412 to `LF T b`
(or directly base-change the S2412 curve to `LF` and identify it with
`WFproj`). Then:
1. transport each point via `pointTransport`;
2. `pointTransport` is an `AddEquiv`, hence preserves `2 • P = 0`;
3. injectivity gives distinctness; zero maps to zero;
4. `pointTransport_galois` gives Galois naturality; for `IsGaloisFixed`
   combine with the S2412 fixedness/root choice.

## 3. S2296LCoprimeRepresentative plan

S2420 file (subagent) already has candidate lemmas:
`unitsMap_galois_fixed`, `isGaloisFixed_pointEquiv_mk`,
`lTorsion_pointEquiv_mk`, `exists_lthRoot_in_Kv_of_fixed_class`,
`LCoprimeRepresentative_of_*`.  It needs clean compile after the hold.
Then construct l+1 distinct fixed l-torsion points from
`T.clauseC.torsion23_rational`? (only 6-torsion; l-torsion requires separate
existence) and choose one with l-coprime exponent.

## 4. Order after build resumes
1. S2432 import/binder fix + exact build.
2. S2420 clean build and axiom audit.
3. S1493 point-level map (subagent) + three-point transport.
4. Integrate into S2296ThreeRationalTwoTorsion / S2296LCoprimeRepresentative.
