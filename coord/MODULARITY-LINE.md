# MODULARITY-LINE (ROUTES §10, route α)

Owner: stepxi. Status: active research line, no theorem claimed yet.
Rule: no sorry/axiom/True/PUnit; reused statements must be green citations; every Lean file must pass
single-file `lake env lean -o ...` and #print axioms gate trio.

## 1. Goal and current bottleneck

Route α aims at a modularity-method proof of the Szpiro/ABC boundary, replacing the
unproved "corrected Gap 2" input by an arithmetic bound on a modular parameterization
degree `δ_{N,1}`.

Target interface:
- our green boundary: `Mzk1FinalBoundarySzpiroActual.Szpiro6Shape logq logdf C := logq ≤ 6*logdf + C`;
- route-α modular input: an explicit degree bound
  `log δ_{N,1} ≤ (2+ε) log N + C`;
- bridge: Frey-curve arithmetic identifications
  `logq = 2 log δ`, `logdf = log N` (PENDING as a theorem; currently explicit hypotheses).

## 2. Inventory (read-only)

### 2.1 External FLT Lean tree
Path: `D:\lean\external\flt-lean-recon-20261016\FLT` (271 .lean files).
It is a **separate lake project**:
- toolchain `leanprover/lean4:v4.35.0-rc3` (our repo is v4.32.2);
- mathlib rev `c0da404748dcfaa230e6ad5f6599771d01e7ae56`;
- therefore NOT importable into this workspace. Use only as definition/theorem text reference.

Relevant modules and declarations:
- `FLT/Deformations/RepresentationTheory/GaloisRep.lean`: `GaloisRep`, `GaloisRep.ker`,
  `GaloisRep.det`, `GaloisRep.baseChange`, `GaloisRep.toLocal`, `GaloisRep.charFrob`,
  `GaloisRep.HasFlatProlongationAt`, `GaloisRep.toRepresentation`, `GaloisRep.IsIrreducible`.
- `FLT/Deformations/RepresentationTheory/GaloisRepFamily.lean`: `GaloisRepFamily`,
  `GaloisRepFamily.isCompatible`.
- `FLT/FreyCurve/FreyPackage.lean`: `FreyPackage` structure.
- `FLT/GaloisRepresentation/Automorphic.lean`: `GaloisRep.IsAutomorphicOfLevel`,
  `cyclic_base_change`.
- `FLT/GaloisRepresentation/HardlyRamified/Frey.lean`:
  `FreyCurve.torsion_isHardlyRamified`, `FreyCurve.torsion_not_isIrreducible`.

### 2.2 Internal green vendor trees (importable candidates)
Counts: EllipticCurves 480, CurvesJacobian 590, Heights 64, WeilCurves 49.

Green declarations worth reusing:
- `EllipticCurves/Reduction/NeronOggShafarevich.lean`:
  `neronOggShafarevich_galoisRep_eq_one`,
  `neronOggShafarevich_galoisRepMod_eq_one`.
- `Heights/Absolute/Basic.lean`: `logHeight`, `logHeight_nonneg`, `logHeight_zero`,
  `logHeight_smul`, `logHeight_mul_table`, `logHeight_one_add_le`,
  `finrank_mul_logHeight_eq_sum`.
- `Heights/Certificates.lean`: `ArchimedeanPeriodData`, `IsIntegralAt`,
  `IsLocalMinimalDiscriminantExponent`, `GlobalMinimalDiscriminantData`,
  `exists_archimedeanPeriodData`, `exists_localMinimalDiscriminantExponent`,
  `exists_globalMinimalDiscriminantData`.
- `Heights/ArchimedeanAlgebraicRealization.lean`:
  `ArchimedeanPeriodData.variableChangeToLatticeCurve`,
  `..._differentialDenominator`, `..._differentialCoefficient`,
  `ArchimedeanPeriodData.latticeCurvePointAddEquiv`.
- `CurvesJacobian`: `FittingZero.lean`, `SerreCriterion.lean`, `SerreS2.lean`,
  `ArithDecomp.lean`, `ArithmeticFill.lean` (further screening needed for periods/differentials).
- `WeilCurves`: `Automorphism.lean`, `Bound.lean`, `PoleOrder.lean`,
  `Genus.lean`, `Divisor.lean`, `Picard.lean` (Weil-pairing/differential prerequisites,
  not yet wired to heights).

## 3. Route-α precise statement

### (a) Modular parameterization degree δ
For an elliptic curve `E/Q` of conductor `N` with a modular parameterization
`φ : X_0(N) → E`, define
`δ_{N,1}(E) : ℕ := deg(φ)` (normalized as in Ribet–Takahashi).
Current Lean: **no definition**. PENDING.

### (b) Ribet–Takahashi ratio formula
Paper form:
`h(E) = (1/2) log δ_{N,1}(E) - log ‖f_E‖ + O(1)`
where `f_E` is the normalized newform. Current Lean: **not formalized**. PENDING.
Need: weight-2 newform, Petersson norm, real period; candidate greens:
`Heights/ArchimedeanAlgebraicRealization.lean` differential/period data.

### (c) Bridge proposition (formal target)
For each `ε > 0` there is `C` such that for every Frey curve `E/Q` with conductor `N`
and modular degree `δ_{N,1}`,
`log δ_{N,1} ≤ (2+ε) log N + C`
implies `Szpiro6Shape (logq_E) (logdf_E) C'` for an explicit `C'` depending on `C`
and on `log N`; under the normalized Frey relations
`logq_E = 2 log δ_{N,1}`, `logdf_E = log N`, and `0 ≤ ε ≤ 1`, the explicit choice
`C' = 2*C` works.
PENDING: the arithmetic identification of `logq/logdf` with `log δ/log N`.
PROVED (Lean, real arithmetic only): see `Mzk1ModularityBridgeActual.lean`.

### (d) Status table

| item | status |
|---|---|
| external FLT GaloisRep/FreyPackage/Automorphic reference | READ-ONLY, not importable (different toolchain) |
| internal green heights/period/discriminant assets | AVAILABLE |
| modular degree δ definition | PENDING |
| Ribet–Takahashi `h(E)` formula | PENDING |
| Frey identifications `logq=2logδ`, `logdf=logN` | PENDING |
| real-arithmetic bridge δ-bound ⇒ Szpiro6Shape | PROVED (conditional) |
| unconditional Szpiro/ABC via route α | NOT PROVED |

## 4. Next steps
1. Freeze a Lean interface for `ModularParameterizationDegree` and `NewformPeterssonNorm`
   using Mathlib modular forms if available; otherwise explicit named structure.
2. Port only compile-compatible definitions from internal `Heights`/vendor trees;
   do not copy external FLT code.
3. Prove the Frey relation as a separate arithmetic module (currently PENDING).
4. Feed the bridge lemma into `Mzk1FinalBoundarySzpiroActual`.


## 5. A787 external FLT migration (toolchain)

Tools used: `tools/xif_external_port.ps1` (-Analyze/-Port/-Compile), plus manual
minimal fixes when a 4.35 API rename has no 4.32 counterpart.

### Analyze
- targets: 5; import closure: 131 files; missing prerequisites: 17 (parser noise in
  comments plus real Mathlib module drift).
- version diff: external `leanprover/lean4:v4.35.0-rc3` / mathlib
  `c0da4047...`; ours `v4.32.2` / `905b9581...`.
- report: `tmp/external/ported/flt/import_chain.md`.

### Port
- 131 files ported to `tmp/external/ported/flt` with internal imports rewritten to
  `tmp.external.ported.flt.*`, Mathlib imports resolved against our pin, and
  attribution headers retained.
- `tools/port_fix_rules.txt` extended (backup `.bak-a787`) with:
  - `module` line removal; `public import` -> `import`;
  - `@[expose] public section` -> `section`; `public section` -> `section`;
  - `Ideal.isMaximal_under_of_isIntegral_of_isMaximal` ->
    `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal`;
  - `Ideal.isMaximal_of_isIntegral_of_isMaximal_under` ->
    `Ideal.isMaximal_of_isIntegral_of_isMaximal_comap`.
- Manual fixes (not generic rules):
  - `FLT/Mathlib/Topology/Algebra/Group/Basic.lean`: missing
    `Mathlib.Topology.Algebra.Group.Neighborhood` replaced by
    `Group.Basic` + `Group.Quotient`;
  - `FLT/Mathlib/GroupTheory/Index.lean`: mid-file `public meta import ToDual`
    removed, `import Mathlib.Tactic.ToDual` put at top;
  - `FLT/Deformations/RepresentationTheory/Frobenius.lean`: `Ideal.under_def`
    bridge to renamed `isMaximal_*_comap`;
  - `FLT/Deformations/Lemmas.lean`: `dite_eq_right` -> `dif_neg`.
- Current ported compile: topo order files 1-8 EXIT=0. File 9
  `IntegralClosure.lean`: after `Ideal.eq_bot_of_under_eq_bot` ->
  `Ideal.eq_bot_of_comap_eq_bot`, remaining goal is an injectivity side condition
  for `Algebra.IsInvariant`; PENDING (not faked).



### A823 file 9 update (`IntegralClosure.lean`)
- first error: line 88 `instance isInvariant_integralClosure`, goal
  `Function.Injective (algebraMap K L)` left by the external proof's
  `obtain ⟨x, rfl⟩ := Algebra.IsInvariant.isInvariant ...`.
- diagnosis: in mathlib v4.32.2, `Algebra.IsInvariant` has field
  `isInvariant : ∀ b, (∀ g, g • b = b) → ∃ a, algebraMap a = b`; the v4.35 proof
  relies on a field-extension `FaithfulSMul K L` instance that v4.32.2 does not
  synthesize here. A local `FaithfulSMul`/explicit witness is needed, plus
  `Subtype.ext` because `IntegralClosure` is the `integralClosure` subtype.
- attempted: replaced the `rfl` pattern by explicit `y, hy := Algebra.IsInvariant.isInvariant`
  and `rw [← hy]`; remaining goal is a subtype equality under `IntegralClosure`
  coercion (PENDING, not faked). `Ideal.eq_bot_or_eq_top` is also absent under
  that name in v4.32.2.
- status: files 1-8 EXIT=0; file 9 PENDING.
