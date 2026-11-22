# L0.2 Stage 1: Tate inverse-j, Delta/evaluator, closed source q_v, and Tate-parameter alignment

- package: `L0.2` (Tate/inverse-j; Layer0 node in `coord/LAYER1-PLAN.md:9`)
- stage: 1 (object/consumer/gap record). No Lean declaration is added by this package.
- owner files (read only in this package):
  - `LeanFormal/IUT/Foundations/PAdicAnalytic/TateDeltaIntegral.lean`
  - `LeanFormal/IUT/Foundations/PAdicAnalytic/TateInverseJNo1728.lean`
  - `LeanFormal/IUT/Foundations/NumberField/SourceQvClosed.lean`
  - `LeanFormal/IUT/Foundations/NumberField/SourceTateParameterAlignment.lean`
- production edits in this package: none. The only file written is this stage record.
- evidence version: working tree at Git `9399e9fab4d62ea5f78a4a0d56ceecb84525a3ee`
  (branch `master`), Lean `leanprover/lean4:v4.32.2`, Mathlib manifest rev
  `905b95818eb32af7874a58b427f50c1711a5e96c`. All four files are untracked
  (`??`) in this working tree; `Project.lean` is modified (` M`).
- target status: not `target_accepted`. No locked target, no comparator run,
  and no actual L0.4/L1 proof consumer of these modules was found.

## 1. Source target and exact objects

Source objects:

- IUT I, Definition 3.1(b): the local curve has split multiplicative reduction
  at the bad finite place.
- IUT I, Example 3.2(iv): the local Tate parameter `q_v` of `E_v/K_v`, with
  `q_v != 0`, `|q_v| < 1`; the source theta layer later uses `q_v^(1/2l)`
  only up to `mu_{2l}` ambiguity. Existing verified line record:
  `logs/coordination/source-place-partition-20261016.md:30`
  (IUT I Example 3.2(iv), text lines 3701-3731).
- The intended Lean carrier is a number field `F`, a finite place
  `v : NumberField.FinitePlace F`, a punctured elliptic curve
  `X : PuncturedEllipticCurve F`, and `hsplit : X.HasSplitMultiplicativeReductionAt v`.
  The local field used by the current chain is `K_v := NormalizedCompletion v`.

Quantifier shape actually formalized:

```text
forall (F) [Field F] [NumberField F],
forall (v : NumberField.FinitePlace F),
forall (X : PuncturedEllipticCurve F),
  X.HasSplitMultiplicativeReductionAt v ->
  Nonempty (SourceQv (K := NormalizedCompletion v)
    (X.baseChange (NormalizedCompletion v)).curve
    (X.baseChange (NormalizedCompletion v)).isElliptic)
```

Semantic warning: the original `q_v` is the Tate parameter of the local curve
`E_v/K_v`, not merely an element with the same `j`-invariant. The current
`SourceQv` records only the latter; `AlignedSourceTateParameter` upgrades it to
a variable change over the algebraic closure. This distinction is the main
remaining semantic gap below.

## 2. Exact declarations proved in the current working tree

Lean snippets below are ASCII transliterations for readability. Declaration
names, binder structure, and theorem conclusions are exact; the source files
use the corresponding Unicode notation (`forall`, `Nat`, `!=`, `<=`, `exists`,
`->`, `Int`, `Delta`, `c4` are displayed as ASCII here).

There is no `sorry`, `admit`, `axiom`, or `native_decide` token in the four
files (checked by content search). The four modules contain 38 public
declarations: 25 in `TateDeltaIntegral`, 1 in `TateInverseJNo1728`, 8 in
`SourceQvClosed`, and 4 in `SourceTateParameterAlignment`.

Declaration line map (current working tree):

| declaration | location |
|---|---|
| `integral_DeltaK` | `TateDeltaIntegral.lean:101` |
| `HK_coeff_norm_le_one_no1728` | `TateDeltaIntegral.lean:167` |
| `generalPSEval_DeltaK_eq_delta_no1728` | `TateDeltaIntegral.lean:196` |
| `generalPSEval_HK_eq_tateHK_no1728` | `TateDeltaIntegral.lean:249` |
| `tateHK_eq_q_add_generalTateR_no1728` | `TateDeltaIntegral.lean:274` |
| `exists_tateHK_eq_and_tateJK_eq_inv_no1728` | `TateInverseJNo1728.lean:24` |
| `SourceQv` | `SourceQvClosed.lean:50` |
| `normalized_large_j_of_completion_large_j` | `SourceQvClosed.lean:160` |
| `exists_sourceQv_at_finitePlace_closed` | `SourceQvClosed.lean:185` |
| `AlignedSourceTateParameter` | `SourceTateParameterAlignment.lean:60` |
| `exists_alignedSourceTateParameter` | `SourceTateParameterAlignment.lean:102` |
| `SourcePointUniformizationObligation` | `SourcePointUniformization.lean:107` |
| `TateWeierstrassPointData` | `TateUniformizationPointMap.lean:180` |


### 2.1 `TateDeltaIntegral.lean` (283 lines, 25 declarations)

Common context: `{K : Type u} [NontriviallyNormedField K] [CompleteSpace K]
[CharZero K] [IsUltrametricDist K]`, namespace
`LeanFormal.IUT.PAdicAnalytic.General`.

Endpoint declarations:

```lean
theorem integral_DeltaK (hint : forall n : Nat, ‖(n : K)‖ <= 1) :
    PowerSeriesIntegral (DeltaK (K := K))

theorem HK_coeff_norm_le_one_no1728
    (hint : forall n : Nat, ‖(n : K)‖ <= 1) (n : Nat) :
    ‖(HK (K := K)).coeff n‖ <= 1

theorem generalPSEval_DeltaK_eq_delta_no1728
    (hint : forall n : Nat, ‖(n : K)‖ <= 1) {q : K} (hq : ‖q‖ < 1) :
    generalPSEval (DeltaK (K := K)) q =
      (TateCurve.weierstrassCurve K q).Delta

theorem generalPSEval_HK_eq_tateHK_no1728
    (hint : forall n : Nat, ‖(n : K)‖ <= 1) {q : K} (hq : ‖q‖ < 1) :
    generalPSEval (HK (K := K)) q = tateHK (K := K) q

theorem tateHK_eq_q_add_generalTateR_no1728
    (hint : forall n : Nat, ‖(n : K)‖ <= 1) {q : K} (hq : ‖q‖ < 1) :
    tateHK (K := K) q = q + generalTateR (K := K) q
```

Other declarations (definitions, coefficient/integrality lemmas, and the
intermediate evaluation identities):

- `normalizedNumerator`, `DeltaK`, `HKno1728`, `sigmaDiv12`, `firstTermK`
- `zmod12_pow_three_eq_pow_five`,
  `sigma_three_modEq_sigma_five`,
  `twelve_dvd_five_sigma_three_add_seven_sigma_five`
- `sigmaDiv12_coeff`, `integral_sigmaDiv12`,
  `firstTermK_coeff`, `integral_firstTermK`
- `normalizedNumerator_eq_1728_mul_DeltaK`,
  `HKno1728_coeff_norm_le_one`,
  `DK_eq_DeltaK`, `HKno1728_eq_HK`, `integral_DK_no1728`
- `generalPSEval_normalizedNumerator_eq_c4_c6_no1728`,
  `generalPSEval_DK_eq_delta_no1728`,
  `eval_invOfUnit_C4K_cube_no1728`

What is actually proved: `DeltaK` is an integral formal q-series whose
evaluation at any `|q| < 1` is the Weierstrass discriminant of the canonical
q-series curve `TateCurve.weierstrassCurve K q`; `HK` is coefficient-integral;
the evaluation of `HK` is the Tate `H = Delta/c4^3`; and `tateHK` has the
remainder form `q + generalTateR q`. The no-1728 construction is
`HKno1728 = DeltaK * invOfUnit (C4K^3) 1`; `HKno1728_eq_HK` identifies it with
the older `HK`. The old `TateInverseJFinal` endpoint with
`h1728 : ‖(1728 : K)‖ = 1` still exists in the tree and is imported by
`Project.lean`, but the no-1728 endpoint above is the one used downstream.

### 2.2 `TateInverseJNo1728.lean` (115 lines, 1 declaration)

```lean
theorem exists_tateHK_eq_and_tateJK_eq_inv_no1728
    (hint : forall n : Nat, ‖(n : K)‖ <= 1)
    {t : K} (ht0 : t != 0) (ht1 : ‖t‖ < 1) :
    exists q : K, tateHK (K := K) q = t /\
      tateJK (K := K) q = t⁻¹ /\ ‖q‖ < 1
```

Proved by a strict contraction argument on `H(q) = q + R(q)` with
`‖R(q)‖ <= c^2` and `Lip(R) <= c` on the disk `‖q‖ <= c`, where
`c = (1 + ‖t‖)/2 < 1`. The proof uses `HK_coeff_norm_le_one_no1728` and
`tateHK_eq_q_add_generalTateR_no1728` from `TateDeltaIntegral`, plus
`exists_inverseJ_of_remainder`, `generalTateRemainder_norm_le_c_sq`, and
`generalTateRemainder_lipschitz_c`. This is an existence theorem; it does not
state uniqueness of the fixed point.

### 2.3 `SourceQvClosed.lean` (216 lines, 8 declarations)

Common context: `{K : Type u} [NontriviallyNormedField K] [CompleteSpace K]
[CharZero K] [IsUltrametricDist K]`, namespace
`LeanFormal.IUT.SourceQvClosed`.

```lean
structure SourceQv (E : WeierstrassCurve K) (hE : E.IsElliptic) where
  q : K
  q_ne_zero : q != 0
  q_norm_lt_one : ‖q‖ < 1
  canonical_is_elliptic : (TateCurve.weierstrassCurve K q).IsElliptic
  j_eq :
    letI : E.IsElliptic := hE
    letI : (TateCurve.weierstrassCurve K q).IsElliptic := canonical_is_elliptic
    E.j = (TateCurve.weierstrassCurve K q).j

def qSeriesH (q : K) : K :=
  (TateCurve.weierstrassCurve K q).Delta /
    (TateCurve.weierstrassCurve K q).c4 ^ 3

theorem tate_j_eq_inv_qSeriesH (q : K)
    (h : (TateCurve.weierstrassCurve K q).IsElliptic) :
    @WeierstrassCurve.j K _ (TateCurve.weierstrassCurve K q) h = (qSeriesH q)⁻¹

lemma qSeriesH_zero : qSeriesH (K := K) 0 = 0
```

Endpoint finite-place theorem:

```lean
theorem exists_sourceQv_at_finitePlace_closed
    (v : NumberField.FinitePlace F) (X : PuncturedEllipticCurve F)
    (hsplit : X.HasSplitMultiplicativeReductionAt v) :
    Nonempty (SourceQv (K := NormalizedCompletion v)
      (X.baseChange (NormalizedCompletion v)).curve
      (X.baseChange (NormalizedCompletion v)).isElliptic)
```

Supporting declarations:

- `exists_sourceQv` (general form; still carries an unused
  `(R : Type v) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Algebra R K] [IsFractionRing R K]` parameter; the finite-place wrapper
  supplies `CompletionIntegers v`);
- `exists_sourceQv_at_finitePlace` (conditional on explicit `hBridge` and
  `hint`);
- `normalized_large_j_of_completion_large_j` (transfers `1 < ‖x‖` from the
  completion norm to the normalized-completion norm on nonzero `x`).

The closed theorem is unconditional at the finite place: `hsplit` is the source
input, `hBridge` is supplied by
`LeanFormal.IUT.SourceTateParameter.norm_j_gt_one_of_splitMultiplicativeReductionAt`
(plus `normalized_large_j_of_completion_large_j`), and `hint` is supplied by
`LeanFormal.IUT.NumberFieldFinitePlace.normalizedCompletion_natCast_norm_le_one`.
No fixed `Q_5` curve and no `1728`-unit hypothesis is used.

### 2.4 `SourceTateParameterAlignment.lean` (165 lines, 4 declarations)

Common context: `{F : Type u} [Field F] [NumberField F]`, namespace
`LeanFormal.IUT.SourceTateParameterAlignment`.

```lean
theorem normalized_valued_lt_one_iff_norm_lt_one
    (v : NumberField.FinitePlace F) (q : NormalizedCompletion v) :
    (Valued.v (normalizedCompletionRingEquiv v q) :
        WithZero (Multiplicative Int)) < 1 <-> ‖q‖ < 1

abbrev canonicalTateCurve (v : NumberField.FinitePlace F)
    (q : NormalizedCompletion v) : WeierstrassCurve (NormalizedCompletion v) :=
  TateCurve.weierstrassCurve (NormalizedCompletion v) q

structure AlignedSourceTateParameter (v : NumberField.FinitePlace F)
    (X : PuncturedEllipticCurve F) where
  q : NormalizedCompletion v
  q_ne_zero : q != 0
  q_norm_lt_one : ‖q‖ < 1
  valued_lt_one :
    (Valued.v (normalizedCompletionRingEquiv v q) :
      WithZero (Multiplicative Int)) < 1
  canonical_is_elliptic : (canonicalTateCurve v q).IsElliptic
  local_is_elliptic : (X.baseChange (NormalizedCompletion v)).curve.IsElliptic
  local_j_eq_canonical :
    letI : (X.baseChange (NormalizedCompletion v)).curve.IsElliptic := local_is_elliptic
    letI : (canonicalTateCurve v q).IsElliptic := canonical_is_elliptic
    (X.baseChange (NormalizedCompletion v)).curve.j = (canonicalTateCurve v q).j
  C : WeierstrassCurve.VariableChange (AlgebraicClosure (NormalizedCompletion v))
  coordinateChange :
    C • ((X.baseChange (NormalizedCompletion v)).curve.map
        (algebraMap (NormalizedCompletion v) (AlgebraicClosure (NormalizedCompletion v)))) =
      (canonicalTateCurve v q).map
        (algebraMap (NormalizedCompletion v) (AlgebraicClosure (NormalizedCompletion v)))
  delta_normalization : ... -- Delta = C.u⁻¹ ^ 12 * local Delta
  c4_normalization : ...    -- c4 = C.u⁻¹ ^ 4 * local c4
  c6_normalization : ...    -- c6 = C.u⁻¹ ^ 6 * local c6
```

```lean
theorem exists_alignedSourceTateParameter
    (v : NumberField.FinitePlace F) (X : PuncturedEllipticCurve F)
    (hsplit : X.HasSplitMultiplicativeReductionAt v) :
    Nonempty (AlignedSourceTateParameter v X)
```

The alignment uses
`WeierstrassCurve.exists_variableChange_of_j_eq` after mapping both curves to
`AlgebraicClosure (NormalizedCompletion v)`; `IsSepClosed` is available there.
The `Delta/c4/c6` normalization equations are then derived from
`WeierstrassCurve.variableChange_Delta`, `variableChange_c4`, and
`variableChange_c6`. All three normalizations are over the algebraic closure,
not over `NormalizedCompletion v`.

## 3. Donors actually used

All donors below are present in the current working tree and were loaded by the
green replay build; they were not independently re-audited in this package.

| donor | declaration(s) | role |
|---|---|---|
| `PAdicAnalytic/TateQSeriesGeneral.lean` | `C4K`, `C6K`, `S3K`, `S5K`, `DK`, `HK`, coefficient lemmas | formal q-series objects used by the no-1728 construction |
| `PAdicAnalytic/TateJGeneral.lean` | `tateHK`, `tateJK`, `tateHK_mul_tateJK` | canonical H/J definitions and product relation |
| `PAdicAnalytic/PowerSeriesInvIntegral.lean` | `PowerSeriesIntegral`, `integral_C`, `integral_mul`, `integral_pow`, `integral_invOfUnit` | coefficient integrality of `DeltaK` and `HKno1728` |
| `PAdicAnalytic/GeneralPSEval.lean` | `generalPSEval`, `generalPSEval_mul`, `generalPSEval_pow`, `generalPSEval_C`, `summable_generalPSEval` | evaluation of formal series at `q` |
| `PAdicAnalytic/TatePSEvalIdentity.lean` | `generalPSEval_C4K_eq_c4_closed`, `generalPSEval_C6K_eq_c6_closed` | identification of formal c4/c6 with Weierstrass c4/c6 |
| `PAdicAnalytic/TateEstimatesGeneral.lean` | `generalTateRemainder`, `generalTateRemainder_norm_le_c_sq`, `generalTateRemainder_lipschitz_c` | quadratic remainder and Lipschitz estimates |
| `PAdicAnalytic/TateContractionGeneral.lean` | `exists_tateHGeneral_eq` | strict contraction fixed point |
| `PAdicAnalytic/GeneralInverseJAssembly.lean` | `norm_le_of_dist_le_sq`, `exists_inverseJ_of_remainder` | converts the H fixed point to the inverse-j witness |
| `Geometry/TateCurve.lean` | `TateCurve.weierstrassCurve` | canonical q-series Weierstrass curve |
| `Geometry/TateCurveArithmetic.lean` | `c4`, `c6`, `Delta`, `jInvariant`, `jInvariant_spec` | Weierstrass invariants of the canonical curve |
| `Geometry/LocalReduction.lean` | `HasSplitMultiplicativeReductionAt`, `HasSplitMultiplicativeReductionOnMinimalModel` | source local-reduction predicate |
| `NumberField/SourceTateParameterBridge.lean` | `norm_j_gt_one_of_splitMultiplicativeReductionAt` | split multiplicative reduction -> `1 < ‖j‖` |
| `NumberField/SourceIntegerNorm.lean` | `normalizedCompletion_natCast_norm_le_one` | discharges the inverse-j `hint` at a finite place |
| `ABCBridge/Geometry/FinitePlaceNormalizedIntegers.lean` | `normalizedCompletion_norm_lt_one_iff` | completion norm vs normalized norm |
| Mathlib `EllipticCurve/IsomOfJ.lean` | `WeierstrassCurve.exists_variableChange_of_j_eq` | same-j variable change over a separably closed field |
| Mathlib `EllipticCurve/Weierstrass.lean` | `variableChange_Delta`, `variableChange_c4`, `variableChange_c6` | normalization under a variable change |

Do not treat the Mathlib donor as a descent theorem: its signature requires
`[IsSepClosed F]` (Mathlib `IsomOfJ.lean:333`). That is exactly why the
alignment lives over `AlgebraicClosure (NormalizedCompletion v)`.

## 4. Actual consumer audit

Import-level facts (current working tree):

| consumer | import/use | status |
|---|---|---|
| `TateInverseJNo1728.lean` | imports `TateDeltaIntegral`; uses `HK_coeff_norm_le_one_no1728` and `tateHK_eq_q_add_generalTateR_no1728` | internal proof consumer |
| `SourceQvClosed.lean` | imports `TateInverseJNo1728`; uses `exists_tateHK_eq_and_tateJK_eq_inv_no1728` at line 96 | internal proof consumer |
| `SourceTateParameterAlignment.lean` | imports `SourceQvClosed`; uses `exists_sourceQv_at_finitePlace_closed` at line 106 | internal proof consumer; its own endpoint has no consumer |
| `SourcePointUniformization.lean` | imports `SourceQvClosed`; restates the closed q_v theorem at line 95 and uses the `SourceQv` type in `SourcePointUniformizationObligation` at lines 107-124 | statement-level consumer only; **not imported by any file and not in `Project.lean`** |
| `TateCurvePointMap.lean` | imports `TateDeltaIntegral`; uses `generalPSEval_DeltaK_eq_delta_no1728` at line 119 | internal proof consumer; only `Project.lean` imports this file, and no declaration consumes its results |
| `Project.lean` | imports at lines 51, 58, 59, 65, 185 | build coverage only; per AGENTS.md this is not a mathematical consumer |

There is no L0.4 or L1 Tate module that imports any of the four files:

- `IUTII/Frobenioid/Example36SourceLogKummerIdentification.lean` (L0.4/L1-F5/F6)
  constructs a separate fixed `sourceLocalField := Q_[l]` and does not import
  `SourceQvClosed` or `SourceTateParameterAlignment`.
- `Geometry/TateUniformizationPointMap.lean` (L1-F7) takes an abstract `q`
  and `TateWeierstrassPointData q`; it does not import the source q_v chain.
- `Geometry/TateGroupLaw.lean` likewise takes abstract `q` and point data; it
  does not import the source q_v chain.
- No file imports `SourceTateParameterAlignment` except `Project.lean`.
- No file imports `SourcePointUniformization`.

Consequence: the only concrete downstream statement that uses the closed q_v
result is `SourcePointUniformizationObligation`. That statement is a `Prop`
with no inhabitant, and the file is not integrated. The L0.2 chain therefore
does not currently reduce a premise of the claimed L0.4/L1 consumer; it is an
internal, Project-visible island. `AlignedSourceTateParameter` is entirely
unused.

What the source-level consumer still asks for (exact lines):

```lean
-- SourcePointUniformization.lean:118-120
exists C : WeierstrassCurve.VariableChange (NormalizedCompletion v),
  C • TateCurve.weierstrassCurve (NormalizedCompletion v) S.q =
    (X.baseChange (NormalizedCompletion v)).curve
```

This `C` is over `NormalizedCompletion v`, whereas
`AlignedSourceTateParameter.C` is over
`AlgebraicClosure (NormalizedCompletion v)`. That is the precise mismatch.

## 5. Precise gaps

1. **No local-field variable change (descent/twist gap).**
   `SourceQv.j_eq` gives only equality of `j`-invariants.
   `AlignedSourceTateParameter.C` is a
   `VariableChange (AlgebraicClosure (NormalizedCompletion v))`.
   The only concrete downstream statement
   (`SourcePointUniformizationObligation`) requires a
   `VariableChange (NormalizedCompletion v)`. Descent from the algebraic
   closure, or a proof that the relevant quadratic twist is trivial, is not
   present. Mathlib 4.32.2's same-j theorem is only available over
   `[IsSepClosed]`; no `quadraticTwist` or descent donor was found in the
   repository.

2. **The name `SourceQv.q` currently means "same-j q", not "identified Tate
   parameter".**
   The structure proves `q != 0`, `‖q‖ < 1`, canonical ellipticity, and
   `E.j = Tate(q).j`; it does not prove `E ≅ Tate(q)` over `K_v`. The
   original source `q_v` is a Tate parameter of `E_v`; the current object is
   a candidate witness for it. This is a semantic boundary, not a false Lean
   statement.

3. **Existence is not uniqueness/canonicity.**
   `exists_tateHK_eq_and_tateJK_eq_inv_no1728` and
   `exists_sourceQv_at_finitePlace_closed` return `exists` / `Nonempty`.
   They do not state that the q in the disk is unique, and they do not provide
   a canonical choice. Consumers that need a definite `q_v` (for example to
   define `q_v^Z` or a root) must choose a witness noncomputably. The
   contraction argument suggests uniqueness, but it is not a declaration.

4. **No point data, point bijection, or group law.**
   `SourcePointUniformizationObligation` additionally requires a
   `TateWeierstrassPointData` for the source q,
   `CanonicalTatePointMapBijectionObligation` (the
   `TateUniformizationPointMapGap`), and a group isomorphism
   `E(K_v) ≃+ K_v^x / q^Z`. None of these is proved. They are downstream of
   the local-field identification in gap 1, and belong to L1-F7 rather than
   L0.2.

5. **No source `2l`-th root / `mu_{2l}` data.**
   The original theta layer uses `q_v^(1/2l)` up to `mu_{2l}`
   (IUT I Example 3.2(iv)). `SourceQv` contains only `q`; there is no root,
   no `mu_{2l}`-torsor, and no compatibility with the theta packet. This is
   L0.5/L1-F8, not a requirement of the L0.2 inverse-j theorem, but it prevents
   reading `SourceQv.q` as the full source theta q_v.

6. **No L0.4 integration; the claimed consumer is absent.**
   L0.4 code does not import the chain. If a future L0.4 consumer needs only
   `ord(q)` or `‖q‖`, the missing statement would instead be a norm/valuation
   relation such as `‖tateHK q‖ = ‖q‖` for `0 < ‖q‖ < 1` (and hence
   `‖j(Tate q)‖ = ‖q‖⁻¹`). The repository only has the `q = l`-specific
   `TateJInvariantNorm` results, not this general relation. No such L0.4
   consumer currently exists either.

7. **Interface artifact.**
   `exists_sourceQv` carries an unused
   `(R : Type v) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
   [Algebra R K] [IsFractionRing R K]` parameter. The finite-place wrapper
   supplies `CompletionIntegers v`. This is not a mathematical gap, but it is
   an avoidable consumer-side obligation.

## 6. Smallest missing bridge

### 6.1 Bridge to the only existing downstream statement (recommended)

The smallest bridge that makes the proved L0.2 data usable by an existing
statement is a **local-field variable-change theorem**:

```lean
theorem exists_variableChange_sourceQv
    {F : Type u} [Field F] [NumberField F]
    (v : NumberField.FinitePlace F) (X : PuncturedEllipticCurve F)
    (hsplit : X.HasSplitMultiplicativeReductionAt v) :
    exists S : SourceQv (K := NormalizedCompletion v)
        (X.baseChange (NormalizedCompletion v)).curve
        (X.baseChange (NormalizedCompletion v)).isElliptic,
      exists C : WeierstrassCurve.VariableChange (NormalizedCompletion v),
        C • (X.baseChange (NormalizedCompletion v)).curve =
          TateCurve.weierstrassCurve (NormalizedCompletion v) S.q
```

Equivalently, define a `LocalAlignedSourceTateParameter` whose `C` is over
`NormalizedCompletion v` (not its algebraic closure). This is smaller than
point uniformization: it only identifies the two Weierstrass curves; it does
not assert `TateWeierstrassPointData`, injectivity/surjectivity, or the group
law.

Why this is the right smallest bridge:

- It is exactly the missing field in
  `SourcePointUniformizationObligation` (lines 118-120).
- It is exactly the boundary recorded by the prior consumer review
  (`logs/coordination/compute-priority-review-20261021.md:58-59`:
  "same-j; cannot replace actual local curve isomorphism or point
  uniformization" and "next step should handle local-field descent/twist").
- It does not require the full Tate uniformization theorem; it only requires
  the curve isomorphism over the local field.

What it does not solve: gaps 2 (semantic identification is only as strong as
the variable change), 4 (point map/group law), and 5 (2l-th root).

Honest proof boundary: no current donor proves this. The available same-j
theorem is over a separably closed field. A proof needs either a descent
argument for the variable change or a triviality argument for the quadratic
twist under split multiplicative reduction. That is a genuine child node, not
a mechanical import change.

### 6.2 Strictly weaker norm-level alternative (only if a consumer needs `ord`)

If the actual downstream need is only the valuation of `q` (the theta/volume
side often uses only `ord(q_v)`), the smaller statement is:

```lean
theorem norm_tateHK_eq_norm_q
    (hint : forall n : Nat, ‖(n : K)‖ <= 1) {q : K}
    (hq0 : q != 0) (hq : ‖q‖ < 1) :
    ‖tateHK (K := K) q‖ = ‖q‖
```

Together with `SourceQv.j_eq`, this gives
`‖E.j‖ = ‖q‖⁻¹`. It avoids descent/twist entirely, but no current L0.4 or
L1 file imports `SourceQv` to consume it. It is therefore not a substitute
for the consumer bridge in 6.1 unless the parent first fixes a real consumer.

## 7. Stage status and acceptance

- `statement_compiles`: **current working-tree artifacts are green**.
  `lake build LeanFormal.IUT.Foundations.NumberField.SourceTateParameterAlignment
  LeanFormal.IUT.Foundations.NumberField.SourcePointUniformization
  LeanFormal.IUT.Foundations.Geometry.TateCurvePointMap` exited 0,
  "Build completed successfully (3623 jobs)". The targets were replayed from
  current oleans; no fresh source-level re-elaboration was performed in this
  package.
- `proof_body_checked`: **not freshly re-checked from source in this package**.
  The current oleans are newer than the source files and the replay build
  accepted them. The four endpoint declarations were axiom-probed from the
  current environment (see below).
- `kernel_closed`: **not claimed at package level**. A transitive axiom probe
  on the four endpoints returned only
  `[propext, Classical.choice, Quot.sound]`; no full dependency audit or
  full `Project` build was run here.
- `target_accepted`: **not run**. There is no locked L0.2 target, no comparator
  invocation, and no source-semantic acceptance of `SourceQv.q` as the
  original `q_v`.

Axiom-probe command (stdin, no file written):

```text
import LeanFormal.IUT.Foundations.NumberField.SourceTateParameterAlignment
#print axioms LeanFormal.IUT.SourceQvClosed.exists_sourceQv_at_finitePlace_closed
#print axioms LeanFormal.IUT.SourceTateParameterAlignment.exists_alignedSourceTateParameter
#print axioms LeanFormal.IUT.PAdicAnalytic.General.exists_tateHK_eq_and_tateJK_eq_inv_no1728
#print axioms LeanFormal.IUT.PAdicAnalytic.General.generalPSEval_DeltaK_eq_delta_no1728
```

Actual output for each: `depends on axioms: [propext, Classical.choice,
Quot.sound]`. Exit 0.

## 8. File SHA/status and version caveats

All hashes are SHA-256 of the current working-tree file. "lines" is the
line-numbered file length used by the read tool.

| file | lines | SHA-256 | git status | role |
|---|---:|---|---|---|
| `PAdicAnalytic/TateDeltaIntegral.lean` | 283 | `765DAA10B2C10B5CA4A1B729E1FD5CD527EB23D0A1338F705F420240B9531D9A` | `??` untracked | proved donor |
| `PAdicAnalytic/TateInverseJNo1728.lean` | 115 | `2AC1C09360A9B2379BA1E9CB7FEADF39EEDCE869F1BF713C0DCF679A3F36070A` | `??` untracked | proved endpoint |
| `NumberField/SourceQvClosed.lean` | 216 | `7215A0DA7B788BD7037DF21E4EDFFF515DB2125B24D6E9FABD8147B48240AB26` | `??` untracked | proved endpoint |
| `NumberField/SourceTateParameterAlignment.lean` | 165 | `703A03BF1663909DCFE0779C585742D3CDAB858CD45E9162DEB214F69850595D` | `??` untracked | proved endpoint; no consumer |
| `NumberField/SourcePointUniformization.lean` | 141 | `EBAF74A72A851C6E706054C7B37595803807A68F0B39880D08DDFC2194D1C15F` | `??` untracked | statement consumer; not in `Project.lean` |
| `Geometry/TateCurvePointMap.lean` | 163 | `1209CB23C3E7C2EF319E39F3D40D71F8131B4EE3F1C4F04B84967B2E5885AEBE` | `??` untracked | uses Delta evaluation; only `Project.lean` imports it |
| `NumberField/SourceTateParameterBridge.lean` | 103 | `3B4F6DCF23EE2D9D1E6493CF72E88B6DC99AE68ABB098B2313467D9DE45741A2` | `??` untracked | donor |
| `NumberField/SourceIntegerNorm.lean` | 42 | `EFAFB8F687BC7CC544F1EF084BC566C37C4567BB102F5F2B53AC2D653EEEE63A` | `??` untracked | donor |
| `LeanFormal/IUT/Project.lean` | 573 | `A4FE7F2D91E64E26B21F7B6FFCBE311B11D568887DAE61562FDBCCDE27A70724` | ` M` modified (+353 lines) | imports the chain; not a consumer |

Additional version caveats:

- Git `HEAD` is `9399e9fa...`; `Project.lean` at HEAD contains none of
  `TateDeltaIntegral`, `TateInverseJNo1728`, `SourceQvClosed`,
  `SourceTateParameterAlignment`, or `TateCurvePointMap`. The current
  `Project.lean` is a working-tree modification with 353 added lines.
  The four L0.2 files plus `SourcePointUniformization`,
  `SourceTateParameterBridge`, and `SourceIntegerNorm` are untracked.
  A Git-only reproduction of this evidence is impossible without snapshotting
  the working tree.
- Five of the files are byte-identical to their
  `tmp/n8-20261018/general/` copies: `TateDeltaIntegral`, `SourceQvClosed`,
  `SourceTateParameterAlignment`, `SourcePointUniformization`, and
  `TateCurvePointMap`. `TateInverseJNo1728.lean` is **not** a byte copy:
  the production file is the 115-line SHA `2AC1...` version, while
  `tmp/n8-20261018/general/TateInverseJNo1728.lean` is a 138-line SHA
  `455B312615907C1E2E7DD61A87096920667939ED99FAC7A9D0FE6BD251075805`
  rewrite. Do not cite the tmp file as the current proof.
- `TateInverseJFinal.lean` (the older endpoint with
  `h1728 : ‖(1728 : K)‖ = 1`) is still imported by `Project.lean` at line 64.
  It is a second endpoint for the same inverse-j problem. Per the prior
  review, do not open another parallel wrapper around it; the no-1728 endpoint
  is the one consumed by `SourceQvClosed`.
- `SourceQvClosed` carries `set_option maxHeartbeats 1600000` unscoped and
  `SourceTateParameterAlignment` carries `set_option maxHeartbeats 1600000`;
  the build reports linter warnings for these style options, not errors.
- No full `Project` build was run in this package. The 2026-10-20 checkpoint
  (`logs/coordination/layer03-checkpoint-20261020.md:7`) records a
  `Project` exit 0 with 9431 jobs at that time; it is historical evidence for
  that working tree, not current acceptance. The current targeted replay is
  3623 jobs.

## 9. Node-local stage and next action

- Node `L0.2` stage 1: **this document**; scope, exact declarations, consumer
  audit, donors, and gaps fixed.
- Stage 2: not started for the bridge. No Lean declaration is added by this
  package.
- Stage 3: the four existing endpoints are proved in the current working tree;
  the package itself is not a target and is not `target_accepted`.
- Children / next action:
  - If the parent prioritizes the existing L1 point consumer, open a child
    node for the local-field variable-change theorem in 6.1 (descent/twist).
    Do not add another algebraic-closure alignment wrapper; the current one
    already exists and is unused.
  - If the parent prioritizes only the theta/volume `ord(q)` input, open a
    child node for the norm relation in 6.2, but first name the actual consumer;
    no current L0.4/L1 file imports the chain.
  - Do not claim L0.2 `target_accepted` or source-faithful `q_v` identification
    from the current four files.
