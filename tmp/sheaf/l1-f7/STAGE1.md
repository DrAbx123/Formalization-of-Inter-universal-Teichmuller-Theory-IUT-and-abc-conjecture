# L1-F7 Stage 1 — Tate uniformization: point map, theta transform, group law

- package: `L1-F7`
- stage: 1 (exact target, actual consumer, green donors, precise gaps, smallest next statement)
- date: 2026-10-22
- production edits: **none**. This package writes only this file.
- sources read in full: `Example36TateUniformization.lean`, `TateGroupLaw.lean`, `TatePointLocal.lean`; consumers and donors listed in §3–§4.
- compilation/axiom re-runs: **none in this package**. "Green" below means: current working-tree source has no textual `sorry`/`admit`/`axiom`, and a prior `.olean` artifact exists with timestamp later than the source. This is not a substitute for a current build or a transitive axiom audit; none is claimed.

Node-local staging follows `coord/FRACTAL-STAGES.md`: L1-F7 is stage 1 here; it does not gate S1/S2/F1–F6/F8.

## 0. Owned files and current SHA/status

All paths are relative to `D:/lean`. `status` is `git status --porcelain` for the file; the repository HEAD is `9399e9fab4d62ea5f78a4a0d56ceecb84525a3ee` (2026-08-15), and these files are untracked, so the SHA is the current working-tree content.

| file | lines | SHA256 | git status | prior olean |
|---|---|---|---|---|
| `LeanFormal/IUT/IUTII/Frobenioid/Example36TateUniformization.lean` | 1095 | `5D8DCFFDE08D3414AB01042E4BC6C8F1DECB970BFE692F8F8AFD855BBCF12504` | untracked (`??`) | 2026-10-20 03:35:08 |
| `LeanFormal/IUT/Foundations/Geometry/TateGroupLaw.lean` | 142 | `0C247E93FC07E6C863D861B918869954F6F39D8FDA9AFE6E25A00DB7C94864C0` | untracked (`??`) | 2026-10-20 08:27:51 |
| `LeanFormal/IUT/Foundations/Geometry/TatePointLocal.lean` | 97 | `3E3F9C69A9CFAB90E86A4DC2C23DEF55F4AC24F78154A2056B4C22FE648298C3` | untracked (`??`) | 2026-10-20 08:25:00 |

Immediate support files named in this record:

| file | lines | SHA256 | git status | prior olean |
|---|---|---|---|---|
| `LeanFormal/IUT/Foundations/Geometry/TateUniformizationPointMap.lean` | 257 | `CCE4967CC073FAF7173A1469765D5C37D540ED61507314DFE3AA17FEBEE9FE36` | untracked | 2026-10-18 05:55:56 |
| `LeanFormal/IUT/Foundations/Geometry/TateUniformizationPointMapReduction.lean` | 147 | `462B50BBD9B387E9A6B6F6507F2FB27CE2196FB8DD973F9AF66423533775A806` | untracked | 2026-10-18 05:56:11 |
| `LeanFormal/IUT/Foundations/Geometry/TateUniformizationBaseChange.lean` | 265 | `29950230321552B7AAE6A0745BAEB125BA1F2D64D4FAA6CB94787A1880253670` | untracked | 2026-10-18 05:56:26 |
| `LeanFormal/IUT/Foundations/Geometry/TateUniformizationContract.lean` | 160 | `12AEE482DCFA56A88621C9651563CD9F6F37D092E2BF46614DC481AE1F950C82` | untracked | 2026-10-16 01:50:57 |
| `LeanFormal/IUT/Foundations/Geometry/TatePointQuotientBoundary.lean` | 216 | `2B8EF15A883C23CAFDF68880E0AAF004C8EFB64FE7B0570E1A59BFDAEAD909EA` | untracked | 2026-10-16 04:22:38 |
| `LeanFormal/IUT/Foundations/Geometry/TateInverseJUniformization.lean` | 206 | `4850632CF4BD32FCE486B28D30A40A7CC19714D131A6C74D693BC15DE8842457` | untracked | present; **not imported anywhere** |
| `LeanFormal/IUT/Foundations/NumberField/SourcePointUniformization.lean` | 141 | `EBAF74A72A851C6E706054C7B37595803807A68F0B39880D08DDFC2194D1C15F` | untracked | 2026-10-20 08:16:59; **not imported anywhere** |
| `LeanFormal/IUT/Foundations/NumberField/SourceQvClosed.lean` | 214 | `7215A0DA7B788BD7037DF21E4EDFFF515DB2125B24D6E9FABD8147B48240AB26` | untracked | 2026-10-20 08:09:06 |
| `LeanFormal/IUT/Foundations/NumberField/SourceTateParameterAlignment.lean` | 165 | `703A03BF1663909DCFE0779C585742D3CDAB858CD45E9162DEB214F69850595D` | untracked | present; Project import only |
| `LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceSourceAlgebraicClosure.lean` | 83 | `6392D86FBD1FE6A353A0B91D55EE3B3CFEBA5F345B70C1DB28A077A843167596` | untracked | 2026-10-17 08:13:10 |

## 1. Source target

Classical Tate uniformization at a split multiplicative place, as used by IUT I,
Definition 3.1(b)(c) and Example 3.2(iv): a q-parameter q, a Weierstrass
coordinate change identifying the local curve E with the canonical q-series Tate
curve, and a Galois-equivariant group isomorphism
`(Kbar)^x / q^Z  ~=  E(Kbar)` (equivalently, the q^Z-periodic point map on the
parameter quotient is bijective onto the nonzero points and respects the group
law). The tree records this as the exact contract
`CurveIndexedTateUniformization` (interface, no constructor).

The file `Example36TateUniformization.lean` records the same target at the
concrete split place above 5, including the explicit statement that the analytic
curve/point/theta section theorems are absent (module header, lines 23–58; audit
obligation, lines 415–488).

## 2. Exact target decomposition

### 2.1 T1 — consumer-facing structure (exact fields)

`LeanFormal/IUT/Foundations/Geometry/TateUniformizationContract.lean:88`:

```lean
structure CurveIndexedTateUniformization
    {F : Type u} [Field F] [NumberField F]
    (X : PuncturedEllipticCurve F)
    (place : NumberField.FinitePlace F)
    (parameter : NumberFieldFinitePlace.FinitePlaceQCandidate place) where
  canonicalIsElliptic :
    (TateCurve.weierstrassCurve (Completion place) parameter.q).IsElliptic
  coordinateChange : WeierstrassCurve.VariableChange (Completion place)
  realizesCurve :
    coordinateChange •
        TateCurve.weierstrassCurve (Completion place) parameter.q =
      (X.baseChange (Completion place)).curve
  pointUniformization :
    let localCurve := X.baseChange (NumberFieldFinitePlace.Completion place)
    letI : localCurve.curve.IsElliptic := localCurve.isElliptic
    ((AlgebraicClosure (NumberFieldFinitePlace.Completion place))ˣ ⧸
      Subgroup.zpowers
        (NumberFieldFinitePlace.tateParameterUnit
          place parameter.q parameter.q_ne_zero)) ≃*
      Multiplicative localCurve.AlgebraicClosurePoint
  pointUniformization_galoisEquivariant :
    let localCurve := X.baseChange (NumberFieldFinitePlace.Completion place)
    letI : localCurve.curve.IsElliptic := localCurve.isElliptic
    ∀ (sigma :
        AlgebraicClosure (NumberFieldFinitePlace.Completion place) ≃ₐ[
          NumberFieldFinitePlace.Completion place]
        AlgebraicClosure (NumberFieldFinitePlace.Completion place))
      (x : (AlgebraicClosure
        (NumberFieldFinitePlace.Completion place))ˣ),
      pointUniformization
          (QuotientGroup.mk
            (Units.map sigma.toRingEquiv.toMonoidHom x)) =
        Multiplicative.ofAdd
          (localCurve.galoisActionOnPoint sigma
            (pointUniformization (QuotientGroup.mk x)).toAdd)
```

The equivalent comparison structure is
`TateCurveComparison` (`TatePointQuotientBoundary.lean:124`) with fields
`canonicalIsElliptic`, `coordinateChange`, `realizesCurve`, and
`points : TatePointComparison X place parameter`; the point half is
`TatePointComparison` (`:25`) with exactly `pointEquiv` and
`galois_naturality`. `TateCurveComparison.toUniformization` is
`TatePointQuotientBoundary.lean:161`; the reverse bridge is
`SourcePlaceTateComparisonSynthesis.lean:54` (`ofUniformization`).

### 2.2 T2 — concrete target at the place above 5

`LeanFormal/IUT/Foundations/Geometry/TateInverseJUniformization.lean:143`:

```lean
def TateInverseJUniformizationInterface : Prop :=
  ∃ (parameter : NumberFieldFinitePlace.FinitePlaceQCandidate concreteFivePlace),
    Nonempty (CurveIndexedTateUniformization
      concreteSplitPuncturedCurve concreteFivePlace parameter) ∧
    ‖parameter.q‖ = (5 : ℝ)⁻¹
```

This is the exact concrete target: p = concreteFivePlace, E =
`concreteSplitPuncturedCurve` (the curve y^2 + xy = x^3 + 5 over Q), q of norm
1/5. The definition has **no inhabitant** and — note — `TateInverseJUniformization.lean`
is not imported by any file and not in `Project.lean`; it is a statement fragment,
not a wired consumer target.

The two component predicates already exist: `HasTateCoordinateChange` (`:91`)
and `HasTatePointUniformization` (`:100`), and
`curveIndexedTateUniformization_implies_interface` (`:124`) proves that a
contract gives both. The converse is not proved.

### 2.3 T3 — generic point-map target (current Lean statement)

`LeanFormal/IUT/Foundations/Geometry/TateUniformizationPointMap.lean:248`:

```lean
def TateUniformizationPointMapGap {K} [NormedField K] [CharZero K] (q : K)
    (parameterNeZero : q ≠ 0) (hdata : TateWeierstrassPointData q) : Prop :=
  Function.Injective (tateQuotientPoint q parameterNeZero hdata) ∧
    ∀ P : (weierstrassCurve K q).toAffine.Point, P ≠ 0 →
      ∃ w : TateParameterQuotient q parameterNeZero,
        tateQuotientPoint q parameterNeZero hdata w = P
```

The pair-level equivalent form is
`tatePairCoordinatesSeparateOrbits q ∧ tateCoordinatesCoverNonzeroPoints q`
(`TateUniformizationPointMapReduction.lean:37,46,129`). The second conjunct is
exactly the SHEAF §7 requirement "X(u)=x is required only for actual curve
points (x,y)": every nonsingular affine point is the image of a legal parameter.

**Normalization defect (must be handled before this is the classical target).**
`TateWeierstrassPointEquation.lean:4–14` states, and
`TateCoordinateNormalization.lean:67–111` makes precise, that the raw series
`tateWeierstrassX = coordinateSeries`, `tateWeierstrassY = yCoordinateSeries`
are **not** the coordinates of the canonical Tate equation. The canonical
coordinates are

```lean
normalizedTateX q u = tateWeierstrassX q u - 2 * tateCoordinateCorrection q
normalizedTateY q u = tateWeierstrassY q u + tateCoordinateCorrection q
```

and the exact equation statement for them is the *equivalence*
`normalizedTate_equation_iff_oddSeries`
(`TateCoordinateNormalization.lean:96`), whose right-hand side is the classical
odd-coordinate (sigma/theta) identity. The identity itself is not proved.
Consequently `TateUniformizationPointMapGap` is a conditional statement about the
raw pair on the unshifted curve `weierstrassCurve K q`; it is not yet the
classical Tate point map. The canonical target must be stated with
`normalizedTateX/Y` (see F7a in §6). `TateGroupLaw.tateNormalizationPointEquiv`
(`:45`, additive, `:57`) is the green bridge between the shifted raw curve and
the canonical curve, but it is not used by the raw point map.

### 2.4 T4 — group-law target (not yet a Lean declaration)

There is no multiplication on `TateParameterQuotient`/`TatePointCompletion`.
`TateGroupLaw` only defines
`tatePointGroupLaw := tateCompletionAdd (tatePointBijection ... hgap)`
(`:120–125`), i.e. the curve group law transported along the *hypothetical*
bijection `hgap`. That is a transport of the curve law, not the natural
parameter law; it is exactly the substitution SHEAF §7 forbids
("不以搬运定义的群律……替换原目标"). `tatePointBijection_add` (`:127`) is the
tautological compatibility of that transport. No theorem relates it to
multiplication in `K^x/q^Z`.

The precise target statement is:

```lean
-- x * y is multiplication in the deck quotient K^x / q^Z
theorem tateUniformization_add
    {K : Type*} [NormedField K] [CompleteSpace K] [CharZero K]
    (q : K) (hq0 : q ≠ 0) (hdata : TateWeierstrassPointData q)
    (x y : Kˣ ⧸ Subgroup.zpowers (Units.mk0 q hq0)) :
    completionPoint q hq0 hdata (deckEquiv x * deckEquiv y) =
      completionPoint q hq0 hdata (deckEquiv x) +
        completionPoint q hq0 hdata (deckEquiv y)
```

where `deckEquiv : Kˣ/q^Z ≃ Option (TateParameterQuotient q hq0)` is F7b below
and `completionPoint` extends `tateQuotientPoint` by `none ↦ 0`. This is the
classical theta addition theorem; nothing in the tree proves it. The
`tatePointGroupLaw` transport above cannot be used as a substitute.

### 2.5 T5 — theta transform target

What is exact and green in the target file:

- q |-> q^2 transport: `transportParameter` (`:306`), `transportDomain`
  (`:318`), `thetaTransport` (`:328`), `transportParameter_q_ne` (`:331`);
- two one-sided Tate theta sums on the rigid annulus: `positiveTerm`,
  `negativeTerm`, `positiveTerm_summable` (`:245`),
  `negativeTerm_summable` (`:283`), `positiveSeries`, `negativeSeries`,
  `thetaSeries` (`:291–293`), `hasSum_thetaSeries_split` (`:300`);
- q-expansion/special-value identification:
  `thetaQExpansionCoefficient` (`:355`),
  `thetaQExpansionCoefficient_eq_realThetaValue` (`:358`),
  `thetaQExpansionCoefficient_eq_sourceTheaterScale` (`:364`),
  `transportThetaQExpansionCoefficient_eq_square` (`:378`);
- summary: `tateThetaSeries_actual_summary` (`:394`).

Adjacent green theta-power laws (source side, F4):
`realThetaValue_pow_q` (`Example36SourceThetaDivisor.lean:487`),
`thetaUnit_transport` (`:495`), and the actual theta-function shift law
`OddTheta.oddTheta_shift` (`Foundations/Theta/OddThetaShift.lean:14`).

Precise theta gap: there is **no series-level theorem** relating
`thetaTransport` to `thetaSeries`; `thetaTransport` is a bare definition with
no property. There is also no identification of `thetaSeries` with the source
theta function / line-bundle section. The genuine theta transformation law of an
actual theta function in the tree is `oddTheta_shift` (F4), not a property of
`TateRigidTheta.thetaSeries`. The source-side q |-> q^2 transport that the
source-theta card actually consumes is `Example36SourceThetaGenerator.analyticThetaTransport`
(`:140`, inhabited in `analyticDistinctThetaHistoryData`, `:234`), **not**
`TateRigidTheta.thetaTransport`. Thus T5 currently has no production consumer and
is a prune candidate for F7 (see G7).

## 3. Consumers — actual import and declaration-level audit

Direct imports of the three owned files:

| consumer | line | kind | declaration use |
|---|---|---|---|
| `LeanFormal/IUT/IUTII/Frobenioid/Example36TateInverseJCanonical.lean` | 1 | import | uses `canonicalQSeriesJ` (`:24,55,67,78`) and `concreteSplitCurveLocal_j_eq` (`:70`) from `Example36TateUniformization` |
| `LeanFormal/IUT/Project.lean` | 530 | aggregator | import only (`Example36TateUniformization`) |
| `LeanFormal/IUT/Project.lean` | 441 | aggregator | import only (`TateGroupLaw`); **zero declaration consumers** |
| `LeanFormal/IUT/Project.lean` | 440 | aggregator | import only (`TatePointLocal`); **zero declaration consumers** |

`TateQSeriesAnalytic.lean:22` mentions `Example36TateUniformization` only in its
module comment; it does not import the module.

Consumer chain of the *boundary/contract*, not of the three owned files:

1. `TateCurveComparison`/`TatePointComparison` (`TatePointQuotientBoundary.lean`,
   Project:210).
2. `InitialThetaTateComparison` (`LeanFormal/IUT/IUTI/InitialTheta/TateComparisonBoundary.lean:23`,
   Project:233) — field `curveComparison : TateCurveComparison ...`; it has
   **no constructor** ("a genuine Tate comparison must be supplied by the
   source-faithful C-layer proof", header lines 11–14).
3. `SourceLocalTateBoundary` (`SourceLocalTateBoundary.lean:24`, Project:234) —
   its field `comparison : InitialThetaTateComparison`; this is the leaf of the
   Project-wired chain. No inhabitant of either structure exists.
4. Independent D4 branch (current tree, **not imported by Project**):
   `BadPlaceTateUniformizationCards`
   (`SourcePlaceQParameterUniformization.lean:70`), whose field
   `comparison : ∀ w hw, TateCurveComparison A.curve w (parameter w hw)`
   (`:74–76`); its `uniformization` is the derived
   `CurveIndexedTateUniformization` (`:86`). It is consumed by
   `SourcePlaceTateComparisonSynthesis.lean:98,115,145` (`BadPlaceUniformizationContract`,
   Clause (b) assembly) and then by `SourceDefinition31D4D9Supply.lean:99,107`
   (`D4ReductionSupply.tateUniformization`), `SourceDefinition31D4TateQIdentification.lean`
   (`TateQIdentificationStatement`, lines 231–234) and
   `SourceDefinition31D4FKDescentBridge.lean` (no importer). All are olean-present
   but outside `Project.lean`.

Exact consumer gap: every path above needs an inhabitant of
`TateCurveComparison X place parameter`, equivalently of
`CurveIndexedTateUniformization`. **None exists.** No consumer uses
`TateGroupLaw` or `TatePointLocal` declarations directly; no consumer uses
`TateRigidTheta.thetaTransport`.

## 4. Green donors (current tree; prior-build artifacts only)

### 4.1 Curve / q-series / concrete objects

- `TateCurve.weierstrassCurve`, `a4`, `a6`
  (`Foundations/Geometry/TateCurve.lean`).
- Ellipticity of the general Tate curve:
  `TateCurvePointMap.tateWeierstrassCurve_isElliptic_of_norm`
  (`TateCurvePointMap.lean:159`), via `tateCurve_Δ_ne_zero` (`:123`).
- Concrete q = 5: `concreteFiveTateParameter`
  (`Example36TateUniformization.lean:99`), `concreteFiveTateCurve` (`:119`),
  `concreteFiveTateCurve_isElliptic` (`:132`), `concreteFiveTateCurve_delta_norm`
  (`:142`), `concreteFiveTateCurve_c4_norm` (`:152`),
  `concreteFiveQCandidate` (`:167`), summary (`:198`).
- Concrete split curve: `concreteSplitPuncturedCurve`
  (`ConcreteSplitMultiplicativeCurve.lean:61`),
  `concreteSplitCurveLocal_j_eq` (`Example36TateUniformization.lean:570`),
  `concreteSplitPuncturedCurve_hasSplitMultiplicativeReductionAt_five`
  (`ConcreteSplitCurveFivePlace.lean:126`).
- Inverse-j q at the concrete split place:
  `Example36TateInverseJCanonical.exists_canonicalQSeriesJ_eq_split_j`
  (`:21`) and `..._full` (`:75`) — q != 0, `canonicalQSeriesJ q =
  concreteSplitCurveLocal.j`, `||q|| = 1/5`, `dist q (-5) <= 1/25`. This is
  model-only q-series data (no coordinate change, no point map).
- Negative result pruning the naive candidate:
  `five_not_qSeriesInverseJParameter` (`Example36TateUniformization.lean:1064`)
  proves q = 5 is not an inverse-j parameter; the 5*j residues are +1 (Tate at
  q=5) vs -1 (split curve).

### 4.2 Point map / coordinates / periodicity

- Kernel series and summability: `TateCoordinateSeries.coordinateKernel`,
  `coordinateKernel_int_summable`, `coordinateSeries`,
  `coordinateSeries_zpow_mul_parameter`; `TateYCoordinateSeries.yCoordinateKernel`,
  `yCoordinateKernel_int_summable`, `yCoordinateSeries`;
  `TateCoordinatePeriodicity` for the three period/inversion laws.
- Raw point equation and nonsingularity decomposition:
  `TateWeierstrassPointEquation.tateWeierstrassEquation` (`:189`),
  `tateWeierstrassEquation_iff_oddSeries` (`:209`),
  `tateWeierstrassNonsingular_iff` (`:265`), `tateWeierstrassPointAt` (`:281`).
  (These prove equivalences; they do **not** prove the odd-series identity.)
- Quotient carrier and point map: `coordinateParameterDomain`,
  `tateParameterSetoid`, `TateParameterQuotient`,
  `tateWeierstrassX_eq_of_orbitRel`, `tateWeierstrassY_eq_of_orbitRel`,
  `tateQuotientX`, `tateQuotientY`, `TateWeierstrassPointData`,
  `tateDomainPoint`, `tateQuotientPoint`, `tateQuotientPoint_mk`,
  `tateQuotientPoint_orbit`, `tateQuotientPoint_ne_zero`.
- Reduction of the gap to coordinate conditions:
  `tatePairCoordinatesSeparateOrbits`, `tateCoordinatesCoverNonzeroPoints`,
  `tateQuotientPoint_injective_iff_pairCoordinatesSeparateOrbits`,
  `tateQuotientPoint_surjective_iff_coordinatesCoverNonzeroPoints`,
  `tateUniformizationPointMapGap_iff_pairConditions`.
- Base-change naturality (on the image of a continuous field homomorphism):
  `lambertSeries_map`, `a4_map`, `a6_map`, `weierstrassCurve_map`,
  `tateWeierstrassX_map`, `tateWeierstrassY_map`,
  `coordinateParameterDomain_map_iff`, `tateWeierstrassNonsingular_map`,
  `tateParameterQuotientMap`, `tateQuotientPoint_map_mk`.
- Normalization bridge: `TateCoordinateNormalization.normalizedTateX` (`:41`),
  `normalizedTateY` (`:45`), `normalizedTateX_zpow_mul_parameter`,
  `normalizedTateY_zpow_mul_parameter`, `normalizedTate_equation_iff_oddSeries`
  (`:96`); `TateGroupLaw.tateNormalizationVariableChange` (`:20`),
  `tateNormalizationCurve` (`:40`), `tateNormalizationPointEquiv` (`:45`),
  `tateNormalizationPointEquiv_add` (`:57`).

### 4.3 Quotient / Galois / deck action

- `ConcreteTateDeckQuotient` (olean present): the algebraic quotient, Galois
  invariance and descent of the deck action.
- `TateDeckAction.tateDeckQuotientEquiv` (`:65`) and
  `tateDeckQuotientEquiv_mk` (`:82`); `tateParameterDeckSubgroup_algEquiv_map`
  (`TateUniformizationContract.lean:75`).
- `EllipticTorsion.galoisActionOnPoint` (`:73`), with
  `galoisActionOnPoint_one` (`:87`) and `galoisActionOnPoint_mul` (`:109`).
- `WeierstrassVariableChangePoints.weierstrassVariableChangePointEquiv`
  (`:299`), `..._apply` (`:306`), `..._mul` (`:377`), plus the affine
  `WeierstrassCurve.Affine.Point.map` / `map_some` API.

### 4.4 Source q and source-side comparison donors

- `SourceQv` (`SourceQvClosed.lean:50`) and the unconditional
  `exists_sourceQv_at_finitePlace_closed` (`:185`): for a split multiplicative
  curve at a finite place, a q with `q != 0`, `||q|| < 1`, canonical
  q-curve elliptic, and equal j-invariants (normalized completion).
- `SourceTateParameterAlignment.AlignedSourceTateParameter` (`:60`) and
  `exists_alignedSourceTateParameter` (`:102`): over
  `AlgebraicClosure (NormalizedCompletion v)`, a variable change with
  `C • E_local.map = Tate.map` (reverse direction) and the Delta/c4/c6
  normalizations; existence is unconditional from split reduction.
- `InitialThetaTateInput` (`TateInput.lean:11`), `InitialThetaTateComparison`
  (`TateComparisonBoundary.lean:23`), `SourceLocalTateBoundary`
  (`SourceLocalTateBoundary.lean:24`) are the consumer structures.

### 4.5 Theta (F4 / F8 track)

- `TateRigidTheta`: `positiveTerm`/`negativeTerm` summability,
  `thetaSeries`, `transportParameter`/`transportDomain`/`thetaTransport`,
  `thetaQExpansionCoefficient`, `tateThetaSeries_actual_summary`.
- `GaussianKernel.realThetaValue` (`:70`); `Example36SourceThetaDivisor`
  `thetaQUnit`, `thetaUnit`, `thetaUnit_eq_qUnit_pow`, `realThetaValue_pow_q`,
  `thetaUnit_transport`, `thetaRootValue`.
- `Foundations/Theta/OddThetaShift.oddTheta_shift` — the actual theta-function
  shift law (EtTh Prop 1.4(ii)); green olean.
- `Example36SourceThetaGenerator.analyticThetaTransport` (`:140`),
  `analyticDistinctThetaHistoryData` (`:234`), inhabited source-theta-history card.

## 5. Precise gaps

### G1 — point bijection (the analytic core)
No inhabitant of `TateUniformizationPointMapGap` (nor of the pair conditions)
exists. This is the classical Tate/sigma addition/coverage theorem; the tree has
no proof route, only the reduction to `tatePairCoordinatesSeparateOrbits` and
`tateCoordinatesCoverNonzeroPoints`. `SourcePointUniformization.CanonicalTatePointMapBijectionObligation`
(`:72`) is only an alias of the same gap, and the file is unimported.

### G2 — wrong coordinate normalization of the current point map
`TateWeierstrassPointData q` uses raw `tateWeierstrassX/Y`; by the module
erratum these do not lie on `weierstrassCurve K q` (they lie on the shifted
`tateNormalizationCurve q`). The canonical target is
`normalizedTateX/Y` plus the odd-coordinate identity
(`normalizedTate_equation_iff_oddSeries`), which is unproved. So the current gap
statement is conditional on possibly-unsatisfiable `hdata` and is **not** the
classical Tate point map. Any consumer-facing proof must re-base on normalized
coordinates; no `normalizedTateQuotientPoint` or normalized gap statement exists.

### G3 — group law
No natural parameter multiplication; `tatePointGroupLaw` is the transported
curve law along `hgap` (circular as a group-law construction and explicitly
disallowed as a substitute by SHEAF §7). No theta addition theorem; the exact
missing statement is §2.4. `tatePointBijection` is only an `Equiv`, not an
additive equivalence.

### G4 — Galois equivariance
`TatePointComparison.galois_naturality` is an unpopulated field. Donors supply
the action (`galoisActionOnPoint`), the quotient action
(`tateDeckQuotientEquiv`), and base-change equivariance on the image of a
continuous field homomorphism (`tateQuotientPoint_map_mk`). No theorem
intertwines a point equivalence on `AlgebraicClosure (Completion place)` with
`galoisActionOnPoint` over the whole `Kbar^x/q^Z`; no `pointEquiv` exists to
intertwine.

### G5 — carrier/completeness obstruction (independent of the classical theorem)
The consumer carrier is `AlgebraicClosure (Completion place)`. The project
gives it a spectral norm (`FinitePlaceSourceAlgebraicClosure.SourceAlgebraicClosure`
is `AlgebraicClosure (NormalizedCompletion place)`, with
`NontriviallyNormedField` `:57` and `IsUltrametricDist` `:65`), but the
same file states explicitly: "No completeness or properness of the algebraic
closure is assumed: finite subfields will supply the required complete carriers"
(`:8–12`). Every summability lemma for `coordinateSeries`, `yCoordinateSeries`,
`thetaSeries` requires `[CompleteSpace K]`; there is no `CompleteSpace`
instance at `AlgebraicClosure (Completion place)` and no finite-level/density
argument. Consequently the analytic point map cannot currently be instantiated at
the consumer carrier, even granting the classical theorem. This is a genuine
carrier-level gap in addition to G1.

### G6 — curve-side coordinate change over the completion
`HasTateCoordinateChange` / `CurveIndexedTateUniformization.realizesCurve` has
no inhabitant. `exists_alignedSourceTateParameter` gives a variable change only
over `AlgebraicClosure (NormalizedCompletion v)`, in the reverse direction
(`C • E_local.map = Tate.map`; moving to the contract direction is formal from the
`Group`/`MulAction` instances on `VariableChange`, but no such step or its typing
is recorded here), and **not** over the completion. Descent
from `Kbar` to `Completion place` is not proved; j-equality alone does not give
a variable change over the completion (quadratic twists). The inverse-j q over
Q_5 exists only at the q-series level
(`exists_canonicalQSeriesJ_eq_split_j_full`) and is not packaged as a
`FinitePlaceQCandidate`; the naive q = 5 is excluded
(`five_not_qSeriesInverseJParameter`).

### G7 — theta transform / theta section
Series-level `thetaSeries` transport under q |-> q^2 is not stated;
`thetaTransport` has no theorem and no consumer. The actual theta-function
transform law in the tree is `oddTheta_shift` (F4), a different theta object.
The source theta line-bundle section / identification with `thetaSeries` is F4/F8
scope, not supplied here. The source-side q |-> q^2 transport that is actually
consumed by `SourceDistinctThetaHistoryCard` is
`Example36SourceThetaGenerator.analyticThetaTransport`, not
`TateRigidTheta.thetaTransport`. T5 is therefore offline/duplicative for F7.

### G8 — source Theta-link / line bundle
Out of F7: recorded in L1-F4/F8 (`Example36TateUniformization` audit obligation
:415–488 and `curveIndexedTateUniformization` :146–158). Not needed for the D4
consumer's curve/point fields; must not be silently added to F7.

### G9 — carrier nonemptiness
`TatePointLocal.coordinateParameterDomain_nonempty` (`:93`) has **no consumer**;
there is no lemma recording `Nonempty (TateParameterQuotient q hq0)`
(the `some` part of the completion); `Nonempty (TatePointCompletion q hq0)` itself
is tautological via `none`. This is a pure packaging gap and
the natural consumer of the entire `TatePointLocal` file.

### G10 — consumer wiring and inhabitants
`InitialThetaTateComparison` and `SourceLocalTateBoundary` (Project) have no
inhabitants; `BadPlaceTateUniformizationCards` and
`BadPlaceUniformizationContract` (D4 branch) have no inhabitants and the D4
branch is not imported by `Project.lean`. `TateInverseJUniformization` and
`SourcePointUniformization` are unimported statement fragments. No production
proof currently consumes `TateGroupLaw` or `TatePointLocal` declarations.

## 6. Smallest next statement (recommended F7a)

**F7a — re-state the point map on the canonical normalized coordinates.**

This is the smallest statement that removes a real defect (G2) and is provable
from green donors without any hard analytic input. Target a new tmp stage-2 file
(not production), e.g. `tmp/sheaf/l1-f7/NormalizedPointMap.lean`:

```lean
import LeanFormal.IUT.Foundations.Geometry.TateCoordinateNormalization
import LeanFormal.IUT.Foundations.Geometry.TateUniformizationPointMap

namespace LeanFormal.IUT.TateCurve

variable {K : Type*} [NormedField K] [CharZero K] (q : K) (hq0 : q ≠ 0)

/-- Canonical normalized-coordinate point data: the normalized pair is
nonsingular on the canonical q-curve for every legal parameter. -/
def TateNormalizedPointData : Prop :=
  ∀ u : ↥(coordinateParameterDomain q),
    (weierstrassCurve K q).toAffine.Nonsingular
      (normalizedTateX q (u : K)) (normalizedTateY q (u : K))

/-- The canonical point map on the quotient of K^x by q^Z. -/
noncomputable def normalizedTateQuotientPoint
    (hdata : TateNormalizedPointData (K := K) q) :
    TateParameterQuotient q hq0 → (weierstrassCurve K q).toAffine.Point :=
  Quotient.lift
    (fun u => WeierstrassCurve.Affine.Point.some
      (normalizedTateX q (u : K)) (normalizedTateY q (u : K)) (hdata u))
    (by
      intro u v huv
      obtain ⟨m, hm⟩ := huv
      rw [WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨by rw [← hm, normalizedTateX_zpow_mul_parameter hq0],
             by rw [← hm, normalizedTateY_zpow_mul_parameter hq0]⟩)

/-- Exact remaining canonical point-map gap. -/
def TateUniformizationNormalizedPointMapGap
    (hdata : TateNormalizedPointData (K := K) q) : Prop :=
  Function.Injective (normalizedTateQuotientPoint q hq0 hdata) ∧
    ∀ P : (weierstrassCurve K q).toAffine.Point, P ≠ 0 →
      ∃ w : TateParameterQuotient q hq0,
        normalizedTateQuotientPoint q hq0 hdata w = P
```

Proof route (all green): the well-definedness proof is exactly the pattern of
`tateQuotientPoint` (`TateUniformizationPointMap.lean:191–207`) with
`normalizedTateX/Y_zpow_mul_parameter` (`TateCoordinateNormalization.lean:48,53`)
in place of `tateWeierstrassX/Y_zpow_mul_parameter`; `WeierstrassCurve.Affine.Point.some.injEq`
is the same. No `sorry` is needed for the definition; the gap Prop is a
definition, not a proof obligation. The analytic part is the `hdata`
construction, which is exactly the unproved odd-coordinate identity:
`inversionOddYCoordinateSeries q u ^ 2 = 4 * normalizedTateX q u ^ 3 + ...`
(the right-hand side of `normalizedTate_equation_iff_oddSeries`). That identity
must be registered as a separate named node, not hidden in `hdata`.

Acceptance boundary for F7a: `statement_compiles` only (no analytic
`sorry` required in the definition); no `proof_body_checked` or
`kernel_closed` claim.

Why this before the algebraic group-law work: it fixes the object that all later
point/group/Galois statements must use. The current raw-coordinate gap is not the
classical target; building on it would propagate G2 to every consumer.

## 7. Child nodes / suggested order

1. **F7a** (recommended first): normalized-coordinate point map + normalized gap
   statement, tmp stage 2; proof-free definitions, `statement_compiles`.
2. **F7b** (provable, pure algebra): identify the consumer deck quotient with the
   point-map carrier,
   ```lean
   noncomputable def unitsQuotientEquivOption {K : Type*} [Field K]
       (q : K) (hq : q ≠ 0) :
       (Kˣ ⧸ Subgroup.zpowers (Units.mk0 q hq)) ≃
         Option (TateParameterQuotient q hq)
   ```
   Route: the pole-excluded domain is exactly `K^x minus q^Z`
   (`coordinatePoleExclusion q u ↔ ∃ n, q^n u = 1`);
   `coordinateParameterDomain_zpow_mul_parameter` gives well-definedness; the
   `none` fiber is the class of 1; the `some` fiber is the orbit relation
   `tateParameterOrbitRel`. This is the exact domain of T1/T2.
3. **F7c** (stage 2, named `sorry`): the natural addition theorem of §2.4
   (`tateUniformization_add`), stated against F7a/F7b; no proof exists.
4. **F7d** (stage 2/3): Galois equivariance of the point equivalence. State it
   first over a `NormedField`+`CompleteSpace` carrier where the point map is
   meaningful; the algebraic-closure consumer version is blocked by G5. The
   base-change donor `tateQuotientPoint_map_mk` is the only green input.
5. **F7e** (blocked): the analytic odd-coordinate identity, the bijection G1, the
   coordinate-change descent G6, and the completed-carrier bridge G5. These are
   the parent-blocking gaps; none is a statement-only task.
6. **F7f** (independent packaging): package the inverse-j q of
   `Example36TateInverseJCanonical` as a `FinitePlaceQCandidate` with j equal
   to the split curve (needs norm/valuation transport along
   `concreteFivePadicEquiv`); feeds the consumer's `parameter` field only.

## 8. Status boundary

- `statement_compiles`: **not run** for F7a/F7b (no Lean file written in this package).
- `proof_body_checked`: **no** new declaration.
- `kernel_closed`: **no**; no current build/axiom probe was run. Prior oleans are not a kernel-closure audit.
- `target_accepted`: **no**; no comparator, no source-semantics review.
- production files changed: **none**.
- node-local stage: L1-F7 stage 1 delivered by this document; stage 2 = F7a/F7b;
  stage 3 open; parent remains **unclosed**.
