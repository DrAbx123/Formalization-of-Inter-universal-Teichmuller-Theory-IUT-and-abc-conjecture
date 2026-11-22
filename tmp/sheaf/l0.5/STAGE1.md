# L0.5 Stage 1 — source Theta-link: exact objects, consumers, donors, precise gaps

- package: `L0.5` (Layer 0 row of `coord/LAYER1-PLAN.md`)
- node: `l05-source-theta-link` (not yet a JSON DAG node; this record is its stage-1 material)
- stage: **1 — open (this record)**; stage 2 not started; stage 3 not started
- production edits: **none**; this file is the only artifact of the package
- date: 2026-10-22 (Asia/Shanghai); all SHAs are SHA-256 of the versions actually read in this stage
- rule applied: SHEAF §7 — fix AΘ / divisor-units / Mq→MΘ / root-deck / tempered synchronization from the paper
  first; do **not** fill a `ThetaLink` card and push upward
- status: `statement_compiles` n/a (no Lean declaration written), `proof_body_checked` no,
  `kernel_closed` no, `target_accepted` no

Inputs read: `logs/coordination/n8-theta-link-handoff-20261020.md`;
`tmp/n8-20261018/general/ActualSourceThetaLink.lean`;
`LeanFormal/IUT/IUTII/Theta/ThetaLinkAssembly.lean`;
`LeanFormal/IUT/IUTII/Frobenioid/Example36SourceThetaDivisor.lean`;
`LeanFormal/IUT/IUTII/Theta/ThetaLinkSourceCover.lean`;
`LeanFormal/IUT/Foundations/AlgebraicGeometry/SourceQlTheta*.lean`;
`Iut/Foundations/SourceTemperedCoveringCategory.lean`; `Iut/Foundations/SourceTemperedDeckGroup.lean`;
`Iut/Foundations/Frobenioid.lean`;
`LeanFormal/IUT/IUTII/Frobenioid/Example36SourceEtaleThetaTheory.lean`;
paper anchors IUT I Example 3.2 (i)–(vi), IUT II Example 3.2 / Proposition 3.3 / Remark 2.5.1, EtTh Proposition 1.4;
stage-1 records `tmp/sheaf/l1-f4/STAGE1.md`, `tmp/sheaf/l1-f8/STAGE1-source-binding.md`,
`tmp/sheaf/l1-f8/STAGE1-theta-link-source-cover-slice.md`.

## 0. Verdict

L0.5 **cannot** enter stage 2 yet. None of the five paper objects is instantiated at the source, and one of them (the geometric divisor/unit) has no Lean shadow at all:

| paper object | Lean shadow that exists | instantiated at the source? |
|---|---|---|
| AΘ = Yddot_v × A over the actual X_v | `ThetaProductData.product` + `ThetaCoverSubcategory` (formal product cones, conditional) | **no** — no diagram/Yddot/data for any actual curve |
| Θ_v unit + geometric theta divisor | none; only `SourceThetaDivisor := InfinitePlace F → ℤ` (a different object) and real-valued analytic theta | **no** |
| Mq(A) → MΘ(AΘ) | `ThetaLinkAssembly.thetaLink` (abstract comm-group monoids) | **no** — `Mq`/`MΘ` do not exist as Lean definitions |
| μ_2l / l·Z / deck ambiguity | `CarriesRootSubgroup` (an abstract hypothesis) and real-valued `thetaRootValue` | **no** — no μ_2l group, no l·Z action |
| tempered Π_v synchronization | `thetaLink_synchronized_evaluation` (a J-indexed family with one unit equivalence) | **no** — no Π_v, no conjugate family, no cyclotomic rigidity |

Three further facts decide scheduling:

1. The only files stating an actual source-level theta truth are outside Project or outside production:
   `tmp/n8-20261018/general/ActualSourceThetaLink.lean` (tmp, no olean) and
   `LeanFormal/IUT/IUTII/Theta/ThetaLinkSourceCover.lean` (production, **no olean**, last recorded build red).
2. The card-level Θ model in the tree is **provably degenerate**: `HodgeTheaterLink` forces equal
   `thetaPacket.q`, so `no_link_to_different_theta_q` / `actual_link_cannot_shift_theta_q`
   (`Example36SourceEtaleThetaTheory.lean:253,263`) prove that the paper's q ↦ q′ Θ-link cannot be expressed by
   that relation. L0.5 must **not** use `HodgeTheaterLink` as its link.
3. There are at least ten **name collisions** (§5) where the existing declaration means something else than the
   paper object. Substituting one would create a false completion.

## 1. What the paper fixes (objects, quantifiers, anchors)

### 1.1 Quantifier

IUT I Definition 3.1 gives once and for all an elliptic curve E_F over a number field F, a prime l ≥ 5, and bad
nonarchimedean valuations V_bad. Every L0.5 object is attached to such data and to one v ∈ V_bad:

    ∀ (initial Θ-data: E_F/F, l ≥ 5, V_bad), ∀ v ∈ V_bad,
      X_v, K_v, D_v, D_v^⊢, Yddot_v, Θ_v, AΘ = Yddot_v × A, F_v^⊢ ≌ F_v^Θ, μ_2l / l·Z, Π_v, ...

Lean-side candidate carrier: `S : SourceDefinition31Data.{u} l` (`SourceDefinition31Boundary.lean:660`) with
`S.badPlaces` and a place selection (`S.reduction.partition : SourcePlacePartition S.selectedPlaces S.badPlaces`,
`SourcePlaceSelection.V_mod_bad`). Two parts of the original hypothesis must not be dropped: l stays arbitrary
(not l = 5), and l is coprime to the bad residue characteristic p_v
(`BadPlaceQParameterCards.badResidueCharacteristic_primeToL`, `SourcePlacePartitionReduction.lean:800`;
handoff lines 103–136, including the 2026-10-21 correction at line 134).

### 1.2 AΘ (the source theta cover object)

IUT I Example 3.2(v), text lines 3762–3810:

- D_v^Θ ⊆ (D_v)_Yddot_v is the **full subcategory determined by the products in D_v of Yddot_v with objects of
  D_v^⊢**;
- "forming the product with Yddot_v" is a **natural equivalence** D_v^⊢ → D_v^Θ, written A ↦ AΘ := Yddot_v × A;
- for AΘ ∈ Ob(D_v^Θ), AΘ ↦ O^×(T_AΘ) · (Θ_v^N |_T_AΘ) ⊆ O^×(T^÷_AΘ) defines a monoid on D_v^Θ.

This is a theorem about the actual curve, not a definition to assume: the equivalence and the monoid compatibility
are what stage 2 would state.

### 1.3 Θ_v and the theta divisor

IUT I Example 3.2(ii), lines 3665–3694: Θ_v ∈ O^×(T^÷_Yddot_v) is the reciprocal of the Frobenioid-theoretic l-th
root of the theta function, normalized to attain value 1 at √−1, and is **completely determined up to
μ_2l(T^÷_Yddot_v) and the action of l·Z ⊆ Aut(T_Yddot_v)**.

EtTh Proposition 1.4, text lines 1338–1400:

- (i) zeros of Θ̃ on Yddot are precisely the cusps, each of multiplicity one; pole divisor precisely D_1;
- (ii) Θ̃(q_X^{a/2} U) = (−1)^a q_X^{−a²/2} U^{−2a} Θ̃(U);
- (iii) O^×_K̃·η̃_Θ ∈ H¹(Π^tp_Yddot, Δ^Θ) are exactly the Kummer classes of O^×_K̃-multiples of Θ̃, and their
  restrictions at y equal O^×_K̃·Θ̃(y).

So "divisor" means a geometric divisor on the actual Yddot plus a Kummer class, not a q-series coefficient comparison
(handoff line 18).

### 1.4 Mq(A) → MΘ(AΘ)

IUT I Example 3.2(iv)–(v), lines 3701–3877. With Φ_{C_v^⊢} = N·log_Φ(q_v)|_{D_v^⊢}:

    O^⊷_{C_v^⊢}(A)  = O^×(T_A)    · (q_v^N |_T_A)
    O^⊷_{C_v^Θ}(AΘ) = O^×(T_AΘ) · (Θ_v^N |_T_AΘ)

and natural isomorphisms O^⊷_{C_v^⊢}(−) ≅ O^⊷_{C_v^Θ}(−), O^×_{C_v^⊢}(−) ≅ O^×_{C_v^Θ}(−), compatible with
q_v|_T_A ↦ Θ_v|_T_AΘ and O^×(T_A) ≅ O^×(T_AΘ) (the unit isomorphism induced by AΘ = Yddot_v × A → A). The result is
a natural equivalence of **split Frobenioids** F_v^⊢ ≌ F_v^Θ mapping τ_v^⊢ ↦ τ_v^Θ (lines 3862–3877), the splittings
being μ_2l(−)-orbits.

The root-level form used by the handoff (lines 19, 55) is the evaluation form of IUT II, Introduction lines 97–104 and
Remark 2.5.1(i) lines 4272–4288: for a chosen 2l-th root q̲_v of q_v, theta values at l-torsion points are, up to a
2l-th root of unity, q̲_v^{j²}; Remark 2.5.1(iii) adds that the μ_2l-indeterminacies for different j are
**independent**, i.e. not one global root choice.

### 1.5 μ_2l, l·Z, tempered synchronization

- ambiguity of Θ_v: μ_2l(T^÷_Yddot_v) and l·Z ⊆ Aut(T_Yddot_v) (IUT I 3674–3694);
- μ_2l-orbit of q̲_v^{j²} (IUT II Remark 2.5.1(i)); independence across j (iii);
- conjugate synchronization: IUT II Example 3.2(i) lines 5458–5568 constructs
  Π_v ↷ ΨF^Θ_v = {ΨF^Θ_{v,α}}_{α∈Π_v}, ∞ΨF^Θ_v, with splittings up to torsion compatible with Π_v;
  Proposition 3.3 lines 5595–5680 identifies Ψ^†F^Θ_v ≅ Ψ^env(MΘ_*) and Ψ^†C_v ≅ Ψ^cns(MΘ_*);
  Proposition 3.4 lines 5683+ states multiradiality under full poly-isomorphisms of MΘ_* projective systems.
  These are the paper's synchronization data; they are not a single chosen root.

## 2. Exact Lean objects that exist (donors)

### 2.1 Tempered source category

`Iut/Foundations/SourceTemperedCoveringCategory.lean` (1369 lines, SHA256
`C8B0E25F43FC76B91F57F32F9092EEA68088218AA5B39AF7451831ED4B19E8F6`):

- `Iut.SourceSemiGraphOfAnabelioids.{u}` with `diagram.base.Vertex`, `diagram.CovObject`, `diagram.GluedObject`;
- `IsTempered (root) (target : diagram.CovObject) : Prop` =
  `∀ basePoint, ∃ splitter, IsComponentSplitBy diagram root splitter target basePoint` (corrected Semi-graphs
  Def 3.5(ii));
- `temperedObjectProperty`, `TemperedCover (root) := (temperedObjectProperty root).FullSubcategory`,
  `temperedCovInclusion`.

Closest Lean carrier of D_v = B^temp(X_v)^0, but **no X_v** is attached to it.

### 2.2 The categorical model of D_v^⊢ ≌ D_v^Θ

`LeanFormal/IUT/IUTII/Theta/ThetaLinkSourceCover.lean` — **red / moving target**:

- version read here: 475 lines, SHA256 `5EF335F442E3FC4A638A2BE15EB42A2D9AF79F215FB4E0E172E26698F01E35B4`;
- the file was rewritten 2026-10-22 07:34:00 (after `CHILD-theta-source-cover-dependency.md` 07:29:42) and again
  before this record finished (later SHA256 `D6323D253A97B64D343D4A277476A0849F401CC46FAEDDBCC2CFA8131A1FE4EB`);
- **no `.olean` exists** and **no file imports it**;
- last recorded build: `lake build LeanFormal.IUT.IUTII.Theta.ThetaLinkSourceCover` exit 1 with three errors
  (`:295` unsolved goals in `productMap_comp`; `:413` rewrite failure in `sliceObjectIsoIdentityOfIsIsoHom`;
  `:407` needs `noncomputable`), per the child record. Its owner under `coord/STATE.md` is the production owner
  (`iplsheapt`); it is not free for this package to edit or to rely on as green.

Exact declarations (types verbatim, bodies elided):

    abbrev ConnectedTemperedCover (diagram) (root) :=
      (connectedTemperedObjectProperty diagram root).FullSubcategory
    structure BaseFieldCoverModel (diagram) (root) where
      IsBaseFieldCover : ConnectedTemperedCover diagram root → Prop
      baseObject : ConnectedTemperedCover diagram root
      baseObject_mem : IsBaseFieldCover baseObject
    abbrev BaseCover (model) := ObjectProperty.FullSubcategory model.IsBaseFieldCover
    abbrev YddotSlice (diagram) (root) (Yddot) := Over Yddot
    structure ThetaProductData (diagram) (root) (Yddot) (model) where
      product : BaseCover model → ConnectedTemperedCover diagram root
      fst : ∀ A, product A ⟶ Yddot
      snd : ∀ A, product A ⟶ A.obj
      lift : ∀ {A} {X}, (X ⟶ Yddot) → (X ⟶ A.obj) → (X ⟶ product A)
      lift_fst / lift_snd / lift_unique / snd_epi : ...
    def productFunctor (data) : BaseCover model ⥤ YddotSlice diagram root Yddot
    instance productFunctorFaithful (data) : (productFunctor data).Faithful
    def SliceFactorization (data) : Prop :=
      ∀ ⦃A B⦄ (h : Over.mk (data.fst A) ⟶ Over.mk (data.fst B)),
        ∃ f : A ⟶ B, h = Over.homMk (data.productMap f) (data.productMap_fst f)
    theorem productFunctor_full (data) (factorization : SliceFactorization data) : (productFunctor data).Full
    abbrev ThetaCoverSubcategory (data) := (productFunctor data).EssImageSubcategory
    noncomputable def thetaEquivalence (data) (factorization : SliceFactorization data) :
        BaseCover model ≌ ThetaCoverSubcategory data
    structure BaseFieldProductIdentification (data) where
      baseProductIso : Over.mk (data.fst (baseCoverObject model)) ≅ Over.mk (𝟙 Yddot)

Reading: the **conditional categorical skeleton** of Example 3.2(v). `product` is an abstract function, `snd_epi` is
a field, `SliceFactorization` is a hypothesis, and the file itself states it does not identify X_v, Yddot_v, B(K_v)^0
or the paper's D_v. It is a donor for the **shape** of AΘ, not a construction of AΘ.

### 2.3 The abstract monoid link

`LeanFormal/IUT/IUTII/Theta/ThetaLinkAssembly.lean` (258 lines, SHA256
`FB8ED077CF794BBE6CE6CAFCB77686A5BE5273C656BD6C743215243B4CFA5463`; olean 2026-10-20 02:13; imported only by
`LeanFormal/IUT/Project.lean:554`):

    variable {U V G H : Type*} [Group U] [Group V] [CommGroup G] [CommGroup H]
    variable (u : U →* G) (v : V →* H) (q : G) (theta : H)
    variable (degreeG : G →* Multiplicative ℤ) (degreeH : H →* Multiplicative ℤ)
    variable (hu : Function.Injective u) (hv : Function.Injective v)
    variable (hunitG : ∀ a, degreeG (u a) = 1) (hunitH : ∀ b, degreeH (v b) = 1)
    variable (hq : (degreeG q).toAdd ≠ 0) (htheta : (degreeH theta).toAdd ≠ 0)
    noncomputable def thetaLink (e : U ≃* V) :
        unitGeneratedSubmonoid u q ≃* unitGeneratedSubmonoid v theta

plus `thetaLink_unitPower`, `thetaLink_embeddedUnit`, `thetaLink_generator`, `thetaLinkSymm`,
`thetaLink_source_representation`, `thetaLink_target_representation`, `thetaLink_unique`,
`thetaLink_unitEquiv_ext`, and the orbit layer `sourceEvaluationOrbit`, `targetEvaluationOrbit`,
`sourceSquaredLabelOrbit`, `targetSquaredLabelOrbit`, `CarriesRootSubgroup (e) (mu) (nu) : Prop`,
`thetaLink_image_sourceEvaluationOrbit`, `thetaLink_image_sourceSquaredLabelOrbit`,
`thetaLink_synchronized_evaluation`, `thetaLink_natural`. Underlying general theorem:
`LeanFormal/IUT/IUTII/Theta/UnitGeneratedMonoidComparison.lean` (291 lines, SHA256
`2ACA26F6076D13F2564745709BA7E7B7848714B9AF952B0BE7F2A55AAA63EA76`; olean 2026-10-20 01:15).

Reading: the **algebra** of the link, parameterized by arbitrary groups. Its header says it "does not instantiate
source local fields, integral Frobenioid units, divisor degrees, or an IUT Theta-link".

### 2.4 The only actual source-level odd-theta object (tmp, not built)

`tmp/n8-20261018/general/ActualSourceThetaLink.lean` (115 lines, SHA256
`559EEB574AABDE55B16D8609F3EA63CCFB29584CF43F54F1953DEDFFA4AA0CE5`; namespace
`LeanFormal.IUT.ActualSourceThetaLink`; **no olean anywhere**, not imported by Project; imports `SourceQvClosed`,
`OddThetaNormalization`, `PuncturedEllipticCurve`):

    abbrev SourceLocalField (v : NumberField.FinitePlace K) : Type u := NormalizedCompletion v
    variable (v : NumberField.FinitePlace K) (X : PuncturedEllipticCurve K)
      (hsplit : X.HasSplitMultiplicativeReductionAt v)
    noncomputable def sourceQv :
        SourceQv (K := SourceLocalField v) (X.baseChange (SourceLocalField v)).curve
          (X.baseChange (SourceLocalField v)).isElliptic :=
      Classical.choice (exists_sourceQv_at_finitePlace_closed v X hsplit)
    noncomputable def sourceQ : SourceLocalField v := (sourceQv v X hsplit).q
    structure SourceThetaRootData (l : ℕ) where
      qbar : SourceLocalField v
      i : SourceLocalField v
      qbar_pow : qbar ^ (2 * l) = sourceQ v X hsplit
      i_sq : i ^ 2 = -1
      two_large : ‖sourceQ v X hsplit‖ < ‖(2 : SourceLocalField v)‖
    theorem sourceOddTheta_normalized (l : ℕ) (D : SourceThetaRootData v X hsplit l) (j : ℤ) :
        oddTheta (sourceQ v X hsplit) (D.i * (D.qbar ^ l) ^ j) /
            oddTheta (sourceQ v X hsplit) D.i =
          (D.qbar ^ l) ^ (-(j ^ 2))

and the file ends with the explicit residual: **not constructed** are an actual ATheta, its integral units, the theta
divisor on the actual source cover, and the finite-layer Kummer evaluation square. The exponent is −(j²) on qbar^l
(not +j² on qbar) — see G10. `SourceQv` itself is `SourceQvClosed.SourceQv`
(`{q, q_ne_zero, q_norm_lt_one, canonical_is_elliptic, j_eq}`), produced by
`exists_sourceQv_at_finitePlace_closed` (`SourceQvClosed.lean:185`, 216 lines, SHA256
`7215A0DA7B788BD7037DF21E4EDFFF515DB2125B24D6E9FABD8147B48240AB26`; olean 2026-10-20 08:09) from
`hsplit : X.HasSplitMultiplicativeReductionAt v`. It is a `Classical.choice` of an existence statement, with no link
to the Definition 3.1 contract's q (gap G9).

### 2.5 F4 analytic theta (L1-F4 owner file)

`LeanFormal/IUT/IUTII/Frobenioid/Example36SourceThetaDivisor.lean` (809 lines, SHA256
`3D49106992D4BCFBC630179F0F8552652AF586631E9143E83D5AA422AEA17BA8` — **same SHA as in `coord/STATE.md` and
`tmp/sheaf/l1-f4/STAGE1.md`**; olean 2026-10-20 02:02; serialized wrapper build exit 0 with 8839 jobs; imported only
by `LeanFormal/IUT/Project.lean:551`).

What it provides for L0.5 (real analytic carrier `AnalyticThetaCarrier := {q : ℝ // 0 < q ∧ q < 1}`):

- `analyticThetaValue t = jacobiTheta (carrierThetaTau t)`, positive, nonzero, `= 1 + 2∑_{n≥0} q^((n+1)^2)`;
- `thetaUnit : ℝˣ`, `thetaUnit_eq_qUnit_pow`, `thetaRootValue (r : ℝ) (j : ℤ) = r^(j^2)` with
  `thetaRootValue_twoLth_root` and `thetaRootValue_mul_root_of_pow_eq_one` (μ_2l action **on real values**);
- `analyticThetaZeroSet = ∅`, `analyticThetaDivisor_trivial` (even theta q-series);
- `oddThetaOrderZeroPart = U − U⁻¹`, `oddThetaReduction_eq_zero_iff` (simple zeros at ±1),
  `oddThetaReduction_pole_at_zero` (simple pole at 0);
- `example36SourceThetaDivisor_summary` and `example36SourceThetaDivisor : Obligation` with status
  `VerificationStatus.testCarrier`.

What it explicitly does **not** provide (audit note lines 759–764): two-sided odd theta convergence, the shift
law/nonvanishing of EtTh Prop 1.4(ii), the meromorphic continuation and divisor of Prop 1.4(i), and the
Kummer-class/line-bundle statement of Prop 1.4(iii). It also warns: **the empty zero divisor of the even theta
q-series is not the source theta divisor.**

### 2.6 Arithmetic divisor / unit donors (global, infinite places)

`LeanFormal/IUT/Foundations/AlgebraicGeometry/InfinitePlacePsiCnsResidual.lean` (272 lines, SHA256
`D21435800FCBC26CD4289531B1658C70ECAEC34C39DE4EEAD58D3A7CD20D864A`):

    abbrev SourceIntegralUnits (S) : Type u := (NumberField.RingOfIntegers S.arithmetic.F)ˣ
    def sourceIntegralUnitLog (S) (w : InfinitePlace S.arithmetic.F) (u) : ℝ
    abbrev SourceThetaDivisor (S) : Type u := NumberField.InfinitePlace S.arithmetic.F → ℤ
    def sourceThetaDegree (S) (D) : ℤ := ∑ w, mult w * D w
    def sourceGlobalNormalization (S) (u) : Prop := ∑ w, mult w * log ... = 0
    def sourceGaloisInvariant (S) (D) : Prop := ∀ σ, ∀ w, D (w.comap σ) = D w
    structure SourcePsiCnsTerms (S) where ...      -- no inhabitant
    def InfinitePlacePsiCnsSourceResidual (S) : Prop := Nonempty (SourcePsiCnsTerms S)

This `SourceThetaDivisor` is **integer coefficients on the infinite places of F** (the archimedean part of the IUT III
Θ-divisor). It is *not* the geometric theta divisor on Yddot (G4, §5).

Other `SourceQlTheta*` files are source-only in this tree (none has a `.lake` olean except
`SourceQlThetaPunctureIdeal`; none is imported by Project except that one):

- `SourceQlThetaObjectActual.lean` (300 lines, SHA256 `56EE4551AFCA0BB4550E6C680292B90B3B560D2ED0A807C9C5B7964497B36E5D`):
  actual `S.arithmetic.curve`/puncture/base change, `SourceThetaDivisor`, `SourceIntegralUnits`, zero divisor with
  degree 0 and Galois invariance; and the **six-item residual enum** `SourceThetaObjectMissingDatum` =
  `arithmeticCurveLineBundle | thetaObjectATheta | geometricThetaDivisor | unitComparisonMqMTheta |
  muTwoLDeckRootAction | conjugateSynchronization` (`sourceThetaObjectMissingData_length = 6`).
- `SourceQlThetaLineBundleFromCurve.lean` (307 lines, SHA256 `FCF563210350A1C683286DD7B9DA876CBC0C468ACD27CDAD9A3AD70283D63CBA`):
  same boundary plus principal-degree formula; six-item enum `SourceThetaLineBundleMissingDatum`.
- `SourceQlThetaLineBundleObstruction.lean` (299 lines, SHA256 `8BF1C531AAEFA1625FE2965A803FF9304E47E22C0A2B64E91EC8080649D8D71B`):
  `sourceThetaFullRealDivisorType = (HeightOneSpectrum →₀ ℤ) × (InfinitePlace → ℝ)`, principal divisor degree
  zero by the product formula, six-item enum.
- `SourceQlThetaPunctureDivisor.lean` (251 lines, SHA256 `63E8CB09BFABE55B45C572E1489E043C8A9B3858DCBE339D5F9616E5E435E7DA`):
  formal divisor supported at the puncture, with support/coefficient/degree theorems.
- `SourceQlThetaDivisorDegreeActual.lean` (272 lines, SHA256 `094E0DB69CD9E31E8EB19ECD1D75DC56364077607F46EC6C7B393FD5299A0E34`).
- `SourceQlThetaDivisorPrincipalQuotient.lean` (279 lines, SHA256 `19FE5A4773E70AEB797F72C66E980ED8145510CD1398236A371D7BD7F6B192E8`)
  and `...Consumer.lean` (258 lines, SHA256 `BFD8E7421233F2B72121C14896ABFADA92D5A5725A49B87141990D052BB93DA4`):
  degree-zero and principal subgroups, `SourceThetaFullPrincipalQuotient`, projection/kernel/surjectivity; the
  consumer is imported by **nothing**.
- `SourceQlThetaPunctureIdeal.lean` (71 lines, SHA256 `F3F3E84F8570C05A04CAEE3466998BDF50360D908C36D84BE91CBE381AA51518`;
  olean 2026-10-21 09:09; imported by `Project.lean:180`): affine puncture vanishing ideal, **unit ideal at the point
  at infinity** — explicitly not a theta line bundle. `SourceQlThetaPunctureIdealProjective.lean` (313 lines, SHA256
  `79EBCA967D4680C316E3CE9AFCFCF0429BB6B13DE5E0FC1F359DD0B584282E5B`) is imported by nothing and isolates the
  missing Dedekind/invertibility inputs; the affine-infinity case is an **obstruction**, not the line bundle.
- `SourceQlThetaLinkBridge.lean` (130 lines, SHA256 `1C24BB87CE7C4FA9E80C520D753E85736F05729644370D74F1A450B256E287FB`;
  **no olean, no importer**): actual Q_l source field/log-shell/principal units/p-scaling, the isometric embedding
  `sourceQlToTargetRingHom`, and the commuting square `actualEmbeddingScalingSquare`. Its residual list
  `sourceThetaLinkResiduals : List String` has exactly 5 entries (AΘ + projection/base change; divisor and
  Mq -> M_Theta; mu_(2l)/l-Z deck/root; conjugate synchronization; object-level identification beyond the
  Q_l -> F_v scalar embedding).

### 2.7 Frobenioid apparatus and model-only presentations

- `Iut/Foundations/Frobenioid.lean` (1295 lines, SHA256 `B6B8F4E1F1712CA711CE62584D036DAA715E0B86A289F0599E03F7D8F80C2279`):
  `PreFrobenioid` with `divisorMonoid : DivisorialMonoidOn D IsFSM` and `divisor`, `FrobenioidAxioms` (Frobenioids I
  Def 1.3), `FrobenioidPresentation extends PreFrobenioidPresentation`. This is the right vocabulary for
  F_v^⊢ ≌ F_v^Θ and the only candidate source of a ℤ-valued divisor degree for the `thetaLink` parameters (G5).
- `LeanFormal/IUT/IUTII/Frobenioid/ConcreteSourceFrobenioidBridge.lean` (810 lines, SHA256
  `9434C08B2E25AA68399E30588673F4572E7937540BA00A2DD4AA9B9B8AC97BD0`): a `FrobenioidPresentation` for the
  **concrete Gaussian place above 5**, `concreteStageModel`. Model-only; not the arbitrary source v.

### 2.8 Residual enumerations and cards (registries, not objects)

- the three six-item enums above; `sourceThetaLinkResiduals` (5 strings);
- `SourceThetaGeneratorCard` (`Theta : Type`, `qExpansion : Theta → ℤ → ℝ`, `q : ℝ`, `q_eq_gaussian`,
  `specialValue : SignedLabel l.value → ℝ`) and `SourceDistinctThetaHistoryCard`
  (`Example36ThetaGeneratorFeasibility.lean:391,413`);
- `SourceCurveEtaleThetaIdentificationCard` (`Example36SourceThetaGenerator.lean:273`), **inhabited** by analytic
  q-expansion/evaluation data at q = 1/5, but carrying no theta function, line bundle or Theta-link (its own text
  says the remaining identification is task-120);
- `HodgeTheater` / `HodgeTheaterLink` / `FiniteThetaPacket` (`Iut/.../HodgeTheaterCore.lean:31,36`,
  `FiniteThetaPacket.lean:26`): `FiniteThetaPacket.q : ℝ`, `scale : SignedLabel → ℝ`; `HodgeTheaterLink` **forces
  theta_q_eq**.

None of these is a source object; the cards must not be used to define one.

## 3. Status table (versions read in this stage)

| file | lines | SHA256 (read) | olean | importer | status |
|---|---|---|---|---|---|
| `tmp/n8-20261018/general/ActualSourceThetaLink.lean` | 115 | `559EEB57…AA0CE5` | none | none | tmp-only, **no build evidence** |
| `.../IUTII/Theta/ThetaLinkAssembly.lean` | 258 | `FB8ED077…4CFA5463` | 10-20 02:13 | `Project.lean:554` | built at that version; abstract only |
| `.../IUTII/Theta/ThetaLinkSourceCover.lean` | 475 | `5EF335F4…01E35B4` → now `D6323D25…1A1FE4EB` | **none** | **none** | **red**, owner repairing (STATE), do not rely |
| `.../IUTII/Frobenioid/Example36SourceThetaDivisor.lean` | 809 | `3D491069…AEA17BA8` | 10-20 02:02 | `Project.lean:551` | build exit 0 (8839 jobs); no sorry |
| `.../AlgebraicGeometry/SourceQlThetaLinkBridge.lean` | 130 | `1C24BB87…E287FB` | none | none | audit text; never compiled |
| `.../AlgebraicGeometry/SourceQlThetaObjectActual.lean` | 300 | `56EE4551…7B36E5D` | none in `.lake` | — | production revision uncompiled; a tmp copy with a different SHA has an olean |
| `.../SourceQlThetaLineBundleFromCurve.lean` | 307 | `FCF56321…D63CBA` | none | — | source only |
| `.../SourceQlThetaLineBundleObstruction.lean` | 299 | `8BF1C531…9D8D71B` | none | — | source only |
| `.../SourceQlThetaPunctureDivisor.lean` | 251 | `63E8CB09…35E7DA` | none | — | source only |
| `.../SourceQlThetaPunctureIdeal.lean` | 71 | `F3F3E84F…A51518` | 10-21 09:09 | `Project.lean:180` | built; affine ideal only |
| `.../SourceQlThetaPunctureIdealProjective.lean` | 313 | `79EBCA96…4282E5B` | none | none | obstruction analysis |
| `.../SourceQlThetaDivisorPrincipalQuotient.lean` | 279 | `19FE5A47…B192E8` | none | — | source only |
| `.../SourceQlThetaDivisorPrincipalQuotientConsumer.lean` | 258 | `BFD8E742…BB93DA4` | none | none | source only |
| `Iut/Foundations/SourceTemperedCoveringCategory.lean` | 1369 | `C8B0E25F…4B19E8F6` | — | — | donor library |
| `Iut/Foundations/SourceTemperedDeckGroup.lean` | 772 | `A3EFD6D9…A002D0F1` | — | — | `TemperedDeckGroup` inverse limit (needs countable diagram) |
| `Iut/Foundations/Frobenioid.lean` | 1295 | `B6B8F4E1…80C2279` | — | — | abstract Frobenioid apparatus |
| `.../Example36SourceEtaleThetaTheory.lean` | 383 | (not hashed) | 10-20 03:34 | `Project.lean:552` | negative result: link relation is q-preserving |
| `tmp/sheaf/l1-f8/ThetaLinkSourceCoverConsumer.lean` | 45 | `458F4E42…F03B48D` | — | — | consumer statement; blocked by red donor |

## 4. Consumers: L1-F4 and L1-F8

### 4.1 L1-F8 — the geometric consumer (statement exists, blocked)

`tmp/sheaf/l1-f8/ThetaLinkSourceCoverConsumer.lean` (SHA256
`458F4E42621AD5AA3E9070BAC564E5DB652D599FDB7426568A91B225CD03B48D`):

    structure ThetaLinkSourceCoverConsumer where
      diagram : Iut.SourceSemiGraphOfAnabelioids.{u}
      root : diagram.base.Vertex
      Yddot : ConnectedTemperedCover diagram root
      model : BaseFieldCoverModel diagram root
      data : ThetaProductData diagram root Yddot model
      factorization : SliceFactorization data
    theorem thetaLinkSourceCoverConsumer_equivalence (consumer : ThetaLinkSourceCoverConsumer.{u}) :
        BaseCover consumer.model ≌ ThetaCoverSubcategory consumer.data

What L1-F8 needs **from L0.5** and does not have: actual `diagram`, `root`, `Yddot`, `model`, `data`, `factorization`
for the source curve X_v — the six fields are exactly the missing source objects. What L1-F8 supplies **to L0.5**:
the categorical equivalence D_v^⊢ ≌ D_v^Θ *conditional on those fields*, i.e. the shape in which AΘ must be produced.
Its child `F8aSourceDiagram.lean` (SHA256 `FA5C9FA77A9FA46368650DD279E0950BAF931D3AD3C3A61BA94ABBB94FEA5167`, 63
lines) already declares `sourceDiagram`, `sourceRoot`, `sourceDiagramOfSignQuotient` with named `sorry`; L0.5 must
**consume that node, not redeclare it**.

Consumer status: `statement_compiles` = **no** (import olean missing because the donor is red); `proof_body_checked` =
no; the statement is a generic categorical wrapper, not a real-source binding.

### 4.2 L1-F4 — the analytic/divisor consumer (no theorem-level consumer; gap owner)

`Example36SourceThetaDivisor.lean` has no consumer except `Project.lean:551` (its `Obligation` record). What L1-F4
supplies **to L0.5**: the analytic odd-theta order-zero reduction (`oddThetaOrderZeroPart`, zeros at ±1, pole at 0)
and the real-valued `thetaUnit`/`thetaRootValue` μ_2l multiplication rule; its remaining gaps (c) meromorphic
continuation/divisor and (d) Kummer class/line bundle **are** L0.5 objects. What L0.5 supplies **to L1-F4**: the
geometric Yddot/AΘ carrier on which the analytic theta becomes a section, the divisor with zeros at cusps and pole
D_1, and the Kummer class, so that F4's `testCarrier` status can be upgraded to a source statement. Note F4 is *not*
the source-relevant odd theta: the nonarchimedean odd theta lives in `ActualSourceThetaLink.lean` (via
`Foundations/Theta/OddTheta*.lean`), while F4's q-series is real-analytic at q ∈ (0,1) ⊂ ℝ and must not be
substituted for the value-group theta.

### 4.3 Edge status

- `L1-F4 → L0.5`: **planned** (paper-level analytic theta leg); no Lean import edge (`Example36SourceThetaDivisor` is
  imported by Project only).
- `L1-F8 → L0.5`: **planned**; no Lean import edge; the F8 consumer does not import L0.5 and L0.5 has no file.
- `L0.5 → L1 Theta/源 Theta 识别` (the downstream row of `coord/LAYER1-PLAN.md`): **planned, no consumer file**.

No `observed_source` edge exists between any of these three; the consumer edges are `planned`, not `verified_lean`.

## 5. Name collisions — do not substitute

| name in tree | what it actually is | paper object it is *not* |
|---|---|---|
| `SourceDefinition31Data.reduction.qParameter : Bad → ℝ` (`SourceDefinition31Boundary.lean:94`) | real-valued contract field with `‖q‖<1`, `q≠1` | `q_v ∈ O^⊷(T_X_v) ≅ O^⊷_K_v` (a local-field element) |
| `SourceQv.q : NormalizedCompletion v` (via `exists_sourceQv_at_finitePlace_closed`) | `Classical.choice` of an existence theorem for supplied `X`, `v` | the contract's q; no equality is proved (G9) |
| `AnalyticThetaCarrier.q : ℝ` (`Example36SourceThetaGenerator.lean:89`) | real analytic parameter, e.g. 1/5 | the nonarchimedean q_v |
| `FiniteThetaPacket.q : ℝ`, `scale : SignedLabel → ℝ` | finite real packet used by `HodgeTheater` | Θ_v as a unit in O^×(T^÷) |
| `SourceThetaDivisor S := InfinitePlace F → ℤ` | archimedean divisor (IUT III Θ-divisor / Ψ^cns data) | EtTh's geometric theta divisor (cusps / D_1) |
| `SourceIntegralUnits S := (𝓞_F)ˣ` | global units with product-formula log | O^×(T_A) (units of the Frobenioid at A) |
| `thetaUnit : ℝˣ`, `thetaRootValue : ℝ → ℤ → ℝ` (F4) | real-valued theta units and roots | value-group units with μ_2l action |
| `ThetaProductData.product : BaseCover → ConnectedTemperedCover` | abstract product-cone function supplied by the caller | Yddot_v × A in D_v |
| `SourceCurveEtaleThetaIdentificationCard` | inhabited card of analytic q-expansion/evaluation at 1/5 | the source etale theta function/line bundle/Theta-link |
| `SourceThetaLinkChain` (`SourceThetaLinkDisplacementReduction.lean:138`) | ℤ-indexed `HodgeTheater` chain along `HodgeTheaterLink` | the source Θ-link (its link relation is q-preserving, §0) |

## 6. Precise gaps

Each gap lists what must exist (paper content), why current fields cannot produce it, the donor to reuse, the child
node to register, and the acceptance condition. **No gap may be closed by a structure field, a Card, `Nonempty`, an
arbitrary `Type`, a `sorry`-inhabited data field, or a weaker quantifier.**

### G1 — sourceDiagram / sourceRoot (owned by L1-F8a; prerequisite, do not duplicate)

- Paper: D_v = B^temp(X_v)^0; the semi-graph of anabelioids of X_v.
- Lean now: `SourceSemiGraphOfAnabelioids` exists; `sourceDiagram`/`sourceRoot` exist **only as named `sorry`** in
  `tmp/sheaf/l1-f8/F8aSourceDiagram.lean`; no production declaration, no construction.
- Why not derivable: no declaration connects `HyperbolicOrbicurve` with `SourceSemiGraphOfAnabelioids` anywhere in the
  tree (a repo-wide search returns no co-occurrence; only `Iut/Foundations/Orbicurve.lean` mentions
  `HyperbolicOrbicurve`). In particular nothing produces a diagram from `SourceCompletionSignQuotient.xF`.
- Donor: `SourceCompletionSignQuotient.xF` built by `toSourceCompletionSignQuotient`
  (`SourceSignQuotientConstruction.lean:74`), the actual source orbicurve.
- Child: `L1-F8a` (exists). Acceptance: `statement_compiles` and a real construction (or a documented obstruction).

### G2 — Yddot, base-field model, product data, SliceFactorization (L1-F8b–e)

- Paper: D_v^⊢ = B(K_v)^0 ⊆ D_v; Yddot_v with base field K_v; products Yddot_v × A; the base-field condition making
  A ↦ Yddot_v × A full.
- Lean now: `BaseFieldCoverModel`, `ThetaProductData`, `SliceFactorization` are **caller-supplied** parameters; their
  fields (`product`, `snd_epi`, the factorization) have no construction. `ConnectedTemperedCover` has **no binary
  products** (deliberately: the product of connected covers is disconnected), so `product` must be built from the
  actual D_v product, not from a global instance.
- Why not derivable: the product in D_v is the fiber product of covers of X_v. The donor file states that no
  `HasBinaryProducts` instance for `TemperedCover`/`ConnectedTemperedCover` exists and that such an instance would be
  mathematically wrong, so the product cannot come from the category API; `snd_epi` (geometric-point surjectivity) is
  a supplied field, not derived.
- Child: `L1-F8b`–`L1-F8e` (registered). Acceptance: each construction, then `productFunctor_full`/`thetaEquivalence`
  instantiated with **no SliceFactorization hypothesis left**.

### G3 — the AΘ object and its Θ_v unit (new node L0.5.a)

- Paper: AΘ := Yddot_v × A ∈ Ob(D_v^Θ); Θ_v ∈ O^×(T^÷_AΘ) (well defined up to μ_2l and l·Z); the unit isomorphism
  O^×(T_A) ≅ O^×(T_AΘ) induced by the projection.
- Lean now: `data.product A` (abstract function), `productFunctor`, `ThetaCoverSubcategory` (essential image). There is
  **no declaration named `ATheta`** and no O^× functor on covers.
- Why not derivable: `ThetaProductData` gives only a cone; nothing relates `product A` to a fiber product of X_v-covers,
  and the units O^×(T_A) are not formalized at all.
- Donor: `productFunctor`; for the unit side only the **abstract** `UnitGeneratedMonoidComparison` (which takes
  `u : U →* G` as a parameter — the actual U must come from the Frobenioid, not from an `ℝˣ`).
- Child: `L0.5.a`. Acceptance: an object of `ThetaCoverSubcategory data` that is `data.product A`, plus a Θ_v element
  in the unit group of the actual cover with the normalization of G10 fixed; no `Type`-valued field.

### G4 — geometric theta divisor and source unit comparison (new node L0.5.b; closes F4 (c))

- Paper: EtTh Prop 1.4(i)(iii): zeros at cusps of multiplicity one, pole divisor D_1; Kummer classes =
  O^×_K̃-multiples of Θ̃; Θ_v normalized to 1 at √−1.
- Lean now: (a) F4's `analyticThetaDivisor_trivial` is the **even** theta q-series on q ∈ (0,1) ⊂ ℝ and the file says
  it is not the source divisor; (b) F4's odd-theta statement is the q-adic order-zero special fibre (`U − U⁻¹`), not a
  divisor on a curve; (c) `SourceThetaDivisor` is the archimedean divisor (different object); (d)
  `SourceQlThetaPunctureDivisor` is a formal divisor at the puncture only.
- Why not derivable: the tree has no Yddot (formal/rigid curve over K_v), no meromorphic-function/divisor API on it,
  and no O^×(T^÷). The Kummer class is missing too (G8).
- Donor: `OddTheta`/`OddThetaShift`/`OddThetaNonvanishing`/`OddThetaNormalization` (real/nonarchimedean odd theta),
  `SourceQlThetaPunctureDivisor` (puncture divisor), `SourceQlThetaDivisorPrincipalQuotient` (principal
  subgroup/quotient).
- Child: `L0.5.b`. Acceptance: a divisor object on the actual Yddot with the two divisor equalities, and a Θ_v whose
  divisor is that divisor; **no q-series coefficient comparison** is accepted as the divisor statement.

### G5 — Mq → MΘ (new node L0.5.c)

- Paper: the monoids O^⊷_{C_v^⊢}(A) = O^×(T_A)·q_v^N, O^⊷_{C_v^Θ}(AΘ) = O^×(T_AΘ)·Θ_v^N, and the natural
  isomorphisms compatible with q_v|_T_A ↦ Θ_v|_T_AΘ and O^×(T_A) ≅ O^×(T_AΘ); at the root level q̲_v^{j²} up to μ_2l
  (IUT II intro 97–104, Rm 2.5.1(i)).
- Lean now: `thetaLink (e : U ≃* V) : unitGeneratedSubmonoid u q ≃* unitGeneratedSubmonoid v theta` with
  `degreeG : G →* Multiplicative ℤ`. **Mq and MΘ do not exist**; the strings appear only in comments and in the enum
  constructor `unitComparisonMqMTheta`.
- Why not derivable: (i) no ambient groups G = O^×·q_v^ℤ and H = O^×·Θ_v^ℤ; (ii) no ℤ-valued degree on them
  (`thetaLink` needs `(degreeG q).toAdd ≠ 0`, and the natural Frobenioid degree sends q_v to 1 but
  q̲_v = q_v^{1/2l} to 1/2l ∉ ℤ); (iii) the unit equivalence U ≃* V must come from AΘ → A, which is G3.
- **Decision required in stage 2 (do not guess):** which link is formalized —
  **Variant A** (monoid level, no roots): Mq = O^×(T_A)·q_v^N, MΘ = O^×(T_AΘ)·Θ_v^N, link q_v ↦ Θ_v, degree
  deg(q_v) = deg(Θ_v) = 1 — directly instantiable with the current `thetaLink`;
  **Variant B** (root level): Mq = O^×·q̲_v^ℤ, MΘ = O^×·Θ_v^ℤ, link q̲_v ↦ Θ_v — requires either a generalization of
  `UnitGeneratedMonoidComparison` to a ℤ[1/2l]- or ℚ-valued degree (a donor change with its own consumers) or a
  proof that ⟨q̲_v⟩ ∩ O^× = {1} plus an exponent-valued degree. The handoff formula u·qbar^n ↦ pullback(u)·Θ^n is
  Variant B; the tree's donors only support Variant A. This choice changes the stage-2 statement and must be
  recorded first.
- Child: `L0.5.c`. Acceptance: Mq/MΘ defined from actual objects, `thetaLink` instantiated (or the chosen
  generalization proved), representation independence/multiplicativity/invertibility/naturality inherited, no unproved
  field.

### G6 — μ_2l, l·Z, deck ambiguity (new node L0.5.d)

- Paper: Θ_v determined up to μ_2l(T^÷_Yddot_v) and l·Z ⊆ Aut(T_Yddot_v) (IUT I 3674–3694); the μ_2l-orbit of
  q̲_v^{j²}, independent across j (Rm 2.5.1(i),(iii)).
- Lean now: `CarriesRootSubgroup e mu nu` is a **hypothesis** of the orbit theorem;
  `thetaRootValue_mul_root_of_pow_eq_one` is real-valued; `TemperedDeckGroup` (772 lines, needs
  `[Countable diagram.base.Vertex] [Countable diagram.base.Edge]`) is an inverse-limit deck group of the diagram,
  **not** the l·Z action on T_Yddot_v.
- Why not derivable: no μ_2l subgroup of a value group, no Aut(T_Yddot), no l·Z action, and no compatibility square
  between the two indeterminacies.
- Child: `L0.5.d`. Acceptance: the actual μ_2l and l·Z objects, the orbit theorem instantiated (i.e.
  `CarriesRootSubgroup` **proved**, not assumed), and the link well defined modulo them.

### G7 — tempered synchronization (new node L0.5.e; the hardest)

- Paper: Π_v ↷ ΨF^Θ_v, ∞ΨF^Θ_v, splittings up to torsion compatible with Π_v (IUT II Ex 3.2(i)); Ψ^†F^Θ_v ≅
  Ψ^env(MΘ_*), Ψ^†C_v ≅ Ψ^cns(MΘ_*) (Prop 3.3); multiradiality for full poly-isomorphisms of MΘ_* projective systems
  (Prop 3.4).
- Lean now: **nothing**. `thetaLink_synchronized_evaluation` is only a J-indexed family with one common unit
  equivalence; it is not a Π_v action and does not resolve the μ_2l indeterminacies.
- Why not derivable: no MΘ_* (mono-theta environment), no ΨF^Θ, no Π_v of X_v, no cyclotomic rigidity. Note the
  paper's Rm 2.5.1(iii) says the μ_2l indeterminacies are *not* synchronized; "conjugate synchronization" is a
  separate phenomenon and must not be stated as "one global root".
- Child: `L0.5.e`. Acceptance: a stated theorem with an actual group action; **blocked** until G3/G5 exist.
  Explicitly out of scope for the first L0.5 proof batch.

### G8 — Kummer class / line bundle (new node L0.5.f; closes F4 (d))

- Paper: EtTh Prop 1.4(iii): O^×_K̃·η̃_Θ ∈ H¹(Π^tp_Yddot, Δ^Θ) equals the Kummer classes of Θ̃ values.
- Lean now: `SourceQlThetaLinkBridge.actualEmbeddingScalingSquare` (source l-scaling ↦ consumer p-scaling) is a
  subgroup-level square only; `SourceQlThetaPunctureIdealProjective` isolates the missing line-bundle inputs and the
  affine-infinity obstruction; there is no cohomology class, no Δ^Θ-torsor, no H¹ identification.
- Child: `L0.5.f`. Acceptance: the class defined from the actual theta section and the value equality at points; no
  H¹-valued free field.

### G9 — source q_v and root existence from the contract (new node L0.5.g; prerequisite for G5/G6)

- Paper: q_v ∈ O^⊷(T_X_v) admits a 2l-th root in O^⊷(T_X_v) by Def 3.1(b)+(c) (IUT I 3701–3723); q̲_v determined up
  to μ_2l.
- Lean now: `exists_sourceQv_at_finitePlace_closed` produces a `SourceQv` for a supplied
  `X : PuncturedEllipticCurve F` and `hsplit : X.HasSplitMultiplicativeReductionAt v`; `SourceQv.q` is a
  `Classical.choice`, unrelated to `SourceReductionClause.qParameter : Bad → ℝ`; `SourceThetaRootData.qbar_pow` is a
  supplied field. The arithmetic input `BadPlaceQParameterCards.sourceQParameterOrder` (positive, prime to l) exists
  but is not connected to the root data.
- Why not derivable: the contract has `badPlaces : Type u` with labels, not finite places of F; the bridge from
  `S.badPlaces`/`V_mod_bad` to `v : NumberField.FinitePlace F` + `HasSplitMultiplicativeReductionAt` is
  `BadPlaceReductionCards` (`SourcePlacePartitionReduction.lean:787`), a card.
- Child: `L0.5.g`. Acceptance: a theorem producing X, v, hsplit, q_v from S and a bad place, and a construction of
  qbar (or the exact field extension/order condition under which it exists), with the contract's `qParameter` matched
  (or the mismatch recorded as a target change).

### G10 — normalization and sign convention (blocking, must be fixed before any stage-2 statement)

Four normalizations coexist and are mutually inconsistent:

1. `ActualSourceThetaLink.sourceOddTheta_normalized`: oddTheta(q, i·(qbar^l)^j)/oddTheta(q, i) = (qbar^l)^(−j²)
   (denominator oddTheta(q,i) = 2i, exponent −j² on qbar^l);
2. EtTh Prop 1.4(ii): Θ̃(q_X^{a/2}U) = (−1)^a q_X^{−a²/2} U^{−2a} Θ̃(U) — a sign and a U^{−2a} factor;
3. F4 `normalizedTheta` / `thetaUnit = q^{j²}` (positive exponent, real q);
4. IUT I Ex 3.2(ii): Θ_v is the **reciprocal** of the l-th root, normalized to 1 at √−1; IUT II intro/Rm 2.5.1(i):
   theta values are q̲_v^{j²} (positive exponent on q̲_v) up to μ_2l.

Before G5/G6 can be stated, one written convention must fix: the choice of qbar (qbar^{2l} = q), the value of r in
r² = q (here r = qbar^l), the exponent sign, whether Θ_v is the theta function or its reciprocal, and the
normalization point (√−1 vs the ratio at i). Conclusion: **the convention is not fixed by the current donors**; any
stage-2 statement written first would have to be rewritten.

### G11 — the "split Frobenioid" level of the link

The paper's link is between split Frobenioids F_v^⊢ ≌ F_v^Θ with τ_v^⊢ ↦ τ_v^Θ (IUT I 3862–3877), not only between
monoids. The tree has the abstract `PreFrobenioid`/`FrobenioidPresentation`/`FrobenioidAxioms` layer and one
model-only presentation (`ConcreteSourceFrobenioidBridge.concreteStageModel`, concrete Gaussian place above 5), but
no C_v^⊢/C_v^Θ for the source, and no μ_2l-orbit of characteristic splittings. This is a **separate obligation** from
G5; it must not be silently dropped by proving only the monoid statement. Child: `L0.5.h` (blocked by G5).

## 7. Node-local stages, children, next action

    node: l05-source-theta-link
    stage1: open (this record): paper objects fixed; donors and gaps enumerated; conventions/quantifiers partly fixed
    stage2: not_started (no statement freezable before G9/G10/G5-decision)
    stage3: not_started
    children: L0.5.a ATheta+Theta_v (blocked by L1-F8b-e)
              L0.5.b geometric divisor/unit (blocked by a)
              L0.5.c Mq->MTheta (blocked by a; needs Variant A/B decision)
              L0.5.d mu_2l / l-Z deck (blocked by c)
              L0.5.e tempered synchronization (blocked by c; separate research)
              L0.5.f Kummer class / line bundle (blocked by b/d)
              L0.5.g source q_v + root existence (independent; can start first)
              L0.5.h split-Frobenioid level (blocked by c)
    upstream: L1-F8a (sourceDiagram/sourceRoot, named sorry), L1-F8b-e, L1-F4 (analytic theta)

**One executable next step** (cheapest real evidence, no production edit): a serialized compile probe of
`tmp/n8-20261018/general/ActualSourceThetaLink.lean` — it is the only existing Lean object that states an actual
source-level odd-theta value and it has **no build evidence**; the probe either gives L0.5 a checked analytic leg or a
precise error to triage. Command shape: `lake env lean tmp/n8-20261018/general/ActualSourceThetaLink.lean`, log the
exit status verbatim. In parallel (document-only, no Lean): freeze G10's convention and the G5 Variant A/B choice,
since both are prerequisites for every stage-2 statement of L0.5.a–L0.5.c.

**Do not** in the next batch: declare a ThetaLink structure/card; declare Mq/MΘ as arbitrary types; use
`HodgeTheaterLink` as the source link (it is q-preserving); use `SourceThetaDivisor` as the geometric theta divisor;
use `FiniteThetaPacket`/`AnalyticThetaCarrier`/`thetaUnit : ℝˣ` as the source theta values; re-declare
`sourceDiagram` (owned by L1-F8a); edit `ThetaLinkSourceCover.lean` (owned by its production owner, currently red).

## 8. Acceptance boundary of this record

- `statement_compiles`: **n/a** — this stage writes no Lean declaration.
- `proof_body_checked`: **no**.
- `kernel_closed`: **no**.
- `target_accepted`: **no**.
- No production file was modified. No build, comparator or axiom probe was run in this stage. Every status above is
  either quoted from the cited file/record or a direct file observation (existence of `.olean`, importer search,
  SHA-256); nothing is claimed as re-verified.

Status of this record itself: stage 1 is **open**, not complete: G9/G10 and the G5 Variant decision remain, and the
F8 donor is red. The record stops here by design; the next stage-1 increment is the two document decisions above plus
the donor compile probe.
