# Public-interface card — source_original_arithmetic_input-v1

Run: `core-construction-map-20261014` · Agent: `dsh_original_input_owner` (gen 2, RUNNING) · Parent: `stepxi_module_supervisor`
Protocol: `iut-agent-tree/2026-10-13-v1` · Contract digest: `d4d54f29ce4d5ef081315ba738b9d3670535ed8f0c1239e2e859d6ebc2802056`
Status: **PUBLIC_PACKAGE_COMPLETE** (no unresolved required cross-owner interface)

Scope: the four whitelisted Theorem 3.11 source modules only. No sibling/parent sources, probes, logs, checkpoints or public entry docs were read. Compiler transitive reads are program execution, not model-read authority.
Evidence basis: direct source inspection of the four paths below **plus** an owned probe run in the existing cached environment (public types/axioms only, no `#print` bodies, no `lake build`).

---

## 1. Exact paths, source SHA256 (before and after), line locators

All four files were read once and hashed before and after; hashes are identical. No source was edited.

| Path | SHA256 | Bytes | Lines | mtime |
|---|---|---|---|---|
| `d:\lean\leanformal\iut\iutiii\theorem311\SourceOriginalInput.lean` | `11C288D385682760B56890B24C57F1738A771DC6A75E2543EFFD67D9FFAFA795` | 65214 | 1663 | 2026-08-11T12:07:49+08:00 |
| `d:\lean\leanformal\iut\iutiii\theorem311\InitialThetaInputCore.lean` | `47DFC4FBF3A980381D580EE56342F6084C170EBB2C87671085DE1B06D1E60F1A` | 1013 | 39 | 2026-08-11T17:40:41+08:00 |
| `d:\lean\leanformal\iut\iutiii\theorem311\SourceHodgeTheaterBridge.lean` | `DDACDA6560CEE45712A134F96585BB001B8B519745FB4291CEC602A5D6F366BE` | 77010 | 1983 | 2026-08-09T09:11:06+08:00 |
| `d:\lean\leanformal\iut\iutiii\theorem311\SourceProcessionBoundary.lean` | `11185E318457E143AB24AFED854257F10D8347EF017DEB3932C15EB58B5A4442` | 22606 | 530 | 2026-08-07T11:29:02+08:00 |

Owned artifacts written this run:
- probe (read_write): `d:\lean\metadata-probes\core-construction-map-20261014\source_original_arithmetic_inputaudit.lean` and `_part2`…`_part9` variants (public `#check`/`#print axioms` only).
- evidence log (append): `d:\lean\logs\coordination\source_original_arithmetic_input-20261014.jsonl`.

### Relevant imports / version limitations

- `SourceOriginalInput.lean:1-2` imports `LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Boundary` and `LeanFormal.IUT.IUTI.HodgeTheater.SourceHodgeTheaterFamily`.
- `InitialThetaInputCore.lean:1-2` imports `LeanFormal.IUT.IUTI.InitialTheta.ArithmeticData` and `Mathlib.Data.Real.Basic`.
- `SourceHodgeTheaterBridge.lean:1-5` imports `SourceFaithfulBoundary`, `SourceDefinition31Boundary`, `IUTI.HodgeTheater.HodgeTheaterCore`, `IUTII.Kummer.VerticalLogKummer`, `Mathlib.Tactic`.
- `SourceProcessionBoundary.lean:1-5` imports `ParametricDStage`, `ConcreteRouteNormalForm`, `IUTI.HodgeTheater.History`, `IUTII.Theta.ConcreteSourceHistoryLinkBridge`, `Mathlib.Tactic`.
- **Version limitation (must be preserved):** olean artifacts in `d:\lean\.lake\build\lib\lean\...` for all four modules have build timestamps *earlier* than the current source mtimes and the source tree is under active ledger repair. The cached environment therefore **cannot certify the current source bytes**. The probe results are corroborating public metadata only; the inspected source text is the authority for statements below.
- `SourceProcessionBoundary.lean` opens `ParametricTheorem311`, `SourceFiniteParameterized`, `ConcreteFiniteTheorem311`, `ConcreteSourceHistoryLinkBridge`, `ConcreteRouteNormalForm` at the concrete finite stage; that concrete instance is a finite stage, not a general source construction.

---

## 2. Complete meaningful public types/signatures for the target

Universe parameters, variables and typeclass assumptions are reproduced exactly as checked. Where a structure is declared in an *imported* module (outside model-read authority) the fields are given from the public environment query only; their provenance module is named but not read.

### 2.1 Root input contract — `Theorem311Source.OriginalInput` (`SourceOriginalInput.lean:39-46`)

```
abbrev SourceTheorem311Index := Int × Int
universe ua uv upi umon ui
structure OriginalInput (l : PrimeGeFive) (V : Type uv) where
  initial : SourceDefinition31Data.{ua} l
  family : SourceHodgeTheaterFamily.{ua, uv, upi, umon, ui} l V
  index_equiv : family.index ≃ SourceTheorem311Index
  arithmetic_alignment : ∀ i, (family.theater i).arithmetic = initial.arithmetic
```
`#check`-confirmed universe: `OriginalInput : PrimeGeFive → Type u_2 → Type (max (max (max (max (u_1+1) (u_5+1)) (u_4+1)) (u_3+1)) u_2)`.

Projections and proved consequences (all in `namespace OriginalInput`, lines 48-1636):
- `indexOf (n m) : I.family.index := I.index_equiv.symm (n,m)` (53)
- `theaterAt (n m) : HodgeTheater.{ua,uv,upi,umon} l V` (56)
- `linkAt (n m n' m') : HodgeTheaterLink (I.theaterAt n m) (I.theaterAt n' m')` (60)
- `indexOf_apply` (64), `indexOf_injective` (68), `theaterAt_eq_iff` (85), `theaterAt_injective` (95)
- `theaterAt_arithmetic (n m) : (I.theaterAt n m).arithmetic = I.initial.arithmetic` (101)
- `linkAt_refl` (114), `linkAt_symm` (118), `linkAt_trans` (123), `linkAt_q` (129), `linkAt_scale` (134)
- `horizontalLink` (139), `verticalLink` (143), `horizontal_q`/`vertical_q` (147/152), `square_link_eq` (181)
- `route` (200), `path` (684), `primeStripAt` (788), `dPrimeStripAt` (791), `primeStripLinkAt` (804)
- `initialArithmetic : InitialThetaArithmeticData.{ua} l := I.initial.arithmetic` (241)
- `initialThetaInput : InitialThetaInput.{ua} l := I.initial.toInitialThetaInput` (1297)
- `initial_arithmetic_sqrt_neg_one : HasSqrtNegOne I.initial.arithmetic.F` (1487)
- `initial_arithmetic_degree_prime_to_l : Nat.Coprime (Module.finrank I.initial.arithmetic.Fmod I.initial.arithmetic.F) l.value` (1491)
- `source_root_bundle (n m) : (I.theaterAt n m).arithmetic = I.initial.arithmetic ∧ Nonempty I.initial.selectedPlaces ∧ I.initial.torsion.imageContainsSL2 ∧ Function.Surjective I.initial.orbicurve.exactSequence.projection ∧ 0 < I.initial.cusp.epsilon` (1556)

### 2.2 Minimal initial-Theta input — `Theorem311Source.InitialThetaInput` (`InitialThetaInputCore.lean:21-33`), public constructor

```
structure InitialThetaInput (l : PrimeGeFive) where
  arithmetic : InitialThetaArithmeticData l
  selectedPlaces : Type u
  badPlaces : Type u
  badIncluded : badPlaces → selectedPlaces
  selectedNonempty : Nonempty selectedPlaces
  badFinite : Fintype badPlaces
  stableReduction : badPlaces → Prop
  stableReduction_proved : ∀ v, stableReduction v
  torsionImage : Prop
  torsionImage_proved : torsionImage
  cuspParameter : Real
  cusp_positive : 0 < cuspParameter
```

### 2.3 Arithmetic datum and Definition 3.1 boundary (imported; public environment query only)

`InitialThetaArithmeticData : PrimeGeFive → Type (u+1)` with fields (checked types only):
`F Fmod K : Type u`; `NumberField`/`Field` instances `fieldF fieldFmod fieldK numberFieldF numberFieldFmod numberFieldK`; `Algebra` instances `algebraFmodF algebraFK algebraFmodK`; `IsScalarTower Fmod F K`; `FiniteDimensional` + `IsGalois` for `Fmod/F` and `F/K` (`finiteFmodF galoisFmodF finiteFK galoisFK`); `tower : ThetaFieldTower l self.Fmod self.F self.K`; `curve : PuncturedEllipticCurve self.F`.

`ThetaFieldTower` is a `Prop` with `sqrtNegOne : ThetaFieldTower l Fmod F K → HasSqrtNegOne F` and `degreePrimeToL : ThetaFieldTower l Fmod F K → (Module.finrank Fmod F).Coprime l.value`.

`SourceDefinition31Data : PrimeGeFive → Type (u+1)` (public constructor, verbatim field order):
```
arithmetic : InitialThetaArithmeticData l
selectedPlaces : Type u
badPlaces : Type u
reduction : SourceReductionClause self.selectedPlaces self.badPlaces
torsion : SourceTorsionClause l
orbicurve : SourceOrbicurveClause
sections : SourceSectionClause
cusp : SourceCuspClause
arithmetic_reduction_compatibility : Prop
arithmetic_reduction_compatibility_proved : self.arithmetic_reduction_compatibility
arithmetic_torsion_compatibility : Prop
arithmetic_torsion_compatibility_proved : self.arithmetic_torsion_compatibility
arithmetic_orbicurve_compatibility : Prop
arithmetic_orbicurve_compatibility_proved : self.arithmetic_orbicurve_compatibility
arithmetic_section_compatibility : Prop
arithmetic_section_compatibility_proved : self.arithmetic_section_compatibility
arithmetic_cusp_compatibility : Prop
arithmetic_cusp_compatibility_proved : self.arithmetic_cusp_compatibility
```
`toInitialThetaInput : SourceDefinition31Data l → InitialThetaInput l` (public constructor map).

Clause records consumed by Definition 3.1 (public constructors):
- `SourceReductionClause (Selected Bad : Type u)`: `partition : SourcePlacePartition Selected Bad`; `stableReduction multiplicativeReduction splitMultiplicativeReduction : Bad → Prop` with `…_proved : ∀ b, …`; `reductionCompatibility : ∀ b, splitMultiplicativeReduction b → multiplicativeReduction b`; `qParameter : Bad → ℝ`; `qParameter_nonzero : ∀ b, qParameter b ≠ 0`; `qParameter_contracting : ∀ b, ‖qParameter b‖ < 1`; `qParameter_reduction_compatibility : ∀ b, stableReduction b → qParameter b ≠ 1`.
- `SourceTorsionClause l`: `representationCarrier/G : Type`; `torsionCarrier/G : Type`; `representation : self.representationCarrier →* self.representationGroup`; `imageContainsSL2 sixTorsionIndependent lTorsionCompatible : Prop`.
- `SourceOrbicurveClause`: `curve : Type u`, `puncturedCurve : Type v`, `cover : Type w`, `structureGroup : Type u` with `Group`, `curveToPunctured : puncturedCurve → curve`, `coverToPunctured : cover → puncturedCurve`, `cover_surjective : Function.Surjective coverToPunctured`, `exactSequence : SourceExactSequenceClause`, `cuspCount : ℕ`, `cuspCount_pos : 0 < cuspCount`, `curveCompatibility : Prop`, `curveCompatibility_proved : curveCompatibility`.
- `SourceSectionClause`: `valuationCarrier : Type u`, `modifiedValuationCarrier : Type v`, `sectionMap : valuationCarrier → modifiedValuationCarrier`, `finitePlaceData infinitePlaceData : Prop`.
- `SourceCuspClause`: `epsilon : ℝ`, `epsilon_compatibility : Prop` (positive/nonzero lemmas proved in the boundary module).

`SourceDefinition31Data.source_curve_bundle : Function.Surjective S.orbicurve.coverToPunctured ∧ 0 < S.orbicurve.cuspCount ∧ S.orbicurve.curveCompatibility`.

### 2.4 Bridge realization records (`SourceHodgeTheaterBridge.lean`)

- `SourceHodgeTheaterSystem (l) : Type` (40-65): `source : SourceDefinition31Data.{u} l`; `source_universe_anchor : Type u`; `index : Type w`; `theaterCarrier : Type v`; `theater : index → theaterCarrier`; `distinct : Function.Injective theater`; `qParameter : index → Real`; `scale : index → SignedLabel l.value → Real`; `link : ∀ i j, theaterCarrier → theaterCarrier`; `link_refl`, `link_trans`; `q_naturality`, `scale_naturality`; `permutation : Equiv.Perm index`; `permutation_q`, `permutation_scale`.
- `SourceLGPProcession (l) (Label : Type u) (Choice : Type v) [AddGroup Label] [Preorder Choice]` (158-183): `hodge : SourceHodgeTheaterSystem.{u,v,v} l`; `base : Choice`; `level : Choice → Nat`; `ind1 ind2 : Label → Choice → Choice`; `ind3 : Nat → Choice → Choice`; zero/add/inverse laws for `ind1`, `ind2` (additive, reversed-composition form), `ind3`; pairwise commutativity laws; `ind1_level`, `ind2_level`, `ind3_level : level c ≤ level (ind3 n c)`; `source_index : Choice → hodge.index`; `ind1_index/ind2_index/ind3_index` invariance.
- `SourcePacketRealization (P)` (339-360): `carrier : Choice → Type w`; `distinguished : ∀ c, carrier c`; `logVolume determinant : Choice → Real`; `determinant_positive : ∀ c, 0 < determinant c`; `log_determinant : ∀ c, Real.log (determinant c) = logVolume c`; `possibleImage : Choice → Set Real`; `possibleImage_nonempty`; `ind1_volume/ind2_volume : logVolume (P.ind1 g c) = logVolume c`; `ind3_volume : logVolume c ≤ logVolume (P.ind3 n c)`; matching determinant and image laws; `image_ind3 : ∀ n c z, z ∈ possibleImage c → ∃ y, y ∈ possibleImage (P.ind3 n c) ∧ z ≤ y`.
- `SourceVerticalRealization (P) (Q)` (528-553): `vertical : UpperSemiCorrespondence Nat Real`; `vertical_monotone`; `nonarchimedeanImage archimedeanImage : Nat → Set Real → Set Real`; `nonarchimedean_inclusion`; `archimedean_surjection`; `nonarchimedean_profile/archimedean_profile : image m (Q.possibleImage c) = Q.possibleImage (P.ind3 m c)`; `kummer : ∀ c, LabelledKummerIso Choice Choice`; `kummer_label`.
- `SourceEvaluationBridge (P) (Q) (V)` (730-753): `evaluation : EvaluationSystem Choice Choice`; `horizontal : HorizontalLGPLink Choice Choice`; `kummer_horizontal`; `label_horizontal`; `evaluation_horizontal`; `upper_horizontal`; `horizontal_left_index/horizontal_lower_index` (source-index invariance).
- `SourceTheorem311Realization (l) (Label) (Choice) [AddGroup Label] [Preorder Choice]` (910-919): `procession : SourceLGPProcession.{u,v}`; `packet : SourcePacketRealization.{u,v,w} procession`; `vertical : SourceVerticalRealization.{u,v,w} procession packet`; `evaluation : SourceEvaluationBridge.{u,v,w} procession packet vertical`; `genericFamily : TheaterFamily Choice Choice`; `labelledCount : Nat`; `labelledCount_pos : 0 < labelledCount`.

### 2.5 The two top-level conditional exports (`SourceHodgeTheaterBridge.lean`)

```
def SourceTheorem311Realization.input :
  SourceTheorem311Realization l Label Choice → DerivedPrerequisiteInput Label Choice        -- (928)
def source_realization_theorem311 :
  (R : SourceTheorem311Realization l Label Choice) → Theorem311Output R.input                -- (1573)
def source_bridge_conditional_output :
  (R : SourceTheorem311Realization l Label Choice) → Theorem311Output R.input                -- (1676)
```
`DerivedPrerequisiteInput` is the public environment name of the record that the module header calls the “older `Theorem311Source.Input` type … a deliberately named *derived-prerequisite* package” (`SourceOriginalInput.lean:22-24`). Public fields (checked types only):
`labelPrime : PrimeGeFive`; `prime : DPrimeStripProcession Label Choice`; `packet : ProcessionPacketProfile self.prime`; `localPacket : LocalTensorPacket self.prime`; `initial : InitialThetaInput self.labelPrime`; `vertical : UpperSemiCorrespondence ℕ ℝ`; `vertical_monotone`; `verticalSite : VerticalSiteData Choice`; `labelledCount : ℕ`; `labelledCount_pos`; `evaluation : EvaluationSystem Choice Choice`; `labelledKummer : Choice → LabelledKummerIso Choice Choice`; `family : TheaterFamily Choice Choice`; `horizontal : HorizontalLGPLink Choice Choice`; `kummer_horizontal_compat`; `labelled_horizontal_compat`; `evaluation_horizontal_compat`.

`Theorem311Output : {Label Choice} → [AddGroup Label] → [Preorder Choice] → DerivedPrerequisiteInput Label Choice → Type (u_2+1)` (declared in the imported boundary module; not read).

### 2.6 Procession boundary record (`SourceProcessionBoundary.lean:33-50`)

```
structure Input where
  theater : HodgeTheater.{ua,uv,upi,umon} l V
  history : HodgeTheaterHistory.{ua,uv,upi,umon} l V theater
  carrier : Carrier Label Choice
  baseChoice : Choice
  baseChoice_eq : baseChoice = carrier.core.base
  packetVolume : Choice → Real
  packetVolume_eq_profile : ∀ c, packetVolume c = carrier.profile.logVolume c
  base_packetVolume_eq_theta : packetVolume baseChoice = theater.thetaPacket.logVolume
  target_q : Real
  target_q_eq : target_q = history.terminal.thetaPacket.q
  history_q_eq : theater.thetaPacket.q = history.terminal.thetaPacket.q
  route_normal_form : ∀ route, ∃ b n,
    carrier.core.level b = carrier.core.level carrier.core.base ∧
    routeTarget carrier route carrier.core.base = carrier.core.ind3 n b
```
Proved inside it: `profile_base_eq_theta` (70), `target_q_eq_source` (85), `compositeLink` (89), `routeOutput` (167), `indeterminacyEvidence` (227), `dStage` (269), `canonicalOutput` (302), and the assembly `sourceTheorem311Certificate : SourceTheorem311Certificate input` (361). `concreteInput (l : PrimeGeFive) : Input (V := FinitePrimePlace 2 7) (Label := ConcreteFiniteTheorem311.finiteLabel l) (Choice := ConcreteFiniteTheorem311.ProcessionChoice l)` (431). Audit entries: `sourceOriginalInputBoundary` (`SourceOriginalInput.lean:1646`), `sourceHodgeTheaterBridge` (1966), `sourceProcessionBoundary` (515), all `status := VerificationStatus.interface`.

---

## 3. Source-supported dependency edges (producer → consumer, with status)

| # | Producer (exact signature anchor) | Consumer (exact signature anchor) | Edge content | Status |
|---|---|---|---|---|
| E1 | `SourceDefinition31Data l` (imported boundary) | `OriginalInput.initial` (`SourceOriginalInput.lean:42`) | supplied field | supplied-field |
| E2 | `SourceHodgeTheaterFamily l V` (imported) | `OriginalInput.family` (`:43`) | supplied field | supplied-field |
| E3 | `OriginalInput.index_equiv` (`:44`) | `indexOf`, `theaterAt`, `linkAt` (`:53,56,60`) | projection | proved |
| E4 | `OriginalInput.arithmetic_alignment` (`:45`) | `theaterAt_arithmetic` (`:101`), `source_root_bundle` (`:1556`) | projection | proved |
| E5 | `SourceDefinition31Data.toInitialThetaInput` (imported) | `InitialThetaInput` constructor (`InitialThetaInputCore.lean:21`) and `OriginalInput.initialThetaInput` (`:1297`) | constructor map | proved (definitional) |
| E6 | `SourceHodgeTheaterFamily.link` (imported) | `linkAt`, `horizontalLink`, `verticalLink` and 100+ transport lemmas (`:114-1625`) | projection + reindexing | proved |
| E7 | `HodgeTheaterLink.{theta_q_eq,theta_scale_eq,primeStripEquiv}` (imported) | `linkAt_q` (`:129`), `linkAt_scale` (`:134`), `primeStripLinkAt` (`:804`) | projection | proved |
| E8 | `SourceTheorem311Realization` fields (`Bridge:910`) | `DerivedPrerequisiteInput` (`Bridge:928`) | componentwise packaging | proved (definitional assembly) |
| E9 | `Theorem311Source.Theorem311Output` (imported) | `R.output` inside `SourceTheorem311Realization` (`Bridge:1573,1676`) | conclusion assumed by the realization; only repackaged | output-assumes-conclusion |
| E10 | `SourceProcessionBoundary.Input` fields (`:33`) | `sourceTheorem311Certificate` (`:361`), `routeOutput` (`:167`) | projection/assembly | proved |
| E11 | `SourceProcessionBoundary.Input` | `SourceTheorem311Certificate` conclusion | the certificate records source/dStage/indeterminacy/routeNormalization only; it does **not** derive `Theorem311Output` | proved (limited content) |
| E12 | `concreteInput (l)` (`:431`) | all `concreteInput_*` lemmas (`:465-503`) | single finite-stage instance | concrete finite instance, not general |
| E13 | `SourceHodgeTheaterSystem` (`Bridge:40`) | `SourceLGPProcession.hodge` (`Bridge:160`) | supplied field | supplied-field |
| E14 | `SourceLGPProcession` (`Bridge:158`) | `SourcePacketRealization`/`SourceVerticalRealization`/`SourceEvaluationBridge` (`Bridge:339,528,730`) | parameter | proved (typing) |
| E15 | `InitialThetaArithmeticData` (imported) | `InitialThetaInput.arithmetic`, `HodgeTheater.arithmetic`, `SourceDefinition31Data.arithmetic` | supplied field | supplied-field |
| E16 | `ThetaFieldTower` (imported) | `InitialThetaArithmeticData.tower`; consumed at `OriginalInput.initial_arithmetic_sqrt_neg_one` (`:1487`), `initial_arithmetic_degree_prime_to_l` (`:1491`) | supplied field + projection | supplied-field, then proved |
| E17 | `SourceOriginalInput` (whole module) | sibling packages that import it (e.g. `SourceHodgeTheaterBridge` does **not** import it; `SourceProcessionBoundary` does not) | no edge found inside bounded scope | unresolved external consumer |

Note on E17: within the four owned files, `SourceOriginalInput.OriginalInput` is not consumed by `SourceHodgeTheaterBridge`; the bridge builds its conclusion from the *derived* `DerivedPrerequisiteInput`/`Theorem311Output` records instead. Downstream consumers of `OriginalInput` lie outside this bounded package and were not inspected.

---

## 4. Actual paper-fidelity boundary

Compilation and typechecking do **not** show that these Lean objects are the paper's objects. Concretely:

1. **Actual arithmetic data vs abstract carrier.** `InitialThetaArithmeticData` carries genuine field-theoretic content (NumberField/Algebra/IsGalois/FiniteDimensional instances, `ThetaFieldTower`, and a `PuncturedEllipticCurve` over `F`); the cached environment contains `concreteGaussianInitialThetaArithmeticData (l) : InitialThetaArithmeticData l` whose `curve` is provably `concreteSplitPuncturedCurve.baseChange GaussianField`. By contrast, in `SourceDefinition31Data` the place types, torsion/orbicurve/section carriers are bare `Type` fields, and `SourceOrbicurveClause.curve : Type u` is *not* tied by any visible field to `InitialThetaArithmeticData.curve`.
2. **Opaque compatibility propositions.** The five `arithmetic_*_compatibility : Prop` fields of `SourceDefinition31Data` (and `SourceOrbicurveClause.curveCompatibility`, `SourceTorsionClause.*`, `SourceCuspClause.epsilon_compatibility`) are arbitrary propositions paired with proofs of themselves. From the owned package there is no source-visible content forcing them to say anything about the curve, the Tate module, the prime strips, or the paper's Definition 3.1 clauses.
3. **`InitialThetaInput` is a witness bundle.** `selectedPlaces : Type u` with `Nonempty`, `badPlaces : Type u` with `Fintype`, `stableReduction : badPlaces → Prop` with `∀ v` proof, `torsionImage : Prop` with a proof, and `cuspParameter : Real` with `0 < cuspParameter`. Nothing in the owned package builds these places from the arithmetic curve or identifies `cuspParameter` with a cusp value.
4. **Bridge records are inhabited only by hypothesis.** `SourceTheorem311Realization`, `SourceLGPProcession`, `SourcePacketRealization`, `SourceVerticalRealization`, `SourceEvaluationBridge` are structure *types*; the only construction appearing in this package is `SourceProcessionBoundary.Input.concreteInput` at finite prime places `FinitePrimePlace 2 7` with `ConcreteFiniteTheorem311` labels/choices. The audit note itself marks the bridge's arithmetic-geometric existence as “still a source-facing obligation”.
5. **`source_realization_theorem311` / `source_bridge_conditional_output` are conditional wrappers.** Their conclusion `Theorem311Output R.input` is produced from `R.output`, i.e. the conclusion is assumed by the realization record, not derived. This matches the module-header statement that the audit entry “remains an interface until an arithmetic-geometric construction supplies an inhabitant of this bridge.”
6. **The two `Input` records are distinct namespaces.** `Theorem311Source.DerivedPrerequisiteInput` (bridge target) and `SourceProcessionBoundary.Input` (finite-stage procession record) are different structures and are not linked by any theorem in this package.

---

## 5. Earliest necessary unproved construction in this bounded package

**Statement (exactly as forced by the owned source, no invented quantifiers).**

There is no inhabitant of the root input contract inside this package. Precisely, the first necessary unproved construction is:

```
∀ (l : PrimeGeFive) (V : Type uv),
  ∃ (S : SourceDefinition31Data.{ua} l)
    (F : SourceHodgeTheaterFamily.{ua,uv,upi,umon,ui} l V)
    (e : F.index ≃ SourceTheorem311Index),
    ∀ i, (F.theater i).arithmetic = S.arithmetic
```

- This is the exact type of the argument tuple of `OriginalInput` (`SourceOriginalInput.lean:41-46`); it is presented as the *existence obligation* whose fields the structure supplies, not as a source-derived theorem.
- Full hypotheses: `l : PrimeGeFive` (i.e. `5 ≤ l.value`); `V : Type uv`; five universe parameters `ua uv upi umon ui`; the typeclass assumptions are those carried by `SourceHodgeTheaterFamily` and `HodgeTheater` (queried: `HodgeTheater : PrimeGeFive → Type u_2 → Type ...`, `SourceHodgeTheaterFamily : PrimeGeFive → Type u_2 → Type ...`).
- **Honesty limitation.** The internal content of `InitialThetaArithmeticData`'s field-level quantifiers and the four `SourceDefinition31Data` clause records are available (Section 2.3); the *contents* of the five `arithmetic_*_compatibility : Prop` fields are **not** available from the owned package (they are opaque `Prop`s in the imported boundary module). Therefore the inner statement “S is the paper's actual Definition 3.1 datum” is **not** an exactly formalized Lean proposition here, and this card does **not** present it as one. If an exact formula for those five Props is required, the precise versioned interface request is recorded in Section 6.
- Immediate actual consumer: `OriginalInput.initial` / `.family` / `.index_equiv` / `.arithmetic_alignment` (`SourceOriginalInput.lean:42-45`), consumed by `theaterAt_arithmetic` (`:101`) and `source_root_bundle` (`:1556`). Downstream, the pipeline that reaches the Theorem 3.11 conclusion is `SourceTheorem311Realization.input` → `Theorem311Output` (`SourceHodgeTheaterBridge.lean:928,1573,1676`).
- Versions/evidence: the four files at the SHA256s in Section 1; probe outputs in Section 8; no `sorryAx`.
- Acceptance criterion: a Lean definition inhabiting `SourceDefinition31Data l` and a definition inhabiting `SourceHodgeTheaterFamily l V` with the equivalence and the alignment equation, all kernel-checked against the *current* source bytes, and — separately required — a source-fidelity review that the five opaque compatibility Props carry the paper's Definition 3.1 content.

A strictly earlier necessary obligation (the arithmetic core) is the inhabitation of `InitialThetaArithmeticData l` with non-split source content; the cached `concreteGaussianInitialThetaArithmeticData` is a concrete instance but is the split/Gaussian example, not the general source construction.

---

## 6. Versioned interface request (only if the boundary-module contents are needed)

No cross-owner information is required for this package to be complete. If the parent wants the *inner* content of the Definition 3.1 boundary formalized exactly, the following exact request is needed (owner of `LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Boundary`, currently outside model-read authority):

- Missing declarations: the public definitions/values of `SourceDefinition31Data.arithmetic_reduction_compatibility`, `.arithmetic_torsion_compatibility`, `.arithmetic_orbicurve_compatibility`, `.arithmetic_section_compatibility`, `.arithmetic_cusp_compatibility` (and `SourceOrbicurveClause.curveCompatibility`), in the form of their defining propositions over `InitialThetaArithmeticData` and the clause types in Section 2.3.
- Missing construction: an inhabitant `SourceDefinition31Data l` (general, not `l`-specific finite model) and a `SourceHodgeTheaterFamily l V` with `index ≃ ℤ × ℤ`.
- Import needed by the requester: the module path only (`LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Boundary`, `LeanFormal.IUT.IUTI.HodgeTheater.SourceHodgeTheaterFamily`); the requester already compiles against them.
- Reason needed: to turn Section 5's existence obligation into an exactly quantified Lean statement and to replace the opaque `Prop` placeholders by the paper's Definition 3.1 conditions.

---

## 7. Verification commands and outcomes

- `lake env lean D:/lean/metadata-probes/core-construction-map-20261014/source_original_arithmetic_inputaudit.lean` (and `_part2`…`_part9`): all intended `#check`/`#print axioms` outputs produced. Exit 1 appeared only from deliberate `unknownIdentifier` probe lines (`InitialThetaArithmeticData.l`, `InitialThetaTower`, `Input.prime` under the wrong namespace, `PuncturedEllipticCurve.base`) and from the `#eval`-vs-`print` parser quirk; these are probe-annotation errors, not source errors.
- `#print axioms` results (representative, all identical in shape):
  `OriginalInput.indexOf_apply`, `.theaterAt_arithmetic`, `.initial_selected_nonempty`, `.initial_arithmetic_sqrt_neg_one`, `.initialThetaInput_eq_projection`, `SourceHodgeTheaterBridge.source_hodge_groupoid_closed`, `source_realization_theorem311`, `source_bridge_conditional_output`, `SourceTheorem311Realization.input`, `SourceProcessionBoundary.Input.sourceTheorem311Certificate_theta`, `.concreteInput_profile_base`, `.routeOutput` → each depends on axioms `[propext, Classical.choice, Quot.sound]` only.
- **`sorryAx` is absent** from every queried declaration. A text scan of the four owned files found no `sorry`/`admit`/`axiom` declarations; the only occurrence of the token “sorry” is inside the audit prose at `SourceProcessionBoundary.lean:524`.
- Source inspection is separated from stale cached metadata: the types above come from source inspection plus probe corroboration; the .olean timestamps are older than the current sources, so the probe cannot certify the current bytes.

---

## 8. Completed work and precise remaining gap

Completed (this run):
- child bootstrap (`...-bootstrap-v1`, exit 0) → state `READY` gen 2; self-inspect confirmed contract digest/version/run/protocol/whitelist.
- SHA256 freeze (identical before/after) and full public-interface extraction of all four owned files, including the exact constructors of `OriginalInput`, `InitialThetaInput`, `SourceDefinition31Data`, the clause records, the bridge realization records, and `SourceProcessionBoundary.Input`.
- Axiom audit: no `sorryAx`; only the three standard axioms.
- Paper-fidelity boundary identified: concrete arithmetic data exists as a split/Gaussian instance; the Definition 3.1 place/compatibility data is abstract or opaque; the bridge and conditional output assume their conclusions.
- Owned probe and evidence log appended; no source edits; no builds attempted on repairing ledger/dependents.

Precise remaining gap (source-facing, outside this package's construction authority):
1. A general inhabitant of `SourceDefinition31Data l` and of `SourceHodgeTheaterFamily l V` with `index ≃ ℤ × ℤ` and the arithmetic-alignment equation (Section 5).
2. Definitions of the five opaque `arithmetic_*_compatibility : Prop` fields (Section 6), without which the paper-fidelity of Definition 3.1 cannot be stated as an exact Lean proposition.
3. A construction inhabiting `SourceTheorem311Realization` for arbitrary source data (presently only assumed; the finite `concreteInput` is one instance).
4. Bounded-scope caveat: absence of a construction inside these four files is **not** evidence of global absence; other owners may supply the corresponding constructions.

PUBLIC_PACKAGE_COMPLETE — logical state RUNNING (gen 2), contract `source_original_arithmetic_input-v1`, source fingerprints as listed in Section 1.
