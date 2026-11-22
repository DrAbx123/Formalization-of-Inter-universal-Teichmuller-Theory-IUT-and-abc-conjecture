# N8 group3 Stage 1 — actual q/theta-pilot → arithmetic tensor region (N5), generator image

- package: N8 group3 (distilled chapter 02); DAG node `n8-group3-q-theta-pilot`.
- node file: `dag/nodes/n8-group3-q-theta-pilot.json`. Entering state: `stage1: open`,
  `semantic_status: paper_objects_not_frozen`, `locked: false`, `lean: {status: stage1_pending}`.
- distilled source (read in full): `logs/coordination/n8-distilled-02-pilot-kummer-realization-20261018.md`,
  212 lines, SHA256 `5146D9E2436FE585B8263CD15EF3E0779D2F9BFAAEE69CF601A0CDD32270B1DE`.
- internal gap note "N5" (read in full): `logs/coordination/n5-source-realization-gap-20261017.md`,
  443 lines, SHA256 `4B6A49F7EBC69EC60399114BE2DEB5FCFA10DED70FF7101B4F88C24188A5ECAA`.
- stage delivered: **1 only**. Production edits: **none**. Lean compilation in this task: **none**.
- hard rule honoured here: no new structure field, no axiom, no weakened quantifier, no renamed card.

N5 is an internal audit label, not a paper label: its §5 status is **OPEN**, and its §4.2 design is exactly the
`ArithmeticThetaPilotBridge` now in production. This record does not change that status.

## 1. Paper objects and exact quantifiers (corpus-verified this session)

Corpus used (local text, not a summary): `papers/motizuki_corpus/text/Inter-universal Teichmuller Theory III.txt`,
11654 lines, SHA256 `876EBC732CAD5DCA89C1446A6055018583512254E3FF5AB333797175EBE9181F`. The positions below were
re-read on 2026-10-22 in this session; the English wording is verbatim from that file.

- `-|log(q)| ∈ R`, the "pilot-object log-volume of the input data" — corpus 10340-10352, 10848-10849,
  10886-10887: "for the procession-normalized mono-analytic log-volume of the image of a q-pilot object
  [cf. Definition 3.8, (i)], relative to the relevant Kummer isomorphisms [cf. Theorem 3.11, (ii)], in the
  multiradial representation of Theorem 3.11, (i)"; "`-|log(q)|` is the log-volume of the region that arises
  from the representation of the q-pilot object at (1,0) on `1,◦U_Q`".
- the theta-pilot output family `n,◦U_{j,vQ}` and `n,◦U_Q` — corpus 10359-10370: "For `n ∈ Z`, write
  `n,◦U := {n,◦U_{j,vQ}}_{j∈|F_l|, vQ∈V_Q}`".
- `-|log(Θ)|`, the (negative) log-volume of `1,◦U` — corpus 10843-10847.
- the output region of possible log-volumes — corpus 10843-10845, 10880-10883:
  `R_{≤-|log(Θ)|} := {λ ∈ R | λ ≤ -|log(Θ)|}`; "the multiradial construction algorithm of Theorem 3.11,
  followed by formation of the holomorphic hull and application of the log-volume, yields a collection of
  possible log-volumes of pilot-object output data `R_{≤-|log(Θ)|}`".
- log-Kummer correspondence in the 1-column, tensor packets of log-shells — corpus 10854-10863.
- final numeric inclusion and `C_Θ ≥ -1` — corpus 10895-10898, 10351-10353: "The inclusion
  `-|log(q)| ∈ R_{≤-|log(Θ)|}`, hence also the inequality `-|log(q)| ≤ -|log(Θ)|` ... then follows formally".
- the (IPL)/(SHE) slots used by that step — corpus 10871-10887.

Exact quantifiers / scope of the group-3 object:

1. Fixed data: a number field `F`, a prime `l ≥ 5` (Lean: `l : PrimeGeFive`, prime and `5 ≤ l.value`,
   `Foundations/Arithmetic/PrimeLabels.lean:14-18`), a nonempty `V^bad`, the input prime-strip (Lean:
   `I : OriginalInput l V`), a place `v : V`, a source-image realization `R : I.SourceImageRealization v`,
   a procession index `n ∈ Z` (Lean: `n : ThetaPilotCarrier l = Fin (lStar l.value + 1)`), a signed label
   `j ∈ |F_l^⋇|` (Lean: `j : SignedLabel l.value`), and the family `vQ ∈ V_Q`. The arithmetic side
   additionally has a prime `p`, an index type `ι` and place/tuple data `places`, `tuple`.
2. The claim is **not** "some real number lies in the region". It is: the *actual* input pilot-object
   log-volume `-|log(q)|` (from the input prime-strip, represented on `1,◦U`) lies in the region produced
   by the algorithm + holomorphic hull + log-volume. Distilled-02 §D states the same requirement: the actual
   `ι_S(x) ∈ R(S)`, not merely a same-typed `x' ∈ R(S)`. A Lean statement whose conclusion only produces some element
   of the region is a different (weaker) proposition.
3. The numeric step `-|log(q)| ≤ -|log(Θ)|` uses `|log(q)| > 0` (corpus 10349-10353). Division by it and the
   `C_Θ` bookkeeping belong to the hull/degree group (group 6), not to this group. Group 3 owes the *object*:
   the q/theta-pilot realization and the generator landing.
4. Nothing in the corpus passage assumes degree faithfulness; `hdeg` is a formalisation-side hypothesis
   (see §5 G3.3) and must never be installed as a source hypothesis of the paper's claim.

## 2. Distilled-02 §A four layers, and where Lean actually sits

Distilled-02 §A warns that four different facts are routinely conflated: element/source → Kummer class →
multiplicative quotient/unit orbit → valuation/norm. The tree has declarations at every layer, but **no
declaration connects the arithmetic tensor carrier to any of them**:

- layer 1, element and its source: `OriginalInput.theaterAt`, `FiniteThetaPacket` (`q`, `scale`,
  `scale_eq`), `thetaValueAt`, `sourceThetaPilotPoint`, `ThetaPilotObject.generator`.
- layer 2, Kummer class: `AbsoluteKummerInjection.absoluteKummerMap` and `absoluteKummerMap_eq_one_iff`
  (kernel = n-th powers), `KummerGaloisClass.kummerRatioHom`, `KummerClass.kummerClass`, `rootSystemDiff`.
- layer 3, quotient / unit orbit: `ThetaPilotObject.possibleImage` (splitting-monoid orbit),
  `LGPMonoidAction`, `sourceScalingUnits`, `holomorphicHull`.
- layer 4, valuation / norm: `FinitePlaceQCandidate.exponent`, `localSignedLog`, `localLogMagnitude`,
  `sourceLocalLogDegree`, `absoluteDegreeNormalizedLowerSignedLog`, `arithmeticTupleHullUnitLogVolume`.

The exact group-3 gap is a missing arrow from layer 1/2 into layer 3 **on the arithmetic side**: the arithmetic
tensor block has layer-4 numerics (Haar log-volumes of sets) and a field-product decomposition, but no
element-level value map, no Kummer class and no orbit. Conversely the source side has layers 1-3, but its "q" is
a real number, not a p-adic element (§5 G3.5).

## 3. Current Lean interfaces (exact declarations)

### 3.1 Arithmetic tensor side

- `ArithmeticTensorTupleBlock` — `ABCBridge/Geometry/FinitePlaceArithmeticTensorBlocks.lean:26-27`:
  `abbrev ArithmeticTensorTupleBlock (tuple : (i : ι) → V i) := FinitePadicTensor (p := p) (fun i => CommonPrimeCompletion (places i (tuple i)))`,
  with `CommonPrimeCompletion place := NormalizedCompletion place.val` (`ABCBridge/Geometry/FinitePlaceCommonPrimeCompletion.lean:20`)
  and `FinitePadicTensor M := ⨂[ℚ_[p]] i, M i` (`Foundations/LocalFields/FinitePadicTensorTopology.lean:29`). It is an actual
  finite-dimensional `ℚ_[p]`-algebra of completed local fields; its unit group is the group the bridge uses.
- regions: `arithmeticTensorTupleLogRegion` (`:60-62`), `isCompact_arithmeticTensorTupleLogRegion` (`:65-67`),
  `one_mem_arithmeticTensorTupleLogRegion` (`:70-72`), `arithmeticTensorTupleProjection_image_logRegion` (`:74-94`,
  exact image of the ambient log region under the tuple projection); ambient version
  `arithmeticTensorLogRegion` (`ABCBridge/Geometry/FinitePlaceArithmeticIQTensor.lean:32-34`).
- canonical regions: `arithmeticTupleCanonicalHull` (`ABCBridge/Geometry/FinitePlaceArithmeticTupleCanonicalHull.lean:64`),
  `arithmeticTupleCanonicalUnitReference` (`:66`), `arithmeticTupleCanonicalHull_eq` (`:68-74`),
  `isCompact_arithmeticTupleCanonicalRegions` (`:89-102`), `measure_arithmeticTupleCanonicalRegions_pos_lt_top` (`:107-122`),
  `arithmeticTupleCanonicalRegions_relativeLogVolume` (`:124-141`).
- decomposition: `exists_arithmeticTensorTuple_fieldProduct` (`ABCBridge/Geometry/FinitePlaceArithmeticTensorBlockFields.lean:25-36`):
  there are `J`, `E : J → Type` and a `ℚ_[p]`-algebra equivalence `e : A ≃ₐ (j : J) → E j` to finite-dimensional
  complete ultrametric normed fields, continuous both ways. **No unit-group comparison and no map to any value
  monoid is declared.**

### 3.2 Arithmetic q-pilot side

There is **no declaration named `ArithmeticQPilot`** anywhere in the tree (every occurrence is followed by
`LogVolume`, `BaseChange` or `GlobalNormalization`). The q-pilot interface is the three namespaces:

- `ArithmeticQPilotLogVolume` (`IUTIII/Corollary312/ArithmeticQPilotLogVolume.lean`):
  `localSignedLog parameter = Real.log ‖parameter.q‖` (`:35-36`), `localLogMagnitude parameter = -localSignedLog parameter`
  (`:39-40`), with positivity and norm lemmas. Its input `FinitePlaceQCandidate`
  (`Foundations/NumberField/LocalQParameter.lean:39-43`) is exactly
  `{q : Completion place, q_ne_zero : q ≠ 0, valuation_lt_one : (Valued.v q) < 1}`; the module header (`:5-16`)
  states it is *not* a Tate parameter and that Tate uniformization is absent from Mathlib 4.32.2.
- `ArithmeticQPilotBaseChange`: `residueNormBase place = Ideal.absNorm place.maximalIdeal.asIdeal` (`:32-33`)
  and `qNorm_eq_residueNormBase_zpow` (`:47-54`), i.e. the norm formula uses the actual residue norm.
- `ArithmeticQPilotGlobalNormalization`: for `selectedLowerPlaces : Finset (NumberField.FinitePlace k)` and
  `parameters : (lowerPlace : selectedLowerPlaces) → FinitePlaceQCandidate lowerPlace.val`,
  `absoluteDegreeNormalizedLowerSignedLog selectedLowerPlaces parameters = selectedLowerSignedLog selectedLowerPlaces parameters / (Module.finrank ℚ k : ℝ)`
  (`:419-422`), with `absoluteDegreeNormalizedSignedLog_invariant` (`:446-452`) and
  `normalizedLowerSignedLog_neg` (`:454-461`, needs `selectedLowerPlaces.Nonempty`).

### 3.3 Source q/theta side

There is **no declaration named `SourceQTheta`** anywhere in the tree (whole-repo grep: 0 occurrences,
including `logs/` and `coord/`). The actual interfaces are:

- q: `FiniteThetaPacket l = {q : ℝ, q_pos : 0 < q, scale : SignedLabel l.value → ℝ, scale_eq : ∀ j, scale j = realThetaValue q j.1}`
  (`IUTII/Theta/FiniteThetaPacket.lean:26-30`), with
  `log_scale : Real.log (scale j) = (gaussExponent j.1).toNat * Real.log q` (`:56-59`), `ofQ` and `logVolume`.
  So **the source q is a real number**, not a p-adic element.
- procession/links: `I.linkAt_q` (`Theorem311/SourceOriginalInput.lean:129-132`) and `I.linkAt_scale`
  (`:134-137`) identify `q` and every `scale j` across the whole `n`-procession. These are the only
  written justification for procession-independence of the theta values.
- carrier: `I.ThetaPilotCarrier l = Fin (lStar l.value + 1)` (`Corollary312/StepXI/HolomorphicHull/SourceImageHull.lean:64-65`);
  `I.ThetaPilotPoint v = (ThetaPilotCarrier l × SignedLabel l.value) → (I.primeStripAt 0 0).Mon v` (`:139-140`);
  the only structure used on `Mon v` is `CommMonoid` plus the degree hom `(I.primeStripAt n m).degree v`
  (`:100-101`, `logDegreeAt`).
- realization: `I.SourceImageRealization v = {posRealAction : Multiplicative ℝ →* I.ValueMonoidAt 0 0 v, degree_of_q : ...}`
  (`:161-169`). This is the **only** existing scalar → value-monoid map, and it is a *hypothesis field*, not
  constructed.
- theta points: `I.thetaValueAt n m j = (I.theaterAt n m).thetaPacket.scale j` (`:87-88`);
  `I.thetaImageValue R n j = R.posRealAction (I.thetaValueMonoidElement (n.1 : Int) 0 j)` (`:173-175`);
  `I.sourceThetaPilotPoint v R n j = fun _ => I.thetaImageValue R n j` (`:201-203`) — constant across all
  `(n', j')` components, i.e. a diagonal value point; `I.possibleThetaPilotImageSet v R n = {x | ∃ j, x = I.sourceThetaPilotPoint v R n j}`
  (`:231-233`).
- hull/volume: `holomorphicHull Scaling S` (`:323-326`), `I.sourceHolomorphicHull v R n` (`:404-406`),
  `I.sourceThetaPilotPoint_mem_sourceHolomorphicHull v R n j` (`:490-495`),
  `I.sourceLocalLogDegree v x = ∑ i : SourceVolumeIndex l, I.logDegreeAt 0 0 v (x i)`
  (`SourceImageHullVolume.lean:103-104`), `SourceVolumeIndex l = ThetaPilotCarrier l × SignedLabel l.value`
  (`:72-73`; cardinality `(lStar l.value + 1) * l.value` at `:87-90`), `I.sourceHullVolume` (`:193`),
  `I.sourceHullVolume_lt_top_of_hullBound` (`:292`).
- q-side numeric value: `I.sourceQSideNormalizedValue n j = (Fintype.card (SourceVolumeIndex l) : ℝ) * Real.log (I.thetaValueAt (n.val : Int) 0 j)`
  (`SourceQSideComparison.lean:88-91`), with the four proved routes of that module (`:96-204`).
- generator degree (the only hdeg-free computation, and it is **outside the Project closure**):
  `I.sourceLocalLogDegree_thetaPilotPoint_gauss v R n j = (Fintype.card (SourceVolumeIndex l) : ℝ) * (((gaussExponent j.1).toNat : ℝ) * Real.log ((I.theaterAt 0 0).thetaPacket.q))`
  (`CardHullRealGeneratorNonpositivity.lean:301-318`), via `I.log_thetaValueAt_eq_gauss` (`:251-258`),
  `I.thetaImageValue_eq_ofAdd_gauss` (`:263-269`) and `I.logDegreeAt_q_pow` (`:284-294`). Note
  `gaussExponent j = j ^ 2` (`Foundations/Theta/GaussianKernel.lean:23`).

### 3.4 The one declaration that connects both sides

`ArithmeticThetaPilotBridge` — `IUTIII/Corollary312/StepXI/HolomorphicHull/SourceArithmeticThetaPilotBridge.lean:86-118`
(195 lines, SHA256 `7B341C3EB6886B56A3F5F1463E932C548B1F234B78F5D95713ABFFAEF9533818`, no `sorry`/`admit`):

~~~lean
structure ArithmeticThetaPilotBridge
    {K : Type uK} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
    {ι : Type vι} [Finite ι] {Va : ι → Type wV}
    (places : (i : ι) → Va i → FinitePlaceAtPrime K p)
    (tuple : (i : ι) → Va i)
    {l : PrimeGeFive} {V : Type uv}
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) where
  toSource : (ArithmeticTensorTupleBlock places tuple)ˣ →* I.ThetaPilotPoint v
  degreeMap : Additive (ArithmeticTensorTupleBlock places tuple)ˣ →+ Real
  degree_compat : ∀ a : (ArithmeticTensorTupleBlock places tuple)ˣ,
    I.sourceLocalLogDegree v (toSource a) = degreeMap (Additive.ofMul a)
  thetaLift : SourceVolumeIndex l → (ArithmeticTensorTupleBlock places tuple)ˣ
  theta_compat : ∀ q : SourceVolumeIndex l,
    toSource (thetaLift q) = I.sourceThetaPilotPoint v R q.1 q.2
  hull_cover :
    (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) ⊆
      toSource '' {a : (ArithmeticTensorTupleBlock places tuple)ˣ |
        (a : ArithmeticTensorTupleBlock places tuple) ∈
          arithmeticTupleCanonicalHull places tuple}
  unit_bound : ∃ C : Real, ∀ a : (ArithmeticTensorTupleBlock places tuple)ˣ,
    (a : ArithmeticTensorTupleBlock places tuple) ∈
      arithmeticTupleCanonicalHull places tuple →
        degreeMap (Additive.ofMul a) ≤ C
~~~

Proved in that module: `sourceHullVolume_lt_top_of_arithmeticThetaPilotBridge` (`:127-142`) and the negative
calibration `no_degreeFaithful_fullHull_arithmeticThetaPilotBridge` (`:151-174`),
`not_nonempty_arithmeticThetaPilotBridge_of_degreeFaithful` (`:179-191`). No bridge is constructed; the module
says so explicitly (`:54-63`).

### 3.5 The one-place reduction (not the paper object, and not imported)

`IUTII/Kummer/SourceThetaPilotIQContainment.lean` (203 lines, SHA256
`683E974AC876E9C5A0756BE2C1386B1D5A54B74B255F4576757CFB0575B1357D`) proves the generic orbit lemma
`possibleImage_subset_of_generator_mem` (`:52-68`) and, on a **one-place** packet over a single source
log-coordinate field `D.K`, the product comparison `sourceThetaPilotProductMap` (`:90-95`), the packet
`sourceThetaPilotIQPacket` (`:119-121`) and `possibleImage_subset_sourceThetaPilotIQPacket` (`:126-137`).
Its boundary note (`:16-28`, `:185-199`) is exact and still true: it does not identify the source value
monoid with `ArithmeticTensorTupleBlock`, and no declaration connects the two carrier types.

## 4. Actual consumer audit (import graph, verified by grep)

In the Project closure:

- `ArithmeticTensorTupleBlock`: `LeanFormal/IUT/Project.lean:403` imports its module; 7 modules import it,
  including `Theorem311/SourceArithmeticPlaceModel.lean:2` and `IUTII/Kummer/SourceUnitLogTensorLanding.lean:1`.
- q-pilot chain (a real consumer): `ArithmeticQPilotLogVolume/BaseChange/GlobalNormalization` at `Project.lean:555-557`.
  The consumer of `absoluteDegreeNormalizedLowerSignedLog` is
  `StepXIContract.ofAbsoluteDegreeNormalizedSignedLog` (`Corollary312/StepXI/ContractSourceReduction.lean:259-288`),
  whose `qSigned` field *is* that value (`:273-275`), lifted to
  `SourceSHELandingSlotAssembly.ofAbsoluteDegreeNormalizedSignedLog`
  (`Theorem311/SourceArithmeticHolomorphicLanding.lean:395-414`) and consumed by `StepXI/APT.lean:3`
  (Project:333). Crucially the comparison to the theta side is a *caller hypothesis*
  `q_le_target : absoluteDegreeNormalizedLowerSignedLog ... ≤ targetSigned` (`:266-268`) together with
  `target_le_theta : targetSigned ≤ thetaSigned`. So even the q-side consumer requires the missing comparison as input.
- theta-side value layer: `SourceQSideComparison` at `Project.lean:415` (also imported by
  `CertificateHullWiringSigned.lean:3`); `SourceImageHull`/`SourceImageHullVolume` are in the closure through these and
  through the bridge module.
- the bridge: `SourceArithmeticThetaPilotBridge` at `Project.lean:419`. It has **no theorem-level consumer outside its
  own file**: grep for `ArithmeticThetaPilotBridge` returns only Project.lean:419 and that file, and
  `sourceHullVolume_lt_top_of_arithmeticThetaPilotBridge` is used nowhere else. So the bridge consumes both sides,
  but its own consumer is only the build closure. This is exactly the DAG node's
  "consumer_identified_not_verified" state.

Outside the closure (orphans; "not in the import closure" is not a claim of mathematical uselessness, per
SHEAF §3):

- `SourceThetaPilotIQContainment`: 0 importers.
- `Theorem311/SourceArithmeticPlaceModel` (129 lines, SHA256 `23CCF14AB5C2D77D4E516F90885C30B620B145E71DCA6FE9B78B8E3EBAEB6172`):
  0 importers, although it is the only declaration pairing the actual `places`/`tuple` block with source data
  (`selection : ι → I.initial.selectedPlaces`, `qParameter : (i : M.ι) → FinitePlaceQCandidate (M.places i (M.tuple i)).val`,
  `block` — `:55-93`). Its own handoff (`:27-33`) names this alignment as still missing: "construct the
  source/arithmetic comparison from the actual Tate q data (B1/B7/B8) to `FinitePlaceQCandidate`, including the
  `ord(q)`/`thetaPacket.q`/scale compatibility needed for the pilot region".
- `Theorem311/SourceK1K2ActualTuplePacket` (546 lines, SHA256
  `A7937558D69E75C3FB3F2023C668715D4A2555D0786FD9A2B756B80212D9849C`): 0 importers. Its "missing source bridge card"
  (`:480-508`) lists the same missing maps (including `φ : ArithmeticTensorTupleBlock places tuple → I.ThetaPilotPoint v`
  and the remark that `σ : Nat → ThetaPilotCarrier l` cannot be injective). A research note, not a proof dependency.
- `CardHullRealGeneratorNonpositivity` (544 lines, SHA256
  `0C153C1F4882E2E18AE1C9FC09F6428EE0D5D2AC3B7C57B8654419CC15B6DF0C`): its only importer is
  `CardHullRealHaarDilationDocking.lean`, which has 0 importers. Hence its hdeg-free generator-degree identity is
  **outside** the Project closure, while the in-closure `I.sourceLocalLogDegree_constant`
  (`SourceImageHullVolume.lean:137-147`) needs `hdeg`.

## 5. Exact gaps

**G3.1 (the hard gap) — no comparison map at all.** The two carriers have incompatible scalar types:
`(ArithmeticTensorTupleBlock places tuple)ˣ` is the unit group of a finite-dimensional `ℚ_[p]`-algebra, whereas
`I.ThetaPilotPoint v` is an `N`-fold product, with `N = (lStar l.value + 1) * l.value ≥ 15` for `l ≥ 5`, of a
commutative value monoid. The tree has (i) no map from the algebra or its units to any value monoid, (ii) no
valuation/norm map on `A` as a whole (only the per-tuple field-product equivalence `e`, and Haar log-volumes of
*sets*), (iii) no declaration turning `e` into a unit-group equivalence
`Aˣ ≃* (j : J) → (E j)ˣ`. A map `Aˣ →* I.ThetaPilotPoint v` therefore cannot be assembled from current
declarations; it has to be constructed from source data (Kummer class / prime-strip). This is exactly N5 §4.1's
PARK reason and distilled-02 §J's "首要未证源命题".

**G3.2 (N versus 1) — the degree square forces an N-fold multiplicity.** `I.sourceLocalLogDegree` is a sum over
`N` components (`SourceImageHullVolume.lean:103-104`), so any bridge field `degree_compat` forces
`degreeMap (Additive.ofMul a) = N * (per-component degree)`. The arithmetic side has no canonical `N`-fold
diagonal: a single real attached to a unit `a` (e.g. a sum of `Real.log ‖e a j‖` over `j : J`) is indexed by `J`, and
**no declaration relates that cardinality to `N`**. The index comparison is a genuine missing definition, not a
bookkeeping choice (N5 §3.2 records the same obstruction).

**G3.3 (proved obstruction) — the full-hull, degree-faithful bridge is impossible.** For
`hdeg : ∀ b, I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b`,
`not_nonempty_arithmeticThetaPilotBridge_of_degreeFaithful hdeg : ¬ Nonempty (ArithmeticThetaPilotBridge ...)`
(`SourceArithmeticThetaPilotBridge.lean:179-191`), from F2
`I.sourceHolomorphicHull_logDegree_unbounded` (`SourceImageHullVolume.lean:379-410`). Consequences that stage 2
must respect: (a) no stage-2 statement may assert the full-hull cover unconditionally under `hdeg`; (b) a
genuine construction must be non-degree-faithful or change the carrier with a proved equivalence; (c) the
*generator-level* statements in §7-§8 are untouched, because F2 is produced by the all-nonzero scalings
`sourceScalingUnits`, not by the generator.

**G3.4 (quantifier mismatch inside the existing bridge) — the lift is indexed by all processions, the cover by
one.** `thetaLift : SourceVolumeIndex l → Aˣ` has domain `ThetaPilotCarrier l × SignedLabel l.value`, but
`hull_cover` covers `I.sourceHolomorphicHull v R n` for the *single* `n` fixed by the structure. Hence "the
generator lands in the arithmetic region" is derivable at `(n, j)` only. For `q.1 ≠ n` one needs the corollary
`I.sourceThetaPilotPoint v R q.1 q.2 = I.sourceThetaPilotPoint v R n q.2`; it follows from `I.linkAt_scale` and
`FiniteThetaPacket.log_scale` but is only written (off-closure) as `I.thetaImageValue_eq_ofAdd_gauss`. No
in-closure statement of procession-independence exists.

**G3.5 (q-side object mismatch) — the two q's do not share a type.** The source q is
`(I.theaterAt 0 0).thetaPacket.q : ℝ`; the arithmetic q is `parameter.q : Completion place`. No declaration
identifies them. The only typeable comparison is `Real.log ((I.theaterAt 0 0).thetaPacket.q)` versus
`localSignedLog parameter = Real.log ‖parameter.q‖`. `TateQPilotJComparison` gives only the model-level
`qPilotLogVolume l = -Real.log ‖q l‖ = Real.log l` (`:45-73`) with no consumer into
`SourceArithmeticPlaceModel`. Moreover `SourceArithmeticPlaceModel.selection : ι → I.initial.selectedPlaces`
records a source index per tensor factor but asserts no equality between `places` and the source-selected places
(the source place type is opaque; `SourceArithmeticPlaceModel.lean:45-54`). So even "the q-pilot's places are the
tensor factors' places" is unproved.

**G3.6 (Kummer layer) — donors exist, no bridge to the carriers.** `absoluteKummerMap hμ : Kˣ →* Hom(Gal(K̄/K), μ_n)`
with `absoluteKummerMap_eq_one_iff : absoluteKummerMap hμ a = 1 ↔ ∃ b, b ^ n = a`
(`AbsoluteKummerInjection.lean:70-105`, `:119-121`) matches distilled-02 §B4-B5. But nothing feeds it into
`ArithmeticTensorTupleBlock` or `I.ThetaPilotPoint v`: the Kummer layer stops at the abstract Galois side.

**G3.7 (a reduction, not the paper object).** `SourceThetaPilotIQContainment` proves orbit containment for a
one-place packet over a single `Rat`-vector space `D.K`. Distilled-02 §E warns that re-proving generic orbit
containment is not progress; the module is a shape donor only and is outside the build closure.

## 6. Existing Lean donors (file:line, exact role)

Donors S1/S1'/S1''/S1''' may use. **Bold** = outside the Project import closure.

- `ArithmeticTensorTupleBlock` — `ABCBridge/Geometry/FinitePlaceArithmeticTensorBlocks.lean:26-27` — the
  arithmetic carrier and its unit group.
- `arithmeticTensorTupleLogRegion` — `:60-62` — compact tensor log region (contains `1`).
- `arithmeticTensorTupleProjection_image_logRegion` — `:74-94` — exact region image under the tuple projection.
- `arithmeticTupleCanonicalHull` — `ABCBridge/Geometry/FinitePlaceArithmeticTupleCanonicalHull.lean:64` — the
  decomposition-independent hull (target region of S1); `arithmeticTupleCanonicalHull_eq` — `:68-74`.
- `exists_arithmeticTensorTuple_fieldProduct` — `ABCBridge/Geometry/FinitePlaceArithmeticTensorBlockFields.lean:25-36`
  — `A ≃ₐ (j : J) → E j`, continuous both ways.
- `ArithmeticThetaPilotBridge` — `StepXI/HolomorphicHull/SourceArithmeticThetaPilotBridge.lean:86-118` — the
  comparison data (hypothesis of S1/S1'').
- `sourceHullVolume_lt_top_of_arithmeticThetaPilotBridge` — `:127-142` — uses `degree_compat`, `hull_cover`,
  `unit_bound`.
- `no_degreeFaithful_fullHull_arithmeticThetaPilotBridge` — `:151-174` — F2 no-go (G3.3).
- `not_nonempty_arithmeticThetaPilotBridge_of_degreeFaithful` — `:179-191` — no bridge in the `hdeg` regime.
- `I.sourceThetaPilotPoint_mem_sourceHolomorphicHull` — `SourceImageHull.lean:490-495` — generator membership
  in the source hull (key step of S1).
- `I.sourceThetaPilotPoint_mem` — `:241` — membership in the possible-image set.
- `I.sourceThetaPilotPoint_apply` — `:205-209` — component computation.
- `I.sourceLocalLogDegree` — `SourceImageHullVolume.lean:103-104` — the `N`-fold sum over
  `SourceVolumeIndex l`; `SourceVolumeIndex` — `:72-73`; cardinality — `:87-90`.
- `I.sourceQSideNormalizedValue` — `SourceQSideComparison.lean:88-91` — the q-side normalized theta log-volume.
- **`I.sourceLocalLogDegree_thetaPilotPoint_gauss`** — `CardHullRealGeneratorNonpositivity.lean:301-318` —
  hdeg-free generator degree.
- **`I.log_thetaValueAt_eq_gauss`** — `:251-258` — `Real.log (thetaValueAt n 0 j) = gauss * Real.log q_0`.
- **`I.thetaImageValue_eq_ofAdd_gauss`** — `:263-269` — procession-independent value of the theta image.
- **`I.logDegreeAt_q_pow`** — `:284-294` — `k * Real.log q_0` via `degree_of_q`.
- `FinitePlaceQCandidate` — `Foundations/NumberField/LocalQParameter.lean:39-43`; `FinitePlaceQCandidate.exponent_pos`
  — `:71-78`.
- `localSignedLog` / `localLogMagnitude` — `ArithmeticQPilotLogVolume.lean:35-36` / `:39-40`.
- `absoluteDegreeNormalizedLowerSignedLog` — `ArithmeticQPilotGlobalNormalization.lean:419-422`;
  `normalizedLowerSignedLog_neg` — `:454-461`.
- `StepXIContract.ofAbsoluteDegreeNormalizedSignedLog` — `ContractSourceReduction.lean:259-288` — actual consumer
  of the q-pilot value.
- `FiniteThetaPacket` / `FiniteThetaPacket.log_scale` — `IUTII/Theta/FiniteThetaPacket.lean:26-30` /
  `:56-59` — the source real q and its Gaussian scale.
- `I.linkAt_q` / `I.linkAt_scale` — `SourceOriginalInput.lean:129-132` / `:134-137` — procession-independence
  of the source q/scale.
- `possibleImage_subset_of_generator_mem` — `IUTII/Kummer/SourceThetaPilotIQContainment.lean:52-68` — orbit
  containment shape (one-place).
- `absoluteKummerMap` / `absoluteKummerMap_eq_one_iff` — `IUTII/Kummer/AbsoluteKummerInjection.lean:70-105` /
  `:119-121` — Kummer injection, kernel = n-th powers.
- `KummerGaloisClass.kummerRatioHom` — `KummerGaloisClass.lean:146` — the root-ratio cocycle hom.
- `KummerClass.kummerClass` / `.kummerClass_mul` / `rootSystemDiff` — `IUTII/Kummer/KummerClass.lean:62` /
  `:88` / `:106` — class map, multiplicativity, root-change difference.

## 7. The smallest stage-2 statement (precise type)

Chosen minimal statement **S1** — generator landing in the canonical arithmetic region. It is the exact
"the actual generator lies in R(S)" step of distilled-02 §D in the only direction the current data allow (source
generator → arithmetic preimage), at the only procession for which the existing bridge has a cover.

Target file (stage 2): `tmp/sheaf/n8/group3-S1.lean`, namespace `LeanFormal.IUT.N8Group3`, importing
`LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceArithmeticThetaPilotBridge`.

~~~lean
theorem ArithmeticThetaPilotBridge.thetaLift_mem_canonicalHull
    {K : Type uK} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
    {ι : Type vι} [Finite ι] {Va : ι → Type wV}
    {places : (i : ι) → Va i → FinitePlaceAtPrime K p}
    {tuple : (i : ι) → Va i}
    {l : PrimeGeFive} {V : Type uv}
    {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
    {v : V} {R : I.SourceImageRealization v} {n : ThetaPilotCarrier l}
    (B : ArithmeticThetaPilotBridge places tuple I v R n)
    (hinj : Function.Injective B.toSource)
    (j : SignedLabel l.value) :
    (B.thetaLift (n, j) : ArithmeticTensorTupleBlock places tuple) ∈
      arithmeticTupleCanonicalHull places tuple
~~~

Complete natural-language proof (every step uses a donor from §6):

1. By `I.sourceThetaPilotPoint_mem_sourceHolomorphicHull v R n j`,
   `I.sourceThetaPilotPoint v R n j` lies in `(I.sourceHolomorphicHull v R n : Set _)`.
2. Apply the bridge field `B.hull_cover` to that membership: get `a : Aˣ` with
   `hA : (a : A) ∈ arithmeticTupleCanonicalHull places tuple` and
   `hax : B.toSource a = I.sourceThetaPilotPoint v R n j`.
3. By `B.theta_compat (n, j)`, `B.toSource (B.thetaLift (n, j)) = I.sourceThetaPilotPoint v R n j`; combined
   with `hax` this gives `B.toSource (B.thetaLift (n, j)) = B.toSource a`.
4. Injectivity `hinj` gives `B.thetaLift (n, j) = a`.
5. Rewrite; the goal becomes exactly `hA`.

Why this is the smallest genuine statement, and what it does not do:

- It is not a bridge field: neither the membership nor injectivity is assumed by the structure, so the conclusion
  is derived from `hull_cover` and `theta_compat` and is a real obligation for any future construction.
- It is the *generator-level* form, hence untouched by the F2 no-go (G3.3), which concerns the full hull.
- All of its proof dependencies (§6) are inside the Project import closure (`SourceImageHull`,
  `FinitePlaceArithmeticTensorBlocks`, `FinitePlaceArithmeticTupleCanonicalHull`, the bridge module), so a
  stage-3 check can run against the standard target without depending on an orphan module.
- Injectivity is not an arbitrary strengthening: distilled-02 §B5 proves the Kummer-class map is injective on
  `Kˣ / (Kˣ)^n`, and the donor `absoluteKummerMap_eq_one_iff` formalises it; any comparison factoring through
  the Kummer class is injective on units. If the eventual comparison is orbit-valued instead, the correct
  replacement is the degree law S1'' plus a quotient form — a *different* node, not this one.
- It does not construct `toSource`, `degreeMap` or `thetaLift`; it does not close G3.1; it does not identify
  the source value monoid with the arithmetic block; it does not touch the q-side (G3.5).

The type is not yet compiled. Acceptance labels for the stage-2 round, to be filled from the actual run:
`statement_compiles` = not run; `proof_body_checked` = not run; `kernel_closed` = not run;
`target_accepted` = not run.

## 8. Follow-on statements (registered here, not stage 2 of this task)

**S1' (unconditional q ↔ theta identity).** Identifies the two independently proved
numeric paths (the q-side value and the generator's realized degree), which no declaration currently relates.
Declared in namespace `Theorem311Source.OriginalInput` next to `sourceLocalLogDegree_thetaPilotPoint_gauss`:

~~~lean
theorem sourceLocalLogDegree_thetaPilotPoint_eq_sourceQSideNormalizedValue
    {l : PrimeGeFive} {V : Type uv}
    {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (j : SignedLabel l.value) :
    I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n j) =
      I.sourceQSideNormalizedValue n j
~~~

Proof route: both sides equal
`(Fintype.card (SourceVolumeIndex l) : ℝ) * (((gaussExponent j.1).toNat : ℝ) * Real.log ((I.theaterAt 0 0).thetaPacket.q))`,
the left by `I.sourceLocalLogDegree_thetaPilotPoint_gauss`, the right by unfolding
`I.sourceQSideNormalizedValue` and applying `I.log_thetaValueAt_eq_gauss` (minor `Fin.val` cast
normalization). This proof depends on the **off-closure** `CardHullRealGeneratorNonpositivity`; if that dependency
is to be avoided, S1' must carry its own copy of `I.log_thetaValueAt_eq_gauss` (a proof, not a hypothesis).

**S1'' (bridge-level generator degree law; uses S1').**

~~~lean
theorem ArithmeticThetaPilotBridge.degreeMap_thetaLift_eq_sourceQSide
    {K : Type uK} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
    {ι : Type vι} [Finite ι] {Va : ι → Type wV}
    {places : (i : ι) → Va i → FinitePlaceAtPrime K p}
    {tuple : (i : ι) → Va i}
    {l : PrimeGeFive} {V : Type uv}
    {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
    {v : V} {R : I.SourceImageRealization v} {n : ThetaPilotCarrier l}
    (B : ArithmeticThetaPilotBridge places tuple I v R n)
    (q : SourceVolumeIndex l) :
    B.degreeMap (Additive.ofMul (B.thetaLift q)) = I.sourceQSideNormalizedValue q.1 q.2
~~~

Proof route: `rw [← B.degree_compat (B.thetaLift q), B.theta_compat q]`, then S1'. This is the exact law
"arithmetic degree of the theta-pilot generator = procession-normalized theta log-volume" that any future
`toSource`/`degreeMap`/`thetaLift` must satisfy: the one-point form of the paper's `-|log(q)|` versus
`-|log(Θ)|` identification.

**S1''' (procession independence; closes G3.4).**

~~~lean
theorem sourceThetaPilotPoint_eq_of_procession
    (v : V) (R : I.SourceImageRealization v)
    (n n' : ThetaPilotCarrier l) (j : SignedLabel l.value) :
    I.sourceThetaPilotPoint v R n j = I.sourceThetaPilotPoint v R n' j
~~~

Proof route: `funext p`; both components are `I.thetaImageValue`, then `I.thetaImageValue_eq_ofAdd_gauss` twice
(off-closure donor). With S1''', S1 extends from `(n, j)` to every `q : SourceVolumeIndex l`.

**Registered but not stage-2-ready (G3.1, G3.5): construction of the comparison data.** The exact shape that
would close G3.1 is the bridge data *without* `hull_cover`/`unit_bound`, with all five data fields constructed
rather than postulated: `toSource : Aˣ →* I.ThetaPilotPoint v`, `degreeMap : Additive Aˣ →+ ℝ`, the degree
square, `thetaLift : SourceVolumeIndex l → Aˣ`, the theta square. Constructing them requires (i) the index
comparison between the tensor decomposition index `J`/`places`/`tuple` and the source data
(`ι → I.initial.selectedPlaces` currently exists only as data), (ii) a Kummer-class input (G3.6), and (iii) the
q-object identification (G3.5). This record registers the requirement; it does not propose a free field for it.

## 9. Node-local stage record (fractal stages)

    node: n8-group3-q-theta-pilot
    stage1: open/partial — paper objects and quantifiers fixed (§1); exact Lean interfaces fixed (§3); consumer
            audit done (§4); gaps enumerated (§5); minimal stage-2 statement fixed (§7). Still open at stage 1:
            the construction of the comparison data (G3.1) has no in-tree proof route; the index comparison
            (G3.2) and the q-object identification (G3.5) are undefined objects, not lemmas.
    stage2: not started. Planned file tmp/sheaf/n8/group3-S1.lean, declaration
            ArithmeticThetaPilotBridge.thetaLift_mem_canonicalHull; named sorry allowed; statement_compiles
            not run.
    stage3: open. No proof attempt was made in this task (stage-1 only), so proof_body_checked and kernel_closed
            are not claimed; the proof route in §7 is a plan, not evidence.
    children: G3.a = S1 (stage 2 next); G3.b = S1' + S1'' (q<->theta numeric identity); G3.c = S1''' (procession
            independence); G3.d = q-object identification (G3.5, stage 1; no statement yet because the two q's do
            not share a type); G3.e = Kummer-to-carrier bridge (G3.6, stage 1).
    ready_action: stage 2 writes tmp/sheaf/n8/group3-S1.lean with S1 as stated, compiles it with the SETUP
            statement-stage command, and records statement_compiles; no production edit.

## 10. Evidence boundary

- No production file was edited by this task; the only file written is this record.
- No Lean file was compiled in this task. `statement_compiles`, `proof_body_checked`, `kernel_closed` and
  `target_accepted` are all **not run** for S1/S1'/S1''/S1'''; the proof routes are plans.
- The corpus positions in §1 were read directly in
  `papers/motizuki_corpus/text/Inter-universal Teichmuller Theory III.txt`; they are paper text, not a summary. The
  Chinese quotation from distilled-02 is verbatim.
- Consumer statuses in §4 come from grep over the repository (import lines and declaration uses), not from a build.
  "In closure" means reachable from `LeanFormal/IUT/Project.lean` by import; it is not a compile claim, and
  "outside the closure" is not a claim of mathematical uselessness (SHEAF §3).
- The n5 and distilled-02 documents are research/audit notes, not proof evidence; their proved claims were
  re-checked against the Lean declarations cited here, and their unproved parts are labelled as gaps.

---

## 11. Addendum: independent stage-1 read (S1d, 2026-10-22)

This section was appended by an independent stage-1 reader after the main body existed. It does not replace the
main body and does not change its S1. It records three checks not present above; no production edit, no Lean
compilation.

### A1. New obstruction: `SourceImageRealization` is not instantiable at the concrete q = 1/5 source theater

The only declared scalar -> value-monoid map is `SourceImageRealization.posRealAction : Multiplicative Real ->*
I.ValueMonoidAt 0 0 v` plus the single `degree_of_q` equation (`SourceImageHull.lean:161-169`).

The concrete source theater has `primeStrip = finiteLocalIntegralFPrimeStrip 2 7`
(`Example36SourceTheaterCarrier.lean:156-161`), hence `ValueMonoidAt 0 0 v = LocalIntegralMonoid v.1`
(`LocalIntegralFPrimeStrip.lean:57-75`, `LocalIntegralMonoid.lean:32-34`), and its q is the real
`gaussianFiveThetaQ = 1/5` (`Example36SourceTheaterCarrier.lean:170-186`).

A monoid hom from `Multiplicative Real` restricts to a group hom on the subgroup `Real_{>0}` of positive
reals (units in the source), so its image on that subgroup lies in the target's unit group. The group
`Real_{>0}` is divisible. The units of `LocalIntegralMonoid` are the norm-one units of
`(AlgebraicClosure Q_p)^×`; modulo torsion they are `1 + p Z_p`, a torsion-free `Z_p`-module, hence have
no nontrivial divisible subgroup. So the `Real_{>0}`-image is torsion, has degree 0, and `degree_of_q`
forces `log q = 0`, i.e. `q = 1`, contradicting `q = 1/5`.

Status: mathematical obstruction, **not Lean-proved here**. Missing lemmas: (i) unit group of
`LocalIntegralMonoid p` = norm-one units; (ii) its divisible elements are torsion; (iii) the groupification
identification `LocalIntegralMonoid.lean:220-226`.

Consequences:

* this is a second, independent reason (besides F2) why no *unconditional* N5 bridge exists: the concrete source
  theater supplies no `R`;
* S1/S1'/S1'' above are correctly conditional; they must not be read as instantiated on the concrete theater;
* the only inhabited value model is degenerate (`SourceUnitRegionHaarDataActual.lean:11-24, 43-82, 138-140`
  uses the nonpositive reals and `q = 1`);
* the actual q enters a tensor only through its element, not through `Multiplicative Real ->* Mon v`.

### A2. Consumer grep counts (confirmations and the assembly check)

Whole-repo grep on the current snapshot:

* `SourceK1K2ActualTuplePacket`: 0 importers (name absent from all .lean contents and from `Project.lean`).
* `SourceThetaPilotIQContainment`: 0 importers.
* `SourceUnitLogTensorLanding`: 0 importers.
* `SourceArithmeticThetaPilotBridge`: `Project.lean:419` plus 6 self-references; no theorem consumer.
* `SourceTheorem311Assembly`: 0 occurrences of `pilot` / `ThetaPilot` / `thetaPilot` /
  `ArithmeticTensor` / `ArithmeticQPilot` / `SourceQTheta`; 20 occurrences of `labelledKummer`.
* `ArithmeticQPilotGlobalNormalization`: 0 occurrences of `Source` / `Theta` / `OriginalInput` /
  `SourceImage`.

So the consumer chain is only a type slot: `SourceTheorem311Realization.packet`
(`SourceHodgeTheaterBridge.lean:914`) -> `SourceInternalWiring.k1` (`SourceInternalWiring.lean:389`) ->
`canonicalCompletion` (`SourceTheorem311Assembly.lean:1375`). No existing declaration consumes a
q/theta/arithmetic-tensor value there.

### A3. Closure note for a possible one-place log-region sibling

A bridge-free alternative to S1 is the one-place generator landing in the **actual** region
`arithmeticTensorTupleLogRegion` (with the canonical `Rat -> Q_p` comparison). Its typing needs
`SourceLocalLogShellDatum`, which is reachable only through `SourceLogShellFamilyDependent` and the orphan
`SourceUnitLogTensorLanding`; both are outside `Project.lean`. This alternative is therefore *not* an
in-closure statement, whereas S1's donors are. Do not claim closure for it; register it as a separate child if
the region-level form is wanted.

### A4. Stage-2 decision unchanged

Keep S1 as the stage-2 declaration. Add A1 as a hard boundary to the node. Do not assert existence of
`ArithmeticThetaPilotBridge` and do not present `SourceImageRealization` as the actual source realization
without A1.
