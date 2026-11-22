# AUDIT: hq / hθ / R1 donor wiring (Task G)

Date: 2026-11-15 (Asia/Shanghai). Auditor: abc (teammate).
Mode: **read-only audit; no Lean compilation performed**. Evidence source:
`dag/watchdog/watchdog.log` (current watchdog), `tmp/xif_guarded_results.log`
(guard harness流水), olean/src mtimes, and source reading. Per Lead's rule, green
claims must come from watchdog DONE/FAIL; guarded-result entries are recorded
separately and are **not** current watchdog evidence.

Scope files (read in full):

- `tmp/sheaf/xif/paper/S3133RealifiedQPilotDivisorActual.lean`
- `tmp/sheaf/xif/paper/S3133RealifiedQPilotLogVolumeActual.lean`
- `tmp/sheaf/xif/paper/S3133QPilotReadoutActual.lean`
- `tmp/sheaf/xif/paper/S3133QPilotLogVolumeAgreementActual.lean`
- supporting defs: `QPilotGlobalLogVolumeFromQActual.lean`,
  `QPilotZeroLocusDivisorActual.lean`, `QPilotObjectActual.lean`,
  `Mzk1ActualRamifiedDataActual.lean`, `Mzk1RamifiedPlaceDataActual.lean`,
  `Mzk1BaseChangeQCorrespondenceActual.lean`,
  `Mzk1C3BaseQIdentificationActual.lean`, `Mzk1ActualReadingTargetActual.lean`,
  `S3137QThetaPilotLogVolumeReadingsActual.lean`,
  `PaperLevelXiFTargetActual.lean`, hθ donors below.

---

## 0. Evidence / freshness status of the donors

| file | src mtime | olean mtime | olean≥src | current watchdog.log | guarded results |
|---|---|---|---|---|---|
| S3133RealifiedQPilotDivisorActual | 00:31:03 | 00:33:00 | yes | **no entry** | last EXIT=0, SIZE=5199 **matches current source size 5199**; axiom prints standard |
| S3133RealifiedQPilotLogVolumeActual | 00:38:50 | 00:40:07 | yes | **no entry** | last EXIT=0 SIZE=5939 **matches 5939**; standard |
| S3133QPilotReadoutActual | 00:23:19 | 00:24:47 | yes | **no entry** | last EXIT=0 SIZE=7692 **matches 7692**; standard |
| S3133QPilotLogVolumeAgreementActual | 00:42:03 | 00:43:16 | yes | **no entry** | last EXIT=0 SIZE=6465 **matches 6465**; earlier error lines are superseded |
| QPilotGlobalLogVolumeFromQActual (def site of qVEffectiveMultiplicity) | 2026-10-29 01:06:20 | 2026-10-29 21:37:31 | yes | no entry | historical build; no current evidence |

Status: all four donors are **source-olean fresh**, with guarded EXIT=0 whose recorded
SIZE equals the current source byte size; axiom prints in the guarded log are the
three standard axioms. **No current `watchdog.log` START/DONE/FAIL exists for them.**
Under the strict "watchdog-only" rule they are *unverified by the current watchdog*,
and should be enqueued into `dag/watchdog/extra-targets.txt` in the next build batch
(not done in this read-only audit).

Red/stale items: none in the four donor sources; the only stale/uncertain items are
the missing current-watchdog evidence and the older `QPilotGlobalLogVolumeFromQActual`
build.

---

## 1. Donor theorem inventory and what it can feed

### 1.1 S3133RealifiedQPilotDivisorActual (carrier-level divisor)

| theorem / def | location | content | feeds |
|---|---|---|---|
| `qPilotRealifiedDivisor` | :58-62 | `∏ b, (qVZeroLocusPrimeDivisor X b) ^ (qVEffectiveMultiplicity X b)` | hq's **global q divisor** object |
| `qPilotRealifiedDivisor_factor` | :65-68 | each factor is `globalPrimeDivisor (finite b.1)` (rfl) | identification of support to base bad primes |
| `qPilotRealifiedDivisor_eq_prod_factor` | :72-77 | product over `globalPrimeDivisor` with exponents `qVEffectiveMultiplicity` | **mult_b exponents** on the actual divisor |
| `globalPrimeWeight_finite_eq` | :80-84 | weight(finite b) = `Real.log (residueNormBase b.1)` | per-place log base |
| `globalDegree_primeDivisor_pow` | :88-96 | degree of `P^n` = n·weight | log-volume linearity in mult_b |
| `globalDegree_qPilotRealifiedDivisor` | :100-119 | `globalDegree D_q = ofAdd (Σ_b (mult_b:ℝ)·weight_b)` | **hq RHS**: `-Σ_b mult_b·log(residueNormBase b)` |

### 1.2 S3133RealifiedQPilotLogVolumeActual (carrier-level log-volume)

| theorem / def | location | content | feeds |
|---|---|---|---|
| `qPilotRealifiedLogVolume` | :57-59 | `-(globalDegree D_q).toAdd` | hq `qReading` candidate |
| `effectiveDivisorDegree_qVZeroLocusQEffectiveGlobal_eq_sum` | :63-71 | degree of zero-locus effective divisor = Σ mult_b·log(residueNormBase b) | same as above at presentation level |
| `qPilotRealifiedLogVolume_eq` | :74-83 | **`qPilotRealifiedLogVolume = -Σ_b mult_b·log(residueNormBase b)`** | **exact hq formula** `qReading=-A` with `A=Σ mult_b log(base)` |
| `qPilotRealifiedLogVolume_eq_qPilotQGlobalLogVolume` | :87-95 | = presentation-level `qPilotQGlobalLogVolume` | agreement/transport to R1 reading |
| `qPilotRealifiedLogVolume_eq_neg_sum_localLogMagnitude` | :99-105 | = `-Σ_b localLogMagnitude(qVFamily b)` | hq = `-|log q|`, paper form |
| `qPilotRealifiedLogVolume_eq_sum_localSignedLog` | :109-117 | = `Σ_b localSignedLog(qVFamily b)` | signed readout form (feeds C3 signed aggregation) |
| `realifiedLogVolume_factor_eq` | :121-128 | per-b factor = `-mult_b·log(residueNormBase b)` | per-place chip for the weighted sum |

### 1.3 S3133QPilotReadoutActual (Q_C source readout)

| theorem / def | location | content | feeds |
|---|---|---|---|
| `qPilotSignedReadoutAt` | :68-71 | `localSignedLog ((s3130QCSourceData b h).qV)` | R1 / C3 reading at one bad place |
| `qPilotSignedReadoutAt_eq_qVFamilySignedLog` | :75-78 | = `qVFamilySignedLog X.S b` (rfl) | **same-q identification at readout level** (feeds R1's `hq`) |
| `qPilotSignedReadoutAt_eq_log_qNorm` | :81-85 | = `Real.log ((s3130QCSourceData ...).qNorm)` | C3 source norm reading |
| `qPilotSignedReadoutAt_eq_neg_localLogMagnitude` | :88-94 | = `-localLogMagnitude(qVFamily b)` | hq `-|log q_v|` |
| `qPilotSignedReadoutAt_neg` | :97-102 | < 0 (contracting q) | sign/nonpositivity for R1 |
| `qPilotLogMagnitudeAt_eq_multiplicity_mul_log` | :106-110 | **`localLogMagnitude(qVFamily b) = (mult_b:ℝ)·log(residueNormBase b)`** | **per-place mult_b** exactly what actualFn lacks |
| `qPilotWeightedGlobalReadout` | :114-119 | weighted sum `Σ_b w_b·readout_b` | R1 weighted global form |
| `qPilotWeightedGlobalReadout_one` | :123-132 | unit weights = `qPilotQGlobalLogVolume` | agreement with carrier log-volume |
| `qPilotNormalizedGlobalReadout` | :136-140 | weights = `nativeBadLocalWeight X.S` | hq's procession-normalized sum |
| `qPilotNormalizedGlobalReadout_eq` | :144-157 | **= `nativeQVPilotNormalizedSignedLogVolume X.S`** | **R1 right side** `actualQPilotSignedLogClassical` analog / hq scalar |
| `qPilotNormalizedGlobalReadout_nonpos` | :160-166 | ≤ 0 | nonpositivity |

### 1.4 S3133QPilotLogVolumeAgreementActual (same-input agreement package)

| theorem | location | content | feeds |
|---|---|---|---|
| `qPilotLineBundleObject_sameInput` | :72-78 | line-bundle divisor class = Grothendieck class of q_v zero-locus AND log-volume = -Σ|log q_v| | R1 object identification |
| `realified_presentation_logVolume_agreement` | :82-84 | carrier log-volume = presentation log-volume | transport carrier ↔ presentation |
| `qPilotGlobalLogVolume_eq_neg_classicalLog` | :88-90 | global = -classical log | hq formula cross-check |
| `realified_logVolume_eq_sum_localSignedLog` | :94-98 | = Σ signed q_v logs | signed aggregation donor |
| `qCReadout_eq_signedQVFam` | :102-110 | per-place readout = signed qV and = -|log q_v| | R1/C3 per-place |
| `batchA_QC_eq_normalizedQPilot` | :114-119 | Batch A normalized readout = native normalized scalar | **R1 right side identification** |
| `qPilotLogVolume_sameInput_package` | :125-139 | 4-way package (divisor, carrier, presentation, Batch A) | one-stop donor for hq/R1 |

---

## 2. R1 / hq field wiring (donor → field)

Notation: `mult_b := qVEffectiveMultiplicity X.S b = (qVFamily X.S b).order * localResidueDegree ((nativeBadLift X.S).lift b)`
(def: `QPilotGlobalLogVolumeFromQActual.lean:50-53`).

### 2.1 R1 target fields

| field | location | statement | donor that can fill it | status |
|---|---|---|---|---|
| `QSourceLeQNorm` | `Mzk1ActualReadingTargetActual.lean:85-86` | `qPilotLogVolumeReading P ≤ actualQPilotSignedLogClassical T` | `qPilotLogVolumeReading_le_actualQPilotSignedLogClassical_of_structures` (BaseChangeQ:165-182) with `hq` + `agg` | PROVED conditional; only the **same-q** witness missing |
| `HRootLeHTarget` | ibid :92-93 | `actualThetaHullLogRoot T ≤ thetaPilotHullLogVolumeReal C3` | hθ hull bound (see §4) | hθ side still open |
| `qPilotLogVolumeReading` | `S3137QThetaPilotLogVolumeReadingsActual.lean:77-79` | `= P.signedQPilotLogVolume` | — | definition |
| `P.signedQPilotLogVolume` | `QPilotObjectActual.lean:169-170` | `localSignedLog P.line.C3.q`; `= Real.log ‖P.line.C3.q.q‖` (:180-182) | — | definition: **single local C3 q**, not global family |
| `actualQPilotSignedLogClassical` | `PaperLevelXiFTargetActual.lean:63-64` | `-actualQPilotMagnitudeClassical` | readout donors | definition |
| `actualQPilotMagnitudeClassical` | ibid :57-61 | `Σ_b W_b·(c_norm_b·log qVFamTensorP_b)` | `qVFam` norms (not mult_b) | **no q exponent/multiplicity** in the definition |

### 2.2 hq target fields

| field | location | statement | donor | gap |
|---|---|---|---|---|
| `QPilotC3SignedAggregation.signed_eq_global` | `Mzk1BaseChangeQCorrespondenceActual.lean:155-160` | `P.signedQPilotLogVolume = -nativeGlobalQPilotNormalizedLogMagnitude T` | agreement package + normalized readout | needs same-q identification `C3.q ↔ qVFamily` |
| `BaseChangeQElementCorrespondence.q_eq` | ibid :146-151 | completionMap(qVFamily q) = nativeBaseQFamily q | `ClauseBBaseQSourceIdentity` | missing (c) source identity |
| `C3BaseQElementIdentification.log_relation` | `Mzk1C3BaseQIdentificationActual.lean:59-66` | `log‖C3.q.q‖ = -(baseQLogMagnitude T b)/n` | readout/local norms | per-place same-q; not global mult_b |
| `GlobalSumAggregation.log_eq_sum` | ibid :71-77 | `log‖C3.q.q‖ = -Σ_b W_b·baseQLogMagnitude T b` | readout donors give the **normalized** sum with `nativeBadLocalWeight` | identification `W_b·baseQLogMagnitude = mult_b·log(residueNormBase)` still needed |
| `HthetaLinearForm` | `Mzk1HqHthetaStructuralObstructionActual.lean:7-8` | `thetaSide = Lbar + Dbar - sFactor·A` | hθ hull/covolume | see §4 |

### 2.3 Exact wiring table (donor theorem → field)

1. `qPilotRealifiedLogVolume_eq` (:74-83) → hq formula `qReading = -Σ_b mult_b·log(residueNormBase b)`.
2. `qPilotRealifiedLogVolume_eq_qPilotQGlobalLogVolume` (:87-95) → presentation-level hq reading (`qPilotQGlobalLogVolume`).
3. `qPilotRealifiedLogVolume_eq_neg_sum_localLogMagnitude` (:99-105) → `-|log q|` form used in R1 conclusion.
4. `qPilotRealifiedLogVolume_eq_sum_localSignedLog` (:109-117) → `QPilotC3SignedAggregation` signed side.
5. `qPilotLogMagnitudeAt_eq_multiplicity_mul_log` (Readout:106-110) → per-place **mult_b**; this is the exact donor for the "hq 右端缺 q 重数" gap (currently `actualFn` only gives residue degree).
6. `qPilotNormalizedGlobalReadout_eq` (Readout:144-157) → `nativeQVPilotNormalizedSignedLogVolume` = `actualQPilotSignedLogClassical`-compatible normalized scalar (with `nativeBadLocalWeight` weights).
7. `batchA_QC_eq_normalizedQPilot` (Agreement:114-119) → same identification packaged.
8. `qPilotLogVolume_sameInput_package` (Agreement:125-139) → one-shot donor bundle for `QPilotC3SignedAggregation` + R1.
9. `realifiedLogVolume_factor_eq` (LogVolume:121-128) → per-place `-mult_b·log(residueNormBase b)` chip.

**Missing bridge (the wiring task)**: all donors live on `qVFamily` (global, K-level) while R1/hq left side is the single local `C3.q` (Fmod-level). The single unused identification is
`ClauseBBaseQSourceIdentity` (completionMap(qVFamily q) = nativeBaseQFamily q) **plus** the same-q norm identification `qVFamDefaultNorm T b = ‖(baseQ T b).q‖` (the `hq` hypothesis of `qPilotLogVolumeReading_le_actualQPilotSignedLogClassical_of_structures`). Once these hold, the donor theorem chain 1→4→6→7 fills R1/hq without any new inequality.

---

## 3. Where the current `actualFn` lacks the q multiplicity (exact positions)

File: `tmp/sheaf/xif/paper/Mzk1ActualRamifiedDataActual.lean`.

1. **`actualFn` (:39-52)**: chooses `f` from
   `logShellResidueCard (NormalizedCompletion place.val) = p^f`
   via `Classical.choose (logShellResidueCard_eq_prime_pow ...)`.
   It is **only the residue-degree exponent** of the local residue field; there is
   no `qVFamily.order`, no `qVEffectiveMultiplicity`, no `localResidueDegree`.
2. **`actualFn_spec` (:54-71)**: same content (positivity + residue-card power).
3. **`hdecompOf` (:73-104)**: local index decomposition
   `T·index = residueCard^(eK·sK−1)·(residueCard−1)`; the q vanishing order is not
   an input here.
4. **`actualData` (:134-148)** and **`actualDataCore` (:165-179)**: construct
   `RamifiedPlaceData` with
   `fn := actualFn`, `Fdeg := fun _ => Fdeg`, `aExp := chosenA`, `cCorr := chosenC`,
   `logp := fun i => Real.log p`; **no field carries `mult_b`**.
   The structure `RamifiedPlaceData` (`Mzk1RamifiedPlaceDataActual.lean:17-27`)
   has exactly `fn Fdeg l logp logMu logIdx diff aExp cCorr` — no q-order/
   multiplicity field.
5. **`actual_A_le_Lbar_add_Dbar` (:240-256)**: LHS is
   `(1/(2l))·Σ_i (actualFn i)/Fdeg·log p`;
   it contains **no factor `qVEffectiveMultiplicity i`** and no
   `log(residueNormBase b)`. Consequently it bounds the residue-degree weighted
   index, not the q-pilot weighted log-volume `Σ_b mult_b·log(residueNormBase b)`.
6. `actual_paper312` (:258-269+) inherits the same LHS; same gap.

**Exact missing wire**: replace/augment the per-place RHS with the donor identity
`localLogMagnitude(qVFamily b) = (qVEffectiveMultiplicity X b : ℝ)·log(residueNormBase b)`
(`QPilotGlobalLogVolumeFromQActual.lean:109-122`; per-place version
`S3133QPilotReadoutActual.lean:106-110`). Concretely: add a multiplicity component
to `RamifiedPlaceData` (e.g. `mult : ι → Nat` with `mult i = (qVFamily (places i)).order * localResidueDegree ...`)
and use `qVFamily_localLogMagnitude_eq` to rewrite the per-place bound; then the
right side of `A_le_Lbar_add_Dbar` becomes the paper hq sum.

---

## 4. hθ: one-way full-lattice bound and the unique missing identification

### 4.1 Equality donor (product model)

- `LocalFieldIntegralHullSpan.lean:18-24`: `integralSpan_subset_hull` (always).
- `LocalFieldIntegralHullSpan.lean:26-71`: `hull_subset_integralSpan` under
  `[Finite J]`, compact `S`, `S.Nonempty`, coordinate-nondegenerate.
- `LocalFieldIntegralHullSpan.lean:73-79`: **`integralSpan_eq_hull`** = both inclusions
  → actual integral-ring span = holomorphic hull (product model).
- Tensor instantiations: `FinitePadicTensorLogShellHull.lean:83-91`
  (`integralSpan_tensorLogShellProductImage_eq_hull`);
  `FinitePlaceArithmeticIQHull.lean:55-63`
  (`integralSpan_arithmeticTensorProductImage_eq_hull`).

### 4.2 Covolume file: only the one-way direction is proved

`FinitePlaceIntegralTensorCovolume.lean`:

- :96-123 `arithmeticTupleIntegralLogLattice_subset_canonicalHull`:
  `integralLogLattice ⊆ canonicalHull` (one-way inclusion).
- :143-155 `arithmeticTupleLogTensorUnitLogVolume_le_hull`:
  `arithmeticTupleLogTensorUnitLogVolume ≤ arithmeticTupleHullUnitLogVolume` (one-way
  log-volume inequality).
- :128-141 `arithmeticTupleLogTensorUnitLogVolume_eq_relativeHaarLog` (relative Haar
  log identity), :157-184 `..._eq_fieldLogVolume` (field product formula).
- **No equality** `integralLogLattice = canonicalHull`, and **no covolume equality**
  are stated in this file.

### 4.3 The unique hθ identification still missing

Under the Lead's 2026-11-15 route (one-way sufficient bound; exact integral θ hull
equality no longer required), the **single missing identification** is the
**product-coordinate identification of the theta-pilot hull image**:

> `TensorRegionCoordinateProduct` — the actual theta-pilot region image equals a
> product set over its coordinates, i.e. `regionImage = {x | x 0 ∈ localRegion}`
> in the 1-column/tensor case (obstruction file
> `Mzk1HqHthetaStructuralObstructionActual.lean:12-13`), so that
> `Measure.addHaar` factors and `thetaPilotHullLogVolumeReal` equals the sum of
> local log-volumes; this yields `HthetaLinearForm`
> `thetaSide = Lbar + Dbar - sFactor·A`.

Rationale: the one-way full-lattice volume bound is already green
(`arithmeticTupleLogTensorUnitLogVolume_le_hull`), and the product-model equality
`integralSpan_eq_hull` is green; what is missing to turn the hull volume into the
hθ linear form is precisely the product/coordinate identification (index
`coord/LEAN-INDEX.md` §3 item 3 also says "region product / product Haar /
log=Σlocal 仍缺"). If the exact-equality route is ever re-adopted, the missing
identification would instead be the reverse inclusion
`arithmeticTupleCanonicalHull ⊆ ↑(arithmeticTupleIntegralLogLattice)` (equivalently
covolume equality); it is **not** required by the current one-way route.

---

## 5. `coord/LEAN-INDEX.md` coverage audit

Covered (good):

- `S3133RealifiedQPilotDivisorActual.lean` — LEAN-INDEX:100-103.
- `S3133RealifiedQPilotLogVolumeActual.lean` — :104-105.
- `S3133QPilotReadoutActual.lean` — :106-108.
- `S3133QPilotLogVolumeAgreementActual.lean` — :109-110.
- `qVEffectiveMultiplicity` — mentioned :102.
- `integralSpan_eq_hull` — :156 (with path :155).
- `FinitePlaceIntegralTensorCovolume.lean` — :125-126.
- `Mzk1HqHthetaStructuralObstructionActual.lean` — :74, :131.
- Gap statements :82-83 and wiring requirement :111, :136 match §2/§3 of this audit.

Errors / staleness to fix in the index:

1. **Wrong file attribution for `qVEffectiveMultiplicity`** (LEAN-INDEX:102): it is
   listed under `S3133RealifiedQPilotDivisorActual.lean`, but the defining
   `noncomputable def qVEffectiveMultiplicity` is in
   `tmp/sheaf/xif/paper/QPilotGlobalLogVolumeFromQActual.lean:50-53`; the divisor
   file only **uses** it.
2. **`QPilotGlobalLogVolumeFromQActual.lean` filename missing** from the index,
   although it is the definition site of the key `qVEffectiveMultiplicity` and of
   `qPilotQGlobalLogVolume`.
3. **hθ statement inaccurate** (LEAN-INDEX:84): "LocalFieldProductHull 有
   subset/compactness 但无 equality" is wrong — `integralSpan_eq_hull` (equality) is
   in `LocalFieldIntegralHullSpan.lean:73-79` and the index itself cites it at
   :153-159. The accurate statement is: equality is green in the product model, but
   the **arithmetic-tuple covolume file only proves one-way**; product-coordinate
   identification still missing.
4. **One-way bound not indexed**: `FinitePlaceIntegralTensorCovolume.lean` is listed
   only for `arithmeticTupleLogTensorUnitLogVolume_eq_relativeHaarLog` (:126); the
   key one-way `arithmeticTupleLogTensorUnitLogVolume_le_hull` (:143-155) and
   `arithmeticTupleIntegralLogLattice_subset_canonicalHull` (:96-123) are not.
5. **Stale stage4 status** (LEAN-INDEX:86): "withValMovedSigma_surjective 已绿" is
   true only for an older olean; the current `Mzk1GaloisCompletionActual` source
   (09:49:50) is **red** — latest watchdog **FAIL 01:51:09Z** (after an intermittent
   DONE 01:47:57 for an earlier source; still failing on
   `withValMovedSigma_val_eq`/`valueGroup_comap_eq`). Stage4 is restoring green;
   index should mark current-source red / in-progress.
6. **Evidence policy note**: the four S3133 donors have no current watchdog DONE/FAIL;
   their guarded-log EXIT=0 entries (with SIZE matching current sources) should be
   either re-run through the current watchdog or explicitly annotated in the index as
   "guarded-log only, not current-watchdog".
7. `Mzk1IVThm110TensorUnitBallActual` is listed as placeholder (LEAN-INDEX:75,
   132) — consistent with its current content (missing-donor list only).

---

## 6. Next actions (no compilation in this audit)

1. Enqueue the four S3133 donors + `QPilotGlobalLogVolumeFromQActual` in
   `dag/watchdog/extra-targets.txt`; wait for START/DONE and re-probe the listed
   theorems for current-watchdog axioms.
2. Add the q-multiplicity wire (§3) to the actual ramified data/bound, using
   `qVFamily_localLogMagnitude_eq` / `qPilotLogMagnitudeAt_eq_multiplicity_mul_log`;
   state the new per-place bound with `mult_b·log(residueNormBase b)` on the right.
3. Close R1 via `ClauseBBaseQSourceIdentity` + same-q `hq`; then
   `qPilotLogVolumeReading_le_actualQPilotSignedLogClassical_of_structures` gives
   `QSourceLeQNorm`.
4. hθ: keep the one-way route; supply the product-coordinate identification
   (`TensorRegionCoordinateProduct`) and derive the hθ linear form.
5. Update `coord/LEAN-INDEX.md` per §5 (attribution, missing files, one-way lemma,
   stage4 red).

---

## 7. Route correction 2026-11-15（Lead）：one-way hθ/hq 用 rp_strict_measure_resolved

### 7.1 新增 donor：`rp_strict_measure_resolved`
- 文件：`tmp/sheaf/xif/paper/Mzk1HaarProductStrictMainlineActual.lean:165`；
- 声明：`theorem rp_strict_measure_resolved : rpVolume T (rpRegion T) < rpVolume T (s1902Hull T)`；
- 构造链：`rpRequirement : XiEContainmentRequirement`（`qRegion:=rpRegion`、`thetaPossibleImages:=rpRegion`、`hullRegion:=s1902Hull`；`possible_in_hull=rpRegion_subset_hull`，`q_pos`、`strict_measure` 由 `rpRegion_measure_lt_full`）→ `rp_strict_measure_resolved`；
- 证据：watchdog **DONE 2026-11-11T02:50:29Z**；olean 2026-11-11 10:50:29 > src 10:48:19（历史 DONE，当前未重编）；
- 用途：**one-way hθ/hq**（strict measure / contained θ-hull 单向比较）可直接消费，不需要 `ClosedBallMassFormula`，也不需要 exact `ProductHaarToFiberMult` 等式。

### 7.2 `ClosedBallMassFormula` / `ProductHaarToFiberMult` 重新定位
- `ProductHaarToFiberMult`（`Mzk1ProductFiberMultBridgeGapActual`）与 `ClosedBallMassFormula` 现在**只用于 exact product-Haar 等式**这条支线；
- one-way hθ/hq 主线**不等待**它们；`ProductFiber*` 的 DONE 只是 interface/gap 登记；
- `BadPlaceBijection` generally false（已记录），fiber 路线用 `QVBadPlaceFiber`（total map）或 injection。

### 7.3 对 wiring 结论的修改
- 原 §2.3/§4.3（hθ 需 product-coordinate identification 才能接 hθ 线性形式）**降级**：若只需 one-way hθ/hq bound，`rp_strict_measure_resolved` 已给 strict containment/严格测度不等式；
- 仍需的 identification 只剩：把实际 packet/region 与 `rpRegion`/`s1902Hull` 对齐（对象同一性），以及 hq 的 fiber/index 接线；
- 剩余 consumer：`XiEContainmentRequirement` 消费链（`Mzk1HaarProductStrictMainlineActual`）与 node06/09 carrier check。

---

## 8. Route decision 2026-11-15（Lead）：one-way hθ/hq 接受 node0609_rpRegion_volume_le_hull

### 8.1 接受的 one-way 终点
- 文件：`tmp/sheaf/xif/paper/Mzk1Node0609OneWayConsumerActual.lean`；watchdog **DONE 03:34:30Z**；olean **11:34:29 > src 11:33:20**；
- 定理：**`node0609_rpRegion_volume_le_hull : rpVolume T (rpRegion T) ≤ rpVolume T (s1902Hull T)`**（由 `node0609_rpRegion_volume_lt_hull` = `rp_strict_measure_resolved T` 取 `le_of_lt`）；
- 这是 **one-way hθ/hq inequality path 的合法终点**；strict 版本 `node0609_rpRegion_volume_lt_hull` 亦可用。

### 8.2 不再要求 exact weighted-q equality
- 精确 `ProductHaarToFiberMult` / `MqFiber` 等式（`Mzk1ProductFiberMultBridgeGapActual`、`Mzk1QVWeightedActual` 的 equality 部分、`ClosedBallMassFormula`）**在 inequality path 上不要求**；
- 它们只保留为 exact 分支/可选强化（interface/gap 登记即可）；
- hq 的 fiber/index 接线仍需要；但不需要先证 weighted-q 总和等式。

### 8.3 影响
- node06/09 的 inequality consumer 可直接：`Node09HqMultConsumerActual`（03:56:15 DONE）→ `Mzk1Node0609OneWayConsumerActual`（03:34:30 DONE）→ hθ one-way；
- 精确 equality 的 DONE 文件（ProductFiber 03:27:31、QVWeighted 03:33:17）不再是 blocker；
- 下一步集中在：rpRegion/s1902Hull 与实际 packet 的对象对齐 + hq fiber/index 接线。

---

## 9. CONFIRMED exact-missing inputs 2026-11-15（Lead）

- **horder**（`(qVFamily X.S b).order = 1`）：无 donor、存在 order>1 反例 → 不可无条件证明；
- **hcoef**（每 place `CoeffComparison (actualFn i) Fdeg l (chosenA i)`）：无 donor/反例方向确认 → exact missing；
- **hbase**（`Nonempty (FinitePlaceQCandidate (nativeBadBasePlace X))`）：absence of donor → 不可无条件证明；
- **结论**：当前 tree 不存在无条件闭合路线；最终命题必须 conditional on horder/hcoef/hbase（+ hmu0/hl/hc）；hmult 只余 horder，hper 只余 hcoef/hmu0/hl/hc。

---

## 10. Final conditional chain 2026-11-15（Lead）：ABC conditional bridge green

- **链路**：Node09FinalConditional（final_paper312_conditional）→ Node09ABCBridgeConditional（Node09ABCBridgeInterface/toCor312/heightBound）→ Node09GapDictionary（gap1/gap2 归约）→ Node09GapDonorSurvey → Node09ComparisonCards → **Node09FinalABCBridge.final_abcHeightBound_of_cards**；
- **最终 exact inputs**：horder、hcoef、hbase、cards family（Node09ComparisonCards；direct point-volume card + weight dictionary，dictionary jointly refutable）；
- 仅剩 stale probes FAIL（GaloisCompletionCurrent/PadicGalois）；无产品级 real red；no inhabitant/axiom introduced。

---

## 11. Round18 audit status 2026-11-15（Lead）

- Final conditional endpoints green：FinalConditional、ABCBridgeConditional、FinalABCBridge、CardsToFrontier、SingletonFinal、RegionMono、Gap2ToCards；
- Paper-level 仅：**frozen gap2**（Cor312EpsilonArithmeticComparison.regionVolume_le_normalizedWeight）+ **hweightDictionary**；
- Residual（显式输入）：horder/hcoef/hbase；no inhabitant/fake；comparison (1) removed by RegionMono；
- 05:40 后唯一 FAIL：QVFiberWeighted 05:41:49（rerun，非 paper-level）；stale probes 已知。

---

## 12. CRITICAL hdeg+D inconsistency 2026-11-15（Lead）

- hdeg + SourceUnitRegionHaarData D 不一致：`iqCarrierModel_sourceHaarData_not_nonempty_of_degreeFaithful`（IQCarrierConcreteModel.lean:583-590）；
- `Node09DegreeUpper` 的 hdeg+D 假设不可满足 → DegreeUpper vacuous，不能作 hdegreeBound 供给；
- hweightDictionary 无 actual evidence（WeightDictionaryScaling 仅 iff scaling-separated + degree-faithfulness satisfiability，而后者 vacuous）；
- cards/final endpoints 不假设 hdeg+D，非形式 vacuous，但无 discharge path；
- hull 侧：sourceHullVolume_eq_top_of_degreeFaithful、not_exists_sourceHullLogDegreeBound_of_degreeFaithful、cor312CarrierSpec_not_inhabited、dictionaries jointly refutable。

---

## 13. ROUTE RE-ANCHOR 2026-11-15（Lead，Round23）

- **mainline 重新锚定 N0–N11**；cards/S3135 链明确为 **auxiliary**（conditional 端点/等价记录），不作为 mainline 证据或完成度；
- 审计与进度以 N0–N11 为准；本轮无新证据；Ambient placeholder、UniformContinuitySource exact gap、no ABC inhabitant 不变。

---

## 14. ROUTE CORRECTION 2026-11-15（Lead）：deviation 记录

- 此前（Round23 起）把 cards/S3135 与 ad hoc N5 当 mainline = **route deviation**；
- 正确路线：**P1–P8 / D1-H1-S1-G1**；
- cards/S3135 与 ad hoc N5 降级为 off-route/auxiliary，不计 mainline 进度；后续审计只按正确路线。
