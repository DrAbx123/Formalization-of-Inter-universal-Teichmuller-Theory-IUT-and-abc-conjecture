# SIGNED-REUSE-CONFIRM — `Mzk1SignedLogVolumeCor312Actual` and `haarLogVolume_mono` (A1052)

Status: read-only confirmation; no compile.  This replaces the broken
`Mzk1SignedLogVolumeActual` (stopped per lead).

## 1. Reusable theorem list

`tmp/sheaf/xif/paper/Mzk1SignedLogVolumeCor312Actual.lean`:

| theorem/def | statement | usable? |
|---|---|---|
| `signedLogVolume vol S` (`:24`) | `Real.log (vol S)` | definition; no measure normalization |
| `signedLogVolume_mono` (`:29`) | `(hmono : S⊆T → vol S ≤ vol T)`, `S⊆T`, `0 < vol S` ⇒ `signedLogVolume vol S ≤ signedLogVolume vol T` | yes, abstract |
| `XiEContainment` (`:39`) | fields `qRegion`, `hullRegion`, `subset : qRegion ⊆ hullRegion`, `q_pos : 0 < vol qRegion` | yes, but **direction is q⊆hull** |
| `signedQ` (`:46`) | `signedLogVolume vol D.qRegion` | yes |
| `signedTheta` (`:51`) | `signedLogVolume vol D.hullRegion` | yes |
| `xi_f_signed_direction` / `signed_cor312_inequality` (`:57`/`:65`) | `hmono` + `D` ⇒ `signedQ D ≤ signedTheta D` | yes abstract; direction caveat below |
| `positive_magnitude_direction_obstruction` (`:73`) | `qVol ≤ hVol ⇒ -hVol ≤ -qVol` | a warning lemma, not the needed direction |

`tmp/sheaf/xif/paper/Mzk1QRegionInclusionActual.lean` (abc, corrected skeleton):

| theorem/def | statement | usable? |
|---|---|---|
| `RegionLogVol` (`:37`) | `logVol S = -Real.log (μ S).toReal` | yes |
| `haarLogVolume_mono_of_subset` (`:44`) | `S⊆T`, `μ S ≠ 0`, `μ T < ⊤` ⇒ `logVol T ≤ logVol S` | yes, signed/negative-log form |
| `rankOne_minimal` (`:74`) | `thetaRegion ⊆ qRegion` ⇒ `-|log Θ| ≥ -|log q|` | **correct A1049 direction** |
| `variant_rankone_conditional` (`:99`) | `-A ≤ -|log Θ|` | correct signed form |
| `variant_rankone_conditional_rev` (`:106`) | opposite inclusion ⇒ opposite inequality | warning/counterexample |

## 2. Direction caveat (critical)

`signed_cor312_inequality` derives
`signedQ D ≤ signedTheta D` from `D.subset : qRegion ⊆ hullRegion` and
`hmono : S⊆T → vol S ≤ vol T`.
With `signedLogVolume = Real.log ∘ vol`, this is
`log (vol q) ≤ log (vol hull)`.

Two conventions must be distinguished:

1. **`vol` = actual Haar measure** (positive, increasing under inclusion):
   if `vol q = exp(-A)`, `vol hull = exp(-R)`, then
   `q ⊆ hull ⇒ vol q ≤ vol hull ⇒ -A ≤ -R`; this is Cor 3.12, but the
   inclusion direction is **q⊆hull**.
2. **`logVol := -log μ` with `μ` the inverse-Haar quantity** (A1049/abc):
   `thetaRegion ⊆ qRegion ⇒ -A ≤ -R`.

The two are dual conventions.  The existing `XiEContainment` is written in
convention 1 (`vol` increasing, `q⊆hull`); it is **not** the A1049
`theta⊆q` structure.  Do not use `XiEContainment` as if it were
`theta⊆q` without changing `vol` to the inverse-Haar convention; otherwise the
sign is reversed.  The warning lemma `positive_magnitude_direction_obstruction`
records the sign trap for positive magnitudes.

## 3. `haarLogVolume_mono` exact signature

`LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceIQHullInterface.lean:68`:
```lean
theorem haarLogVolume_mono {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {S T : Set X} (hST : S ⊆ T) :
    haarLogVolume μ S ≤ haarLogVolume μ T
```
with
```lean
def haarLogVolume {X} [MeasurableSpace X] (μ : Measure X) (S : Set X) : ENNReal :=
  if μ S = ⊤ then ⊤ else ENNReal.ofReal (Real.log (μ S).toReal)
```
No finiteness hypothesis; `⊤` is preserved.  This is the correct monotonicity
for **theta⊆q**: `haarLogVolume μ theta ≤ haarLogVolume μ q`.

## 4. Integration into our QRegion (call plan)

Use the **negative-log** form for Cor 3.12:
```lean
noncomputable def negHaarLog {X} [MeasurableSpace X] (μ : Measure X) (S : Set X) : Real :=
  - (haarLogVolume μ S).toReal

theorem negHaarLog_anti_mono {X} [MeasurableSpace X] {μ : Measure X}
    {S T : Set X} (hST : S ⊆ T) (hT : μ T < ⊤) :
    negHaarLog μ T ≤ negHaarLog μ S := by
  have h := haarLogVolume_mono hST
  have hTlog : haarLogVolume μ T ≠ ⊤ := by
    rw [haarLogVolume_of_lt_top hT]; exact ENNReal.ofReal_ne_top
  -- h : haarLogVolume μ S ≤ haarLogVolume μ T
  -- toReal monotonicity and negation
  ...
```
Then:
- `thetaRegion ⊆ qRegion` ⇒ `haarLogVolume μ theta ≤ haarLogVolume μ q`;
- `negHaarLog μ q ≤ negHaarLog μ theta`;
- identify `negHaarLog μ q = -A`, `negHaarLog μ theta = -R` (GAP-N5);
- conclude `-A ≤ -R`;
- feed `signedCor312Contract` with `qSigned := -A`, `thetaSigned := -R`,
  `hq : -A < 0`, `hle : -A ≤ -R`.

For the **existing** `Mzk1QRegionInclusionActual` skeleton, instead instantiate
`RegionLogVol.logVol := negHaarLog` and use `haarLogVolume_mono_of_subset`; it
already proves `theta⊆q ⇒ logVol q ≤ logVol theta`.

## 5. Do not use

- `Mzk1SignedLogVolumeActual` (broken; replaced).
- `XiEContainment` as a direct N5 bridge without converting its `vol`
  convention and its `q⊆hull` direction; under A1049 it gives the reversed
  sign unless `vol` is the inverse-Haar measure.
- `signed_cor312_inequality` with `q⊆hull` and `vol` = Haar measure to claim
  `theta⊆q` — the two conventions are dual and must be unified explicitly.

## 6. Remaining gaps

1. Region identification: actual C3 theta hull vs q-pilot region; only
   abstract `qRegion`/`thetaRegion` in `Mzk1QRegionInclusionActual`.
2. Volume identities: `negHaarLog μ qRegion = -A`, `negHaarLog μ thetaRegion = -R`.
3. Conversion of `haarLogVolume` (ENNReal, `⊤` case) to `Real` with the
   finiteness/positivity hypotheses needed by the `Real.log` identities.
4. If using `XiEContainment`, add a theorem converting its increasing-`vol`
   convention to the negative-log convention (or a new structure with
   `theta⊆q`).

## 7. Verdict (updated A1053/A1054, aligned with abc)

- `signedLogVolume_mono` and `signed_cor312_inequality` are **valid abstract
  monotonicity/sign lemmas**, reusable after choosing the `vol` convention.
- **Paper-faithful instantiation (abc A1053):** `vol` = actual Haar volume
  (q-pilot region volume < 1), `XiEContainment.subset = qRegion ⊆ hullRegion`,
  `A = -signedQ`, `R = -signedTheta`; then `signed_cor312_inequality` is exactly
  `-A ≤ -R` (variant).  In this convention the geometric input is **q⊆hull**.
- The inverse-normalization `theta⊆q` (`logVol=-log μ`, `logVol q=-A`,
  `μq=e^A`) is the dual convention; it is only an abstract sufficient form and
  is marked `SUPERSEDED-PARTIAL` in abc's `Mzk1QRegionInclusionActual`.
- Both conventions are related by `vol = exp(-·)`; do not mix them.
- `haarLogVolume_mono` is directly usable in the **negative-log** convention; in
  the paper-faithful signed convention use the signed stack / Haar volume.
- Correct paper integration: signed stack + `q⊆hull` + `A=-signedQ`,
  `R=-signedTheta` (abc §5); the `theta⊆q` QRegion skeleton is superseded for
  paper integration.

---

## 8. Update A1053 — replacements and assembly without the signed stack

### 8.1 What must be replaced in `Mzk1SignedLogVolumeCor312Actual`

The file is proof-correct as an abstract monotonicity lemma, but its
`XiEContainment` structure fixes the wrong paper direction (`qRegion ⊆ hullRegion`).
To instantiate it for our target under the A1049 convention:

1. **Replace** `XiEContainment.subset : qRegion ⊆ hullRegion` by
   `thetaRegion ⊆ qRegion`; equivalently define a new structure
   `N5Containment` with fields `thetaRegion`, `qRegion`,
   `theta_subset_q : thetaRegion ⊆ qRegion`, `q_pos`, volume identities.
2. **Replace** `signedQ/signedTheta` by `qSigned := -A`, `thetaSigned := -R`
   (or `negHaarLog μ qRegion`, `negHaarLog μ thetaRegion`).
3. **Replace** `signedLogVolume_mono` (which is increasing in `vol`) by the
   negative-log form: `negLogVolume q ≤ negLogVolume theta` from
   `theta⊆q` and `haarLogVolume_mono`.
4. Keep `positive_magnitude_direction_obstruction` as a warning: it is the
   sign trap for positive magnitudes; do not use it as the target direction.

A reverse lemma is not needed if we use the negative-log convention: the
monotonicity direction flips once, exactly as in `Mzk1QRegionInclusionActual`.

### 8.2 If the signed stack is not used: minimal assembly

Use only:
- `Mzk1QRegionInclusionActual` (`RegionLogVol`, `haarLogVolume_mono_of_subset`,
  `rankOne_minimal`, `variant_rankone_conditional`);
- `haarLogVolume_mono` from `FinitePlaceIQHullInterface:68`;
- signed contract `signedCor312Contract` or abstain from contract and state
  the real inequality directly.

Steps:
1. Choose `μ : Measure X`, `thetaRegion qRegion : Set X`.
2. Prove/assume `hsub : thetaRegion ⊆ qRegion`.
3. `haarLogVolume_mono hsub : haarLogVolume μ thetaRegion ≤ haarLogVolume μ qRegion`.
4. Define `negHaarLog μ S := -(haarLogVolume μ S).toReal`; from step 3
   (with finite measure of `qRegion`) get
   `negHaarLog μ qRegion ≤ negHaarLog μ thetaRegion`.
5. Supply the two identifications
   `hq : negHaarLog μ qRegion = -A`,
   `hθ : negHaarLog μ thetaRegion = -R`.
6. Conclude `-A ≤ -R`, i.e. `-|log q| ≤ -|log Θ|`.
7. Feed `signedCor312Contract` with `qSigned := -A`, `thetaSigned := -R`,
   `hqneg : -A < 0`, `hle : -A ≤ -R`; or use
   `Mzk1QRegionInclusionActual.variant_rankone_conditional`.

### 8.3 Candidate volume identities in existing files

**Theta side (`-R`):**
- `S2717ThetaHullLogVolume` (`S2717Cor312FullTargetActual:50`) is defined as
  `-(globalThetaHullInterface.logVolume globalThetaHull).toReal`; this is the
  paper `-|log Θ|` candidate on the global IQ hull.
- `S2807_thetaHullVolume_eq_haarRegion` (`S2807ThetaHullVolumeIdentityActual:40`)
  proves `S2717ThetaHullLogVolume = -(haarLogVolume C3Haar C3Region).toReal`
  on the single C3 tensor block; this is the closest concrete theta-side
  identification to `negHaarLog`.
- `HullDetObjectActual.literalIQHullLogVolume` / `detNormalizedLogVolume` are
  global/single-packet Haar log-volume readouts, not yet equated to the N5
  theta region.

**q side (`-A`):**
- `S2717QPilotLogVolume` (`S2717Cor312FullTargetActual:69`) =
  `sourceQPilotSignedLog (I.initial)`; this is the actual signed q-pilot
  scalar, candidate for `-A`.
- `HullDetObjectActual.qPilotLogVolume` (`:158`) = `qPilotLogVolumeReading P`,
  with `qPilotLogVolume_constructed` giving `-|Real.log (‖P.line.C3.q.q‖)|`.
- `S3016StepVQPilot` (`S3016StepVQPilotIdentificationActual:30`) is the
  q-pilot line-bundle log-volume candidate on the ABC-support ideal.
- `ConcreteGlobalPilotDataActual.qPilotSignedLogVolume` is another global
  signed q candidate.

**Status of the two identities: candidates only, not connected.**
- There is no theorem `negHaarLog μ qRegion = S2717QPilotLogVolume` or
  `= qPilotLogVolume`.
- There is no theorem `negHaarLog μ thetaRegion = S2717ThetaHullLogVolume`
  for the **same** `μ`/region; `S2807` identifies the global theta hull with
  the negative C3 Haar log-volume, which is a strong theta-side candidate.
- The q and theta candidates live on different carriers (source scalar vs
  global IQ hull vs C3 tensor block); selecting one common `X`/`μ` is the
  remaining GAP-N5.

### 8.4 Verdict

- The signed stack cannot be used as-is: its containment direction is
  `q⊆hull`, opposite to A1049's `theta⊆q`; using it without changing the
  convention gives the reversed sign.
- Use `haarLogVolume_mono` + `Mzk1QRegionInclusionActual` negative-log skeleton.
- The two volume identifications have concrete candidates on each side, but
  no common-measure theorem exists; they remain explicit fields/GAP-N5.

---

## 9. A1054 final alignment with abc (supersedes the 'cannot be used' wording)

abc's `coord/REUSE-SIGNEDLOG-INTEGRATION.md` §5 fixes the semantics:

- `signedLogVolume vol S = Real.log (vol S)` (log measure, not negative log);
- `XiEContainment.subset : qRegion ⊆ hullRegion`;
- `signed_cor312_inequality : signedQ ≤ signedTheta`;
- **paper-faithful**: `vol` = actual Haar volume (q region volume < 1),
  `A = -signedQ`, `R = -signedTheta`; `q⊆hull` ⇒ `-A≤-R`.  This is the variant.

So the signed stack **is** usable for the paper target, provided one uses the
Haar/exponential normalization and `q⊆hull`.  The earlier remark that it is
'opposite' applies only when `vol` is replaced by inverse Haar and
`logVol=-log μ` with `theta⊆q`; that is abc's abstract QRegion skeleton
(`SUPERSEDED-PARTIAL`), not the paper-faithful integration.

Recommended paper integration:
1. instantiate `vol` as the actual Haar volume on the chosen region carrier;
2. prove `qRegion ⊆ hullRegion` (Step (xi-d) geometric GAP);
3. use `signed_cor312_inequality` with `A=-signedQ`, `R=-signedTheta`;
4. optionally use abc's `SignedQRegionData` adapter;
5. keep the two volume identities as explicit fields;
   the q⊆hull geometric construction remains the open Step (xi-d) input.
