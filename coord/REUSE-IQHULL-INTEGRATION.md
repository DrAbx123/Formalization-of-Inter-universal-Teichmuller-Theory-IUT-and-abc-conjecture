# REUSE-IQHULL-INTEGRATION — IQHull/QRegionCarrier assets (A1051)

Status: read-only audit; no compile.  Direction convention fixed by A1049:
the sufficient inclusion for Cor 3.12 is **`thetaRegion ⊆ qRegion`** when
`logVol S := -log μ(S)` and `qSigned=-A`, `thetaSigned=-R`.

## 1. Exact statements

### `FinitePlaceIQHullInterface.lean`
- `haarLogVolume μ S : ENNReal` (`:51`):
  `if μ S = ⊤ then ⊤ else ENNReal.ofReal (Real.log (μ S).toReal)`.
- `haarLogVolume_of_lt_top` (`:55`).
- `haarLogVolume_eq_zero_of_null` (`:61`).
- **`haarLogVolume_mono` (`:68`)**:
  `{S T : Set X} (hST : S ⊆ T) : haarLogVolume μ S ≤ haarLogVolume μ T`.
  No finiteness of `T` assumed; the `⊤` case is handled separately.
- `exists_arithmeticTupleIQHullLogVolumeInterface` (`:104`):
  gives `IQHullLogVolumeInterface` with `logVolume = haarLogVolume μ`,
  `hull = unitRegion = arithmeticTupleCanonicalHull`, and
  `logVolume_mono := fun hST => haarLogVolume_mono hST`.

### `QRegionCarrierInterface.lean`
- `structure QRegionCarrierSpec (X)` (`:59`) fields:
  `region`, `basePoint/ basePoint_mem`, `moduleUnit/ moduleUnit_mem`,
  `logShell`, `logShell_subset_region : logShell ⊆ region`,
  `lgpLink`, `logVolume : Set X → ENNReal`,
  `logVolume_mono : S ⊆ T → logVolume S ≤ logVolume T`.
- **`qRegionCarrierSpec_logShell_volume_le_region` (`:86`)**:
  `S.logVolume S.logShell ≤ S.logVolume S.region`,
  from `S.logVolume_mono S.logShell_subset_region`.

Interpretation: this is the **log-shell/`lambda·O` half** of the q-carrier
containment (`logShell ⊆ qRegion`), and its volume monotonicity.  It does not
mention a theta-hull region; it is **not** the N5 `thetaRegion ⊆ qRegion`
comparison, nor its converse.

### `FinitePlaceIQHullSignedLogVolume.lean`
- `arithmeticTupleCanonicalHullHaarLog μ :=`
  `Real.log (μ (arithmeticTupleCanonicalHull ...)).toReal` (`:37`).
- `arithmeticTupleIQHullUnitRegionHaarLog μ :=`
  `Real.log (μ (arithmeticTupleIQHullUnitRegion ...)).toReal` (`:43`).
- `arithmeticTupleCanonicalHull_subset_IQHullUnitRegion`
  (in `FinitePlaceIQHullSharpUpperBound.lean:149`):
  `canonicalHull ⊆ IQHullUnitRegion`.
- `arithmeticTupleCanonicalHullHaarLog_le_unitRegionHaarLog` (`:89`):
  `arithmeticTupleCanonicalHullHaarLog μ ≤ arithmeticTupleIQHullUnitRegionHaarLog μ`.
- `arithmeticTupleCanonicalHull_measure_le_unitRegion` (`:81`):
  `μ canonicalHull ≤ μ unitRegion`.
- `haarLogVolume_eq_ofReal_signedLog` (`:118`) and the `ofReal` bridges
  (`:124`, `:132`).

Interpretation: this is a **hull ⊆ scaled unit-region** comparison, with
`log μ(hull) ≤ log μ(unit)`.  It is not the paper's q-pilot region comparison
unless `unitRegion` is identified with the q-pilot region; no such
identification is in the file (it is the `lambda·O` reference unit region).

### `FinitePlaceIQHullSharpUpperBound.lean`
- `arithmeticTupleIQHullUnitRegion := lambda • canonicalUnitReference` (`:69`).
- `arithmeticTupleIQHullUnitLogTheta μ := log (μ unitRegion).toReal` (`:120`).
- `arithmeticTupleIQHull_hull_logVolume_le_unitRegion` (`:159`):
  `haarLogVolume μ (canonicalHull) ≤ ENNReal.ofReal (unitLogTheta μ)`.
- Normalization caveat: `unitLogTheta` sign depends on the additive Haar
  scaling; `exists_normalized_addHaar...` rescales to `μ unitRegion = 1`.

### `FinitePlaceNormalizedUnitScalingLogVolume.lean`
- `arithmeticTupleNormalizedLogVolume_mono` (`:107`):
  `S ⊆ T → 0 < μ S → μ T < ⊤ →
   normalizedLogVolume S ≤ normalizedLogVolume T`.
- `arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic` (`:379`):
  exact normalized log-volume of `F(c)·O_hol` = `-(Σ c_i) log p`.
- `arithmeticTupleNormalizedLogVolume_le_of_subset_fractionalLattice_mul` (`:547`):
  `S ⊆ F(c)·O_hol`, `0<μ S` ⇒ `normalizedLogVolume S ≤ -(Σ c_i) log p`.

## 2. Is `qRegionCarrierSpec_logShell_volume_le_region` the N5 inclusion?

**No.**  It proves
`logVolume(logShell) ≤ logVolume(region)` from `logShell ⊆ region`;
the `logShell` is the `lambda·O`/log-shell slot, and `region` is the
`QRegionCarrierSpec.region` (q-pilot representation region).  It is a
**containment inside the q-region**, not a comparison between the theta hull
and the q region.  It supplies at most one half of a lower bound for the
q-region volume (`logShell` inside `qRegion`), not the N5 `theta ⊆ q` step.

Likewise, the signed IQHull inequality
`log μ(canonicalHull) ≤ log μ(unitRegion)` is a hull-vs-unit-region comparison;
it becomes an N5 statement only after identifying `unitRegion` with `qRegion`
and `canonicalHull` with `thetaRegion` (not present).

## 3. Existing `XiEContainment` direction (important)

`Mzk1SignedLogVolumeCor312Actual.lean`:
```lean
structure XiEContainment (α) (vol : Set α → Real) where
  qRegion : Set α
  hullRegion : Set α
  subset : qRegion ⊆ hullRegion
  q_pos : 0 < vol qRegion
theorem signed_cor312_inequality
    (hmono : S ⊆ T → vol S ≤ vol T) (D : XiEContainment α vol) :
    signedQ D ≤ signedTheta D
```
This encodes **`qRegion ⊆ hullRegion`**, the opposite of the A1049 sufficient
direction.  Under the A1049 convention (`logVol=-log μ`, `qSigned=-A`,
`thetaSigned=-R`), one needs `thetaRegion ⊆ qRegion`.  Do **not** combine
`XiEContainment` with `haarLogVolume_mono` and claim Cor 3.12 without checking
the volume convention: with the positive-measure convention it gives the
reversed inequality (`-A ≥ -R`), as recorded by
`positive_magnitude_direction_obstruction` in the same file.

`Mzk1QRegionInclusionActual.lean` (abc) is the corrected abstract skeleton:
- `RegionLogVol.logVol S = -Real.log (μ S).toReal` (`:37`);
- `haarLogVolume_mono_of_subset` (`:44`): `S⊆T` ⇒ `logVol T ≤ logVol S`;
- `rankOne_minimal` (`:74`): `thetaRegion ⊆ qRegion` ⇒ `-|logΘ| ≥ -|logq|`;
- `variant_rankone_conditional_rev` records the opposite direction.

## 4. Assembly steps (correct direction)

1. **Regions.**  Use a region pair `thetaRegion`, `qRegion` on the same
   measurable space.  For the actual C3 carrier candidate:
   `actualC3LogShellTensorRegion` / `actualHolomorphicHull` for the theta side;
   the q-pilot region needs the `QRegionCarrierSpec.region`/`qPilotClassicalRegion`
   identification (GAP).
2. **Containment.**  Prove/assume `thetaRegion ⊆ qRegion` (A1049).
3. **Monotonicity.**  `haarLogVolume_mono` gives
   `haarLogVolume μ thetaRegion ≤ haarLogVolume μ qRegion`.
   For signed real logs define
   `negLogVolume S := -Real.log (μ S).toReal`; then
   `theta⊆q ⇒ negLogVolume q ≤ negLogVolume theta`.
4. **Identifications.**  Need
   `negLogVolume qRegion = -A` and `negLogVolume thetaRegion = -R`
   (q-pilot/theta-pilot log-volume identities).  These are the N5 GAP-N5
   fields; they are not supplied by `QRegionCarrierSpec` or IQHull alone.
5. **Signed contract.**  Feed
   `qSigned := -A`, `thetaSigned := -R`, `hle : -A ≤ -R` to
   `signedCor312Contract` (`Mzk1SignedCor312ContractActual:22`) or
   `variant_rankone_conditional` (`Mzk1QRegionInclusionActual:99`).
   The contract also needs `hq : qSigned < 0`, i.e. `0 < A`.
6. **XiE/StepXI.**  The strict/non-vacuous `XiEContainmentRequirement`
   (`Mzk1XiEContainmentRequirementActual:29`) cannot be used as-is because its
   `q_in_possible/possible_in_hull` chain is `q⊆theta⊆hull`; either reverse the
   direction in a new structure or keep it only as a non-vacuity witness and
   prove the signed inequality from the corrected theta⊆q inclusion.

## 5. Reuse verdict

| asset | reusable for N5? | caveat |
|---|---|---|
| `haarLogVolume_mono` | **yes** | exact, no finiteness hypothesis; use signed negative log for Cor 3.12 |
| `qRegionCarrierSpec_logShell_volume_le_region` | **partly** | only `logShell⊆qRegion` (one half); no theta region |
| `FinitePlaceIQHullSignedLogVolume` monotonicity | **partly** | `hull⊆unitRegion`; unitRegion not identified with qRegion |
| `FinitePlaceNormalizedUnitScalingLogVolume` | **yes for local q-side bounds** | exact fractional-lattice formula; not the theta hull comparison |
| `XiEContainment`/`signed_cor312_inequality` | **no, opposite direction** | `q⊆hull`; A1049 needs `theta⊆q` |
| `Mzk1QRegionInclusionActual` | **yes** | corrected abstract skeleton; concrete regions/volume identities are fields/GAP |

## 6. Minimal integration target

```lean
-- theta subset q, both regions with finite positive Haar mass
theorem n5_theta_subset_q {α} [MeasurableSpace α] (μ : Measure α)
    {thetaRegion qRegion : Set α}
    (hsub : thetaRegion ⊆ qRegion)
    (hθpos : 0 < μ thetaRegion) (hqfin : μ qRegion < ⊤) :
    -Real.log (μ qRegion).toReal ≤ -Real.log (μ thetaRegion).toReal := by
  have hmono := measure_mono hsub
  have hlog : Real.log (μ thetaRegion).toReal ≤ Real.log (μ qRegion).toReal := ...
  linarith
```
The missing identifications are exactly
`-Real.log (μ qRegion).toReal = -A` and
`-Real.log (μ thetaRegion).toReal = -R`; they are the GAP-N5 fields.

---

## 7. A1054 convention alignment (with abc)

Two equivalent conventions:
1. **Paper-faithful signed Haar**: `vol` = Haar volume (q region <1),
   `signedLogVolume=log vol`, `q⊆hull`, `A=-signedQ`, `R=-signedTheta`;
   `signedQ≤signedTheta` is `-A≤-R`.  This is the abc signed-stack usage.
2. **Inverse/normalized negative-log**: `logVol=-log μ`, `μq=e^A`, `theta⊆q`;
   `Mzk1QRegionInclusionActual`; marked `SUPERSEDED-PARTIAL` for paper
   integration.

`haarLogVolume_mono` is valid in both; the direction is determined by the
normalization, not by the monotonicity lemma.  Do not combine `XiEContainment`
with the inverse-normalization `theta⊆q` structure without converting `vol`.
