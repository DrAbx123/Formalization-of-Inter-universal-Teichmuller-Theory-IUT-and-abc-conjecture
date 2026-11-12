# NEW MATHLIB (v4.33.1) ANALYSIS — Analysis/Measure/Haar/log scan (A506)

Status: **no cherry-pick recommended for our litHaar/log-volume/hull-radius basics.**
Reason below: (i) the requested local v4.33.1 checkout is not present (only the
toolchain/manifest), and (ii) the remote v4.32.2 -> v4.33.1 diff in the relevant
Haar/log/product-measure files is empty (only one docstring commit in
MeasureTheory/Group/Measure.lean), so there are no new lemmas to cherry-pick.

## 1. Local environment evidence (paths checked on disk)

| Path | Version/state |
|---|---|
| .lake/packages/mathlib | v4.32.2, HEAD 905b95818e (our main build) |
| tmp/external/flt-lean | only lean-toolchain v4.33.1; **no .lake directory**; lake-manifest.json mathlib rev db584cd6d46c92f209a44c0f1c829460d327499d (not fetched) |
| tmp/external/iut4-sec1/.lake/packages/mathlib | v4.32.0, HEAD 81a5d257c8 (older than ours) |
| tmp/external/Takkun-IUT_LEAN/.lake/packages/mathlib | v4.31.0 |
| tmp/external/promachina-iut-lean-latest/.lake/packages/mathlib | bare .git only (no checkout, no refs) |

So the premise path tmp/external/flt-lean/.lake/packages/mathlib is currently
absent; a v4.33.1 source tree is not available locally.

## 2. Remote v4.32.2 -> v4.33.1 diff (GitHub API; fetched successfully before the
network host became unavailable)

- Tag v4.32.2 = 905b958 (2026-07-28); tag v4.33.1 = 0df444a (2026-08-21).
- Directory listings at ref=v4.33.1 are **identical** to our v4.32.2 for:
  - Mathlib/MeasureTheory/Measure/Haar (Basic, Disintegration, DistribChar, Extension,
    InnerProductSpace, MulEquivHaarChar, NormedSpace, OfBasis, Quotient, Unique)
  - Mathlib/MeasureTheory/Group
  - Mathlib/MeasureTheory/Constructions
  - Mathlib/Analysis/SpecialFunctions/Log
  - Mathlib/MeasureTheory/Integral
  - Mathlib/MeasureTheory/Measure/Lebesgue
  - Mathlib/Analysis/Normed/Group
  → no new files in these areas.
- Per-file commit lists since 2026-07-28 up to v4.33.1:
  - Mathlib/MeasureTheory/Measure/Haar/Basic.lean: no commits
  - Mathlib/MeasureTheory/Measure/Haar/OfBasis.lean: no commits
  - Mathlib/MeasureTheory/Measure/Haar/Quotient.lean: no commits
  - Mathlib/MeasureTheory/Group/Measure.lean: one commit fcdfe22994
    "chore: add missing `to_additive` docstrings in MeasureTheory.Group (#41639)"
    (docstring only)
  - Mathlib/MeasureTheory/Constructions/Pi.lean: no commits
  - Mathlib/Analysis/SpecialFunctions/Log/Basic.lean: no commits
  - Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean: no commits
- Limitation: the remaining Haar/Log/Integral files were not individually queried
  because api.github.com stopped resolving to a public IP mid-scan; the directory
  listing evidence above still rules out new files in those directories.

## 3. What our files need (and whether v4.33.1 could replace anything)

| Our hand-written asset | Needed lemma | v4.33.1 candidate | Verdict |
|---|---|---|---|
| LeanFormal/IUT/Foundations/LocalFields/HaarLogVolume.lean (`haarLogVolume`, `logClosedBallVolume`, `addHaar_closedBall_unit_pos`, `logClosedBallVolume_smul`) | log of additive Haar measure, closed-ball scaling | none new in Haar/Basic or OfBasis during window | keep ours; no cherry-pick |
| LeanFormal/IUT/Foundations/LocalFields/FinitePadicHaarScaling.lean / PadicFiniteCoordinateHaarScaling.lean | `μ(p·S) = p^{-[K:Qp]}·μ S` | v4.33.1 has no new Haar scaling files/commits (same EqHaar.lean) | keep ours |
| LeanFormal/IUT/Foundations/LocalFields/FinitePadicTensorIntegralRegion.lean | product-region compactness `isCompact_univ_pi`, `Measure.pi_pi` | Mathlib v4.32.2 already provides both; no v4.33.1 changes in Constructions/Pi.lean | use Mathlib directly (as now) |
| litHaar assets (tmp/sheaf/xif/paper, A483/LiteralIQCarrierConstruction etc.) | additive Haar translation invariance on the tensor block (`measure_image_add_translate`) | our own `PadicLogShellModel.measure_image_add_translate` wraps Mathlib `measure_preimage_add`; no new v4.33.1 lemma in Group/Measure (only docstrings) | keep our wrapper |
| hull radius/hull-readout (HullDetObjectActual, C3 shell) | `zpow_le_zpow_right₀`, log lemmas (`Real.log_pow`, `log_le_log_iff`) | all present in v4.32.2; no changes in Log/Basic during window | already using Mathlib |

## 4. Recommendation

1. Do **not** upgrade the main build to v4.33.1 (would rebuild ~10k oleans and the
   diff relevant to us is empty).
2. Do not create tmp/newmathlib/ copies for these files; nothing to adapt.
3. If a specific missing v4.33.1 lemma is later identified, cherry-pick only that
   single lemma: fetch the file at rev 0df444a from GitHub raw and re-prove the
   lemma against v4.32.2 API (the v4.32.2 -> v4.33.1 changes in our areas are only
   docstrings, so copies should compile unchanged in most cases).
4. If the lead wants a complete exhaustive diff, a v4.33.1 checkout must be fetched
   locally (the manifest rev is db584cd6) because GitHub API access is currently
   unavailable.

## 5. Open items / requests

- Provide or fetch tmp/external/flt-lean/.lake/packages/mathlib at rev
  db584cd6 (v4.33.1) if a full diff is required.
- Re-run the per-file commit scan for the remaining files
  (Haar/Unique, Haar/Extension, Haar/NormedSpace, Log/PosLog, Log/ENNRealLog,
  MeasureTheory/Integral/*) once network access is restored.
