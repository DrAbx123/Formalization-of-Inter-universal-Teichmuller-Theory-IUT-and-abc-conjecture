# Theta hull log-volume: sign and normalization audit

Scope: source-text and current-tree audit only. No Lean objects are introduced
here. All file references are to the current tree.

## 1. Paper normalization and sign

The local log-volumes `μ_log` of IUT III, Proposition 3.9, (i), are normalized
so that the "local holomorphic" integral structures have log-volume 0 and
multiplication by the local uniformizer adds `−log(p_v)`:

* `μ_log(O_αF_vQ) = 0` for the integral structures (iut3.txt:6963-7000);
* "multiplication ... by `p_v` corresponds to adding `−log(p_v)`"
  (iut3.txt:7004-7007);
* the same convention in IUT IV: `μ_log(R_i) = 0`,
  `μ_log(p·R_i) = −log(p)` (iut4.txt:688-691).

Thus `μ_log` is a normalized measure, not the pointwise map
`x ↦ log |x|`. A set smaller than the integral/unit reference (in particular a
p-adic set of elements with norm < 1) has **negative** log-volume; a set larger
than the reference has positive log-volume. The zero point of the scale is the
unit/integral region, not the value 1.

The theta values are

`q_v^{j^2}`, `v ∈ V_bad`, `j ∈ F_l^×`

(iut3.txt:899-907). Since the bad-place q-parameters satisfy `0 < q_v < 1`,
every theta value is < 1, so `log(q_v^{j^2}) < 0`. Consequently the
corresponding region/divisor has **negative** signed log-volume.

## 2. `−|log Θ|` and `|log Θ|`

The paper writes the Θ-pilot log-volume as

`−|log(Θ)| ∈ R ∪ {+∞}`

(iut3.txt:902-907). The text explicitly warns that the notation may look
confusing, and explains that `−|log(Θ)|` is meant to be a **positive real
multiple of `−|log(q)|`** — which is itself a negative real — plus a possible
error term that may be `+∞` (iut3.txt:911-918). The positive magnitude is
defined by

`|log(Θ)| := −(−|log(Θ)|) ∈ R ∪ {−∞}`

(iut3.txt:919-922).

Corollary 3.12 / Theorem B states

`−|log(Θ)| ≥ −|log(q)|`

(iut3.txt:1227-1229, 10527-10529). The proof explicitly assumes
`−|log(Θ)| < 0` whenever it is finite, since an inequality
`−|log(Θ)| ≥ 0` would give `−|log(Θ)| ≥ 0 > −|log(q)|`, contradicting the
desired inequality (iut3.txt:10532-10534). So, in the finite case:

* `−|log(Θ)|` is **negative** (the signed Θ-pilot log-volume);
* `|log(Θ)|` is its positive negation (the magnitude);
* `−|log(Θ)| ≥ −|log(q)|` is equivalent to
  `|log(Θ)| ≤ |log(q)|`.

There is no separate positive "hull log-volume" in the paper's signed notation:
the positive scalar is the magnitude `|log(Θ)|`, and the signed scalar is
`−|log(Θ)|`.

## 3. What a correct formal object must have

A final xi-f object must use the actual signed `μ_log` and the unit-region
normalization:

* reference/unit region log-volume is 0;
* finite `−|log(Θ)|` is a **negative real**, not an `ENNReal` clamped at 0;
* `|log(Θ)|` is the positive magnitude `−(−|log(Θ)|)`;
* the paper direction is
  `−|log(q)| ≤ −|log(Θ)|`, equivalently
  `|log(Θ)| ≤ |log(q)|`;
* pointwise/per-place `log(θ_v)` with `θ_v < 1` contributes a negative
  signed log-volume; summing over places gives a negative hull scalar in the
  finite case.

In particular, a definition of the form

`ENNReal.ofReal (Real.log (volume))`

with a negative real log silently becomes 0, and

`max 0 (−sourceLocalLogDegree)`

is a positive-part construction, not the signed paper hull log.

## 4. Current files using the old zero truncation

The old value-layer volume is

`sourcePointVolume v x = ENNReal.ofReal (sourceLocalLogDegree v x)`

(LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/SourceImageHullVolume.lean:103-
109). For a theta-pilot point,
`sourceLocalLogDegree = card(SourceVolumeIndex l) * log(thetaValueAt ...) < 0`,
so `ENNReal.ofReal` truncates it to 0; `sourceSetVolume` (SourceImageHullVolume.lean:188) is the corresponding
supremum of these truncated point volumes.

The following current files still build their hull/image log-volume from
`sourceSetVolume` or `sourcePointVolume`, so the negative theta contribution is
lost. They are **not usable for final xi-f**:

| file | old-truncation use | consequence |
|---|---|---|
| `GlobalThetaPilotHullLogVolumeActual.lean` | `thetaHullVolumeAt := sourceSetVolume ...`; `globalThetaHullLogVolume := ∑ log (volume.toReal)` | per-place theta hull volume is 0, so the global hull log is 0 and any signed comparison is vacuous |
| `ThetaLinkLogKummerActual.lean` | `signedImageLogVolume` / `signedHullLogVolume` from `sourceSetVolume ... .toReal` | signed volumes are −0 = 0, not the paper negative log-volumes |
| `ThetaPilotHullProcessionActual.lean` | `thetaPilotHullVolume := sourceSetVolume ...`; signed log from its `toReal` | procession log-volume is 0; no actual −|log Θ| |
| `WeakIQComparisonDataActual.lean` | `thetaPilotImageVolume` / `thetaPilotHullVolume := sourceSetVolume ...` | volume data are truncated; not paper μ_log |
| `GlobalThetaHullVsQPilotComparisonActual.lean` | uses `globalThetaHullLogVolume` from the old file | comparison is against 0, not the paper signed hull |
| `GlobalHullSignedComparisonActual.lean` | `signedThetaHullLogVolume := -globalThetaHullLogVolume` from the old file | reduces to −0; all signed/magnitude equivalences are vacuous, not final xi-f |
| `IndeterminaciesActual.lean` | `sourceSetVolume` fixedness of regions | action-fixedness may be true, but the induced volume/log-volume data are the old truncated ones and cannot be cited as paper log-volume |

`GlobalThetaPilotHullLogVolumeActual.lean` is the upstream source of the old
scalar. `GlobalHullSignedComparisonActual.lean` is logically equivalent to its
magnitude bound but inherits the same zero-truncated object; its EXIT=0 compile
does not make it paper-valid.

## 5. ENNReal / Haar-normalization files with zero clamping

Separately from `sourceSetVolume`, the Haar-based files use

`haarLogVolume μ S = ENNReal.ofReal (Real.log (μ S))`.

If `Real.log (μ S) < 0`, this again truncates to 0. The current files
therefore require an explicit nonnegativity hypothesis
`CanonicalHullLogNonneg` / `CanonicalHullRealLogNonneg`:

* `HaarThetaNormalizationActual.lean`;
* `HaarThetaAverageProof.lean`;
* `HaarUnitFactorProof.lean`;
* `SignedHnormalActual.lean`;
* `PaperProcessionNormalization.lean`;
* `GlobalIQHullInterfaceActual.lean`;
* `WeakThetaHullLogVolumeActual.lean`.

These are conditional and do not establish the paper's finite **negative**
`−|log(Θ)|`: they avoid truncation by assuming the log is nonnegative, while
the paper's finite signed hull log is negative. They may be used only after
replacing the ENNReal log by a real signed `μ_log`; as written they are not
final xi-f.

`NormalizedIQHullActual.lean` does construct the actual unit region and a
normalized hull-log functional on the actual global IQ Haar data, but its
actual global Theta-pilot image/hull/lambda-scaling data are explicitly missing
(`NormalizedIQHullMissingData` / `NormalizedIQHullObstruction`). It is a
candidate interface, not final xi-f.

## 6. Corrected positive constructions (candidates only)

The following files avoid the old `sourceSetVolume` truncation by constructing
a **positive magnitude**:

* `SourceHullVolumeSignCorrectedActual.lean`:
  `positivePointLogVolume := −sourceLocalLogDegree`,
  `positiveSetLogVolume := ⨆ ENNReal.ofReal (positivePointLogVolume)`.
  This corrects the sign for theta points, but is still an ENNReal sup and
  yields `|log Θ|`, not the signed `−|log Θ|`.
* `WeakThetaHullDataActual.lean`: uses the corrected positive hull and keeps
  the comparison `hullLog ≤ qPilotLog` as a Prop; candidate, not proved.
* `PositiveThetaHullLogVolumeActual.lean`: uses
  `positivePointLogVolume := max 0 (−sourceLocalLogDegree)` and an sSup.
  This is a positive-part construction; the `max 0` is itself a zero
  truncation for points where `sourceLocalLogDegree > 0`, and the result is
  not the paper's signed hull log.
* `GlobalPositiveThetaHullLogVolumeActual.lean`: sums
  `−Real.log (thetaValueAt ...)` directly over labels. This is a raw
  theta-value sum, not the actual holomorphic hull volume; it cannot be used as
  the paper hull log.
* `GlobalPositiveHullFromCorrectedActual.lean` and
  `GlobalPositiveHullPaperXiFActual.lean`: reduce paper xi-f to
  `T ≤ Q` where T is the corrected positive hull magnitude and Q the native
  q-pilot magnitude. The reduction direction is right, but T still comes from
  the value-layer corrected hull, not from the paper's unit-normalized global
  hull.
* `PositiveHullVsQPilotCorrectedActual.lean`: same corrected positive
  magnitude; comparison is only a Prop.

`SignedHullLogActual.lean` is a different abstraction: it uses a positive
hull packet with all scales ≥ 1, a unit reference packet with all scales = 1,
and defines `signedHullLogVolume = −hullLogVolume`. It correctly encodes a
signed negative from a positive magnitude and a unit reference, but it is an
abstract structure with no actual source instantiation (`SourceObligations`),
and its `hull_scales_ge_one` hypothesis must be checked against the actual
theta values, which are < 1. It is not final xi-f evidence.

## 7. Bottom line

* Paper: `μ_log` is zero on the unit/integral region, negative for the finite
  theta hull because theta values are < 1; `−|log Θ|` is the negative signed
  scalar, `|log Θ|` its positive magnitude; the target is
  `|log Θ| ≤ |log q|`, equivalently `−|log q| ≤ −|log Θ|`.
* The old zero-truncated `sourceSetVolume` files listed in section 4 cannot be
  used for final xi-f. This includes `GlobalThetaPilotHullLogVolumeActual` and
  therefore `GlobalHullSignedComparisonActual`.
* The Haar ENNReal files in section 5 are conditional on nonnegativity and do
  not represent the finite negative signed hull object.
* The corrected-positive files in section 6 are candidate magnitudes; they may
  support a magnitude comparison `T ≤ Q` only after their positive hull is
  identified with the actual paper magnitude `|log Θ|`. They are not a proof
  of the signed paper statement by themselves.
