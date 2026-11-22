import LeanFormal.IUT.ABCBridge.Geometry.FreyTateAnalyticInput
import LeanFormal.IUT.Foundations.Geometry.TateJInvariantNorm
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The Frey/Tate parameter comparison packet

This module packages the *comparison hypothesis* that relates the candidate
analytic input `q = j⁻¹` of `FreyTateAnalyticInput` to a parameter `qActual` at
which the canonical Tate q-series equation is supposed to model the Frey curve.

Everything here is stated relative to the frozen rational `j`-expression
`abcJInvariant a b c` and Mathlib's actual rational Frey `j`-invariant
(`rationalFreyWeierstrassCurve`), so no new arithmetic input is introduced.

## Contents

* `freyAbcJInvariantAtP` (and its bridge lemmas): the lift to `ℚ_[p]` of
  Mathlib's actual rational Frey `j`-invariant, definitionally equal to
  `((rationalFreyWeierstrassCurve a b).j : ℚ_[p])` and provably equal to the
  `p`-adic cast of `abcJInvariant a b c`.
* `FreyTateQSeriesJInvariant`: Mathlib's Weierstrass `j`-invariant of the
  canonical Tate q-series curve at an arbitrary contracting input `q`, with the
  ellipticity instance supplied by an explicit arithmetic certificate.
* `FreyTateComparisonPacket`: the comparison hypothesis itself.  It carries
  `qActual : ℚ_[p]`, its nonvanishing and strict contraction, an arithmetic
  certificate for `qActual`, a `jTate` together with
  `jTate = FreyTateQSeriesJInvariant qActual certificate` (the Tate q-series
  side), `jTate = freyAbcJInvariantAtP a b c p h` (the Frey side), and the norm
  identity `‖jTate‖ = (‖qActual‖)⁻¹`.
* the logarithmic-volume comparison `-log ‖qActual‖ = log ‖j_Frey‖`, its
  candidate form `-log ‖qActual‖ = -log ‖q^{cand}‖`, and the quantitative bound
  `log 9 ≤ -log ‖qActual‖`;
* `freyTateComparisonResidual` / `freyTateComparisonResidualUnit`: the ratio
  `qActual / q^{cand}` is a norm-one unit, i.e. the sole remaining degree of
  freedom of the comparison.

## What is deliberately NOT claimed

`qActual` carries only the comparison hypothesis.  This module does **not**
prove that `qActual` uniformizes the Frey curve, does not construct an
isomorphism between the canonical Tate q-series curve at `qActual` and the Frey
curve (or any coordinate change of it), and asserts no point uniformization and
no Galois equivariance.  In particular `jTate_norm` is a *field* of the
packet, not a theorem: the exact Tate `j`-norm identity available in this
repository (`TateCurvePadic.tateJInvariant_norm`, module
`Foundations.Geometry.TateJInvariantNorm`) is stated for the canonical
parameter `q l` of a prime label `l : PrimeGeFive`, and the corresponding
`c₄`/`Δ` norm estimates for an arbitrary contracting `q` are not formalized.
The comparison performed below is therefore conditional on the packet, and the
norm-one residual unit records precisely the freedom that remains after it.
-/

namespace LeanFormal.IUT

noncomputable section

open WeierstrassCurve

/-! ## The lifted rational Frey `j`-invariant -/

/-- The image in `ℚ_[p]` of Mathlib's actual rational `j`-invariant of the Frey
model `y² = x (x - a) (x + b)`, evaluated with the ellipticity instance that the
ABC triple `h` supplies on `rationalFreyWeierstrassCurve a b`.

By construction this is the lift `((rationalFreyWeierstrassCurve a b).j : ℚ_[p])`
of a rational number; `freyAbcJInvariantAtP_eq_rationalFreyWeierstrassCurve_j_cast`
records that definitional equality and
`freyAbcJInvariantAtP_eq_abcJInvariant_cast` rewrites it to the explicit
`p`-adic cast of the `j`-expression `abcJInvariant a b c`. -/
def freyAbcJInvariantAtP (a b c p : ℕ) [Fact p.Prime] (h : IsABCTriple a b c) :
    ℚ_[p] :=
  letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
  ((rationalFreyWeierstrassCurve a b).j : ℚ_[p])

/-- The defining equation of `freyAbcJInvariantAtP`: it is definitionally the
lift of the actual rational Frey `j`-invariant. -/
theorem freyAbcJInvariantAtP_eq_rationalFreyWeierstrassCurve_j_cast
    (a b c p : ℕ) [Fact p.Prime] (h : IsABCTriple a b c) :
    freyAbcJInvariantAtP a b c p h =
      letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
      ((rationalFreyWeierstrassCurve a b).j : ℚ_[p]) := rfl

set_option maxHeartbeats 800000 in
-- Raised budget: unfolding the instance-carrying `j`-invariant and unifying the
-- `p`-adic norm expressions is heavier than the default budget allows.
/-- The lifted Frey `j`-invariant is the `p`-adic cast of the rational
`j`-expression `abcJInvariant a b c`. -/
theorem freyAbcJInvariantAtP_eq_abcJInvariant_cast
    (a b c p : ℕ) [Fact p.Prime] (h : IsABCTriple a b c) :
    freyAbcJInvariantAtP a b c p h = (abcJInvariant a b c : ℚ_[p]) := by
  haveI : (rationalFreyWeierstrassCurve a b).IsElliptic :=
    rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
  rw [freyAbcJInvariantAtP]
  exact congrArg (fun x : ℚ => (x : ℚ_[p]))
    (rationalFreyWeierstrassCurve_j_eq_abcJInvariant_of_isABCTriple h)

set_option maxHeartbeats 800000 in
-- Raised budget: unfolding the instance-carrying `j`-invariant and unifying the
-- `p`-adic norm expressions is heavier than the default budget allows.
/-- The candidate Tate input `q = j⁻¹` of `FreyTateAnalyticInput`, rewritten as
the inverse of the lifted Frey `j`-invariant. -/
theorem freyAbcTateCandidateQ_eq_inv_freyAbcJInvariantAtP
    (a b c p : ℕ) [Fact p.Prime] (h : IsABCTriple a b c) :
    freyAbcTateCandidateQ p a b c = (freyAbcJInvariantAtP a b c p h)⁻¹ := by
  rw [freyAbcTateCandidateQ_def, freyAbcJInvariantAtP_eq_abcJInvariant_cast a b c p h]

set_option maxHeartbeats 800000 in
-- Raised budget: unfolding the instance-carrying `j`-invariant and unifying the
-- `p`-adic norm expressions is heavier than the default budget allows.
/-- The norm of the candidate input is the inverse of the norm of the lifted
Frey `j`-invariant; this is the direction `‖j‖ = ‖q‖⁻¹` used by the
log-volume comparison below. -/
theorem freyAbcTateCandidateQ_norm_eq_inv_freyAbcJInvariantAtP_norm
    (a b c p : ℕ) [Fact p.Prime] (h : IsABCTriple a b c) :
    ‖freyAbcTateCandidateQ p a b c‖ = (‖freyAbcJInvariantAtP a b c p h‖)⁻¹ := by
  rw [freyAbcTateCandidateQ_eq_inv_freyAbcJInvariantAtP a b c p h, norm_inv]

/-! ## The Tate q-series `j`-invariant at an arbitrary contracting input -/

/-- Mathlib's Weierstrass `j`-invariant of the canonical Tate q-series curve
`TateCurve.weierstrassCurve ℚ_[p] q`, with the ellipticity instance supplied by
an explicit arithmetic certificate for `q`. -/
noncomputable def FreyTateQSeriesJInvariant (p : ℕ) [Fact p.Prime] (q : ℚ_[p])
    (cert : TateCurve.ArithmeticCertificate (K := ℚ_[p]) q) : ℚ_[p] :=
  letI : (TateCurve.weierstrassCurve ℚ_[p] q).IsElliptic :=
    TateCurve.ArithmeticCertificate.canonical_is_elliptic cert
  (TateCurve.weierstrassCurve ℚ_[p] q).j

/-- The defining equation of `FreyTateQSeriesJInvariant`. -/
theorem FreyTateQSeriesJInvariant_eq (p : ℕ) [Fact p.Prime] (q : ℚ_[p])
    (cert : TateCurve.ArithmeticCertificate (K := ℚ_[p]) q) :
    letI : (TateCurve.weierstrassCurve ℚ_[p] q).IsElliptic :=
      TateCurve.ArithmeticCertificate.canonical_is_elliptic cert
    FreyTateQSeriesJInvariant p q cert = (TateCurve.weierstrassCurve ℚ_[p] q).j :=
  rfl

/-! ## The comparison packet -/

/-- The Frey/Tate comparison hypothesis at an odd prime `p` dividing `a b c`.

The fields `qActual`, `qActual_ne_zero`, `qActual_norm_lt_one`, `certificate`
and `jTate_norm` are the comparison assumptions: `qActual` is a putative Tate
parameter whose q-series equation carries a `j`-invariant of norm
`(‖qActual‖)⁻¹`, and `jTate_eq_qSeriesJInvariant` /
`jTate_eq_freyJInvariant` freeze the `j`-match between the canonical Tate
q-series curve at `qActual` and the lift of Mathlib's actual rational Frey
`j`-invariant.

This structure asserts nothing about uniformization, isomorphism or Galois
equivariance; see the module doc comment. -/
structure FreyTateComparisonPacket (p : ℕ) [Fact p.Prime]
    (a b c : ℕ) (h : IsABCTriple a b c) (hp_two : p ≠ 2) (hdiv : p ∣ a * b * c) where
  /-- The putative Tate parameter. -/
  qActual : ℚ_[p]
  /-- The putative Tate parameter is nonzero. -/
  qActual_ne_zero : qActual ≠ 0
  /-- The putative Tate parameter is strictly contracting. -/
  qActual_norm_lt_one : ‖qActual‖ < 1
  /-- An arithmetic certificate for the canonical q-series equation at
  `qActual`; this is what makes the q-series `j`-invariant available. -/
  certificate : TateCurve.ArithmeticCertificate (K := ℚ_[p]) qActual
  /-- The `j`-invariant attached to the comparison. -/
  jTate : ℚ_[p]
  /-- The `j`-match on the Tate side: `jTate` is the q-series `j` at `qActual`. -/
  jTate_eq_qSeriesJInvariant : jTate = FreyTateQSeriesJInvariant p qActual certificate
  /-- The `j`-match on the Frey side: `jTate` is the lift of the rational Frey
  `j`-invariant. -/
  jTate_eq_freyJInvariant : jTate = freyAbcJInvariantAtP a b c p h
  /-- The comparison norm identity `‖jTate‖ = (‖qActual‖)⁻¹`. -/
  jTate_norm : ‖jTate‖ = (‖qActual‖)⁻¹

/-- The `j`-match of the packet, stated directly between the canonical Tate
q-series `j` at `qActual` and the lift of the rational Frey `j`-invariant. -/
theorem freyTateComparisonPacket_qSeriesJInvariant_eq_freyJInvariant
    (p : ℕ) [Fact p.Prime] (a b c : ℕ) (h : IsABCTriple a b c)
    (hp_two : p ≠ 2) (hdiv : p ∣ a * b * c)
    (P : FreyTateComparisonPacket p a b c h hp_two hdiv) :
    FreyTateQSeriesJInvariant p P.qActual P.certificate =
      freyAbcJInvariantAtP a b c p h := by
  rw [← P.jTate_eq_qSeriesJInvariant, P.jTate_eq_freyJInvariant]

/-! ## (b) The logarithmic-volume comparison -/

/-- The logarithmic volume `-log ‖qActual‖` of the comparison parameter. -/
noncomputable def freyTateQActualLogVolume
    (p : ℕ) [Fact p.Prime] (a b c : ℕ) (h : IsABCTriple a b c)
    (hp_two : p ≠ 2) (hdiv : p ∣ a * b * c)
    (P : FreyTateComparisonPacket p a b c h hp_two hdiv) : ℝ :=
  -Real.log ‖P.qActual‖

/-- The logarithmic norm `log ‖j_Frey‖` of the lifted rational Frey
`j`-invariant. -/
noncomputable def freyTateFreyJLogVolume
    (a b c p : ℕ) [Fact p.Prime] (h : IsABCTriple a b c) : ℝ :=
  Real.log ‖freyAbcJInvariantAtP a b c p h‖

/-- The logarithmic volume `-log ‖q^{cand}‖` of the candidate input
`q = j⁻¹` of `FreyTateAnalyticInput`. -/
noncomputable def freyAbcCandidateQLogVolume (p a b c : ℕ) [Fact p.Prime] : ℝ :=
  -Real.log ‖freyAbcTateCandidateQ p a b c‖

@[simp] theorem freyTateQActualLogVolume_eq
    (p : ℕ) [Fact p.Prime] (a b c : ℕ) (h : IsABCTriple a b c)
    (hp_two : p ≠ 2) (hdiv : p ∣ a * b * c)
    (P : FreyTateComparisonPacket p a b c h hp_two hdiv) :
    freyTateQActualLogVolume p a b c h hp_two hdiv P = -Real.log ‖P.qActual‖ := rfl

@[simp] theorem freyTateFreyJLogVolume_eq
    (a b c p : ℕ) [Fact p.Prime] (h : IsABCTriple a b c) :
    freyTateFreyJLogVolume a b c p h = Real.log ‖freyAbcJInvariantAtP a b c p h‖ :=
  rfl

@[simp] theorem freyAbcCandidateQLogVolume_eq
    (p a b c : ℕ) [Fact p.Prime] :
    freyAbcCandidateQLogVolume p a b c = -Real.log ‖freyAbcTateCandidateQ p a b c‖ :=
  rfl

/-- The log-norm of `jTate` is the log-norm of the lifted Frey `j`-invariant. -/
theorem freyTateComparisonPacket_jTateLogVolume_eq_freyJLogVolume
    (p : ℕ) [Fact p.Prime] (a b c : ℕ) (h : IsABCTriple a b c)
    (hp_two : p ≠ 2) (hdiv : p ∣ a * b * c)
    (P : FreyTateComparisonPacket p a b c h hp_two hdiv) :
    Real.log ‖P.jTate‖ = Real.log ‖freyAbcJInvariantAtP a b c p h‖ := by
  rw [P.jTate_eq_freyJInvariant]

set_option maxHeartbeats 800000 in
-- Raised budget: unfolding the instance-carrying `j`-invariant and unifying the
-- `p`-adic norm expressions is heavier than the default budget allows.
/-- **(b) the log-volume comparison.**  Under the packet hypotheses the
log-volume `-log ‖qActual‖` of the comparison parameter equals the log-norm
`log ‖j_Frey‖` of the lift of Mathlib's actual rational Frey `j`-invariant.

Note the direction: the packet supplies `‖jTate‖ = (‖qActual‖)⁻¹`, so
`-log ‖qActual‖ = log ‖jTate‖ = log ‖j_Frey‖`. -/
theorem freyTateComparisonPacket_qActualLogVolume_eq_freyJLogVolume
    (p : ℕ) [Fact p.Prime] (a b c : ℕ) (h : IsABCTriple a b c)
    (hp_two : p ≠ 2) (hdiv : p ∣ a * b * c)
    (P : FreyTateComparisonPacket p a b c h hp_two hdiv) :
    -Real.log ‖P.qActual‖ = Real.log ‖freyAbcJInvariantAtP a b c p h‖ := by
  calc -Real.log ‖P.qActual‖ = Real.log (‖P.qActual‖)⁻¹ := (Real.log_inv _).symm
    _ = Real.log ‖P.jTate‖ := by rw [P.jTate_norm]
    _ = Real.log ‖freyAbcJInvariantAtP a b c p h‖ := by
          rw [P.jTate_eq_freyJInvariant]

set_option maxHeartbeats 800000 in
-- Raised budget: unfolding the instance-carrying `j`-invariant and unifying the
-- `p`-adic norm expressions is heavier than the default budget allows.
/-- **(b), explicit rational form.**  The same comparison with the Frey side
written as the `ℚ_[p]`-lift of `(rationalFreyWeierstrassCurve a b).j`; this is
the shape requested by the task statement. -/
theorem freyTateComparisonPacket_qActualLogVolume_eq_rationalFreyJCastLogVolume
    (p : ℕ) [Fact p.Prime] (a b c : ℕ) (h : IsABCTriple a b c)
    (hp_two : p ≠ 2) (hdiv : p ∣ a * b * c)
    (P : FreyTateComparisonPacket p a b c h hp_two hdiv) :
    -Real.log ‖P.qActual‖ =
      letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
      Real.log ‖((rationalFreyWeierstrassCurve a b).j : ℚ_[p])‖ := by
  rw [freyTateComparisonPacket_qActualLogVolume_eq_freyJLogVolume p a b c h hp_two hdiv P]
  exact congrArg Real.log (congrArg (fun z : ℚ_[p] => ‖z‖)
    (freyAbcJInvariantAtP_eq_rationalFreyWeierstrassCurve_j_cast a b c p h))

set_option maxHeartbeats 800000 in
-- Raised budget: unfolding the instance-carrying `j`-invariant and unifying the
-- `p`-adic norm expressions is heavier than the default budget allows.
/-- **(b) candidate consistency.**  The log-volume of the comparison parameter
equals the log-volume of the candidate input `q = j⁻¹` of
`FreyTateAnalyticInput`. -/
theorem freyTateComparisonPacket_qActualLogVolume_eq_candidateLogVolume
    (p : ℕ) [Fact p.Prime] (a b c : ℕ) (h : IsABCTriple a b c)
    (hp_two : p ≠ 2) (hdiv : p ∣ a * b * c)
    (P : FreyTateComparisonPacket p a b c h hp_two hdiv) :
    -Real.log ‖P.qActual‖ = -Real.log ‖freyAbcTateCandidateQ p a b c‖ := by
  rw [freyTateComparisonPacket_qActualLogVolume_eq_freyJLogVolume p a b c h hp_two hdiv P,
    freyAbcTateCandidateQ_norm_eq_inv_freyAbcJInvariantAtP_norm a b c p h, Real.log_inv]
  ring

set_option maxHeartbeats 800000 in
-- Raised budget: unfolding the instance-carrying `j`-invariant and unifying the
-- `p`-adic norm expressions is heavier than the default budget allows.
/-- A quantitative consequence: the explicit bound `‖q^{cand}‖ ≤ 1/9` of
`FreyTateAnalyticInput` transfers to the comparison parameter, so its
log-volume is at least `log 9`. -/
theorem freyTateComparisonPacket_log_nine_le_qActualLogVolume
    (p : ℕ) [Fact p.Prime] (a b c : ℕ) (h : IsABCTriple a b c)
    (hp_two : p ≠ 2) (hdiv : p ∣ a * b * c)
    (P : FreyTateComparisonPacket p a b c h hp_two hdiv) :
    Real.log 9 ≤ -Real.log ‖P.qActual‖ := by
  rw [freyTateComparisonPacket_qActualLogVolume_eq_candidateLogVolume p a b c h hp_two hdiv P]
  have hle := freyAbcTateCandidateQ_norm_le_invNine (p := p) h hp_two hdiv
  have hpos : 0 < ‖freyAbcTateCandidateQ p a b c‖ :=
    norm_pos_iff.mpr (freyAbcTateCandidateQ_ne_zero (p := p) h hp_two hdiv)
  have hlog : Real.log ‖freyAbcTateCandidateQ p a b c‖ ≤ Real.log (1 / 9 : ℝ) :=
    Real.log_le_log hpos hle
  have h9 : Real.log (1 / 9 : ℝ) = -Real.log 9 := by
    rw [one_div, Real.log_inv]
  linarith

/-! ## (c) The norm-one residual unit -/

/-- **(c)** The ratio of the comparison parameter to the candidate input
`q = j⁻¹`: this is the only remaining degree of freedom of the comparison. -/
noncomputable def freyTateComparisonResidual
    (p : ℕ) [Fact p.Prime] (a b c : ℕ) (h : IsABCTriple a b c)
    (hp_two : p ≠ 2) (hdiv : p ∣ a * b * c)
    (P : FreyTateComparisonPacket p a b c h hp_two hdiv) : ℚ_[p] :=
  P.qActual / freyAbcTateCandidateQ p a b c

set_option maxHeartbeats 800000 in
-- Raised budget: unfolding the instance-carrying `j`-invariant and unifying the
-- `p`-adic norm expressions is heavier than the default budget allows.
/-- **(c)** The residual ratio has norm one. -/
theorem freyTateComparisonResidual_norm_one
    (p : ℕ) [Fact p.Prime] (a b c : ℕ) (h : IsABCTriple a b c)
    (hp_two : p ≠ 2) (hdiv : p ∣ a * b * c)
    (P : FreyTateComparisonPacket p a b c h hp_two hdiv) :
    ‖freyTateComparisonResidual p a b c h hp_two hdiv P‖ = 1 := by
  have hcand : ‖freyAbcTateCandidateQ p a b c‖ = (‖freyAbcJInvariantAtP a b c p h‖)⁻¹ :=
    freyAbcTateCandidateQ_norm_eq_inv_freyAbcJInvariantAtP_norm a b c p h
  have hqnorm : ‖P.qActual‖ = ‖freyAbcTateCandidateQ p a b c‖ := by
    calc ‖P.qActual‖ = (‖P.jTate‖)⁻¹ := by rw [P.jTate_norm, inv_inv]
      _ = (‖freyAbcJInvariantAtP a b c p h‖)⁻¹ := by rw [P.jTate_eq_freyJInvariant]
      _ = ‖freyAbcTateCandidateQ p a b c‖ := hcand.symm
  have hne : ‖freyAbcTateCandidateQ p a b c‖ ≠ 0 :=
    ne_of_gt (norm_pos_iff.mpr (freyAbcTateCandidateQ_ne_zero (p := p) h hp_two hdiv))
  rw [freyTateComparisonResidual, norm_div, hqnorm, div_self hne]

/-- **(c)** The residual ratio as a genuine unit of `ℚ_[p]`, with norm one. -/
noncomputable def freyTateComparisonResidualUnit
    (p : ℕ) [Fact p.Prime] (a b c : ℕ) (h : IsABCTriple a b c)
    (hp_two : p ≠ 2) (hdiv : p ∣ a * b * c)
    (P : FreyTateComparisonPacket p a b c h hp_two hdiv) : ℚ_[p]ˣ :=
  Units.mk0 (freyTateComparisonResidual p a b c h hp_two hdiv P) (by
    intro hzero
    have hone := freyTateComparisonResidual_norm_one p a b c h hp_two hdiv P
    rw [hzero, norm_zero] at hone
    norm_num at hone)

@[simp] theorem freyTateComparisonResidualUnit_coe
    (p : ℕ) [Fact p.Prime] (a b c : ℕ) (h : IsABCTriple a b c)
    (hp_two : p ≠ 2) (hdiv : p ∣ a * b * c)
    (P : FreyTateComparisonPacket p a b c h hp_two hdiv) :
    ((freyTateComparisonResidualUnit p a b c h hp_two hdiv P : ℚ_[p])) =
      freyTateComparisonResidual p a b c h hp_two hdiv P := rfl

/-- **(c)** The residual unit has norm one. -/
theorem freyTateComparisonResidualUnit_norm_one
    (p : ℕ) [Fact p.Prime] (a b c : ℕ) (h : IsABCTriple a b c)
    (hp_two : p ≠ 2) (hdiv : p ∣ a * b * c)
    (P : FreyTateComparisonPacket p a b c h hp_two hdiv) :
    ‖((freyTateComparisonResidualUnit p a b c h hp_two hdiv P : ℚ_[p]))‖ = 1 := by
  rw [freyTateComparisonResidualUnit_coe,
    freyTateComparisonResidual_norm_one p a b c h hp_two hdiv P]

/-! ## Summary -/

/-- The comparison output of the packet: the `j`-match, the log-volume
identity in both forms, and the norm-one residual unit. -/
theorem freyTateComparisonPacket_summary
    (p : ℕ) [Fact p.Prime] (a b c : ℕ) (h : IsABCTriple a b c)
    (hp_two : p ≠ 2) (hdiv : p ∣ a * b * c)
    (P : FreyTateComparisonPacket p a b c h hp_two hdiv) :
    FreyTateQSeriesJInvariant p P.qActual P.certificate =
        freyAbcJInvariantAtP a b c p h ∧
      -Real.log ‖P.qActual‖ = Real.log ‖freyAbcJInvariantAtP a b c p h‖ ∧
      -Real.log ‖P.qActual‖ = -Real.log ‖freyAbcTateCandidateQ p a b c‖ ∧
      Real.log 9 ≤ -Real.log ‖P.qActual‖ ∧
      ‖freyTateComparisonResidual p a b c h hp_two hdiv P‖ = 1 :=
  ⟨freyTateComparisonPacket_qSeriesJInvariant_eq_freyJInvariant p a b c h hp_two hdiv P,
    freyTateComparisonPacket_qActualLogVolume_eq_freyJLogVolume p a b c h hp_two hdiv P,
    freyTateComparisonPacket_qActualLogVolume_eq_candidateLogVolume p a b c h hp_two hdiv P,
    freyTateComparisonPacket_log_nine_le_qActualLogVolume p a b c h hp_two hdiv P,
    freyTateComparisonResidual_norm_one p a b c h hp_two hdiv P⟩

end

end LeanFormal.IUT
