import LeanFormal.IUT.ABCBridge.Arithmetic.ABCInvariantLocalValuations
import LeanFormal.IUT.ABCBridge.Arithmetic.ABCNonemptyOddBadSupport
import LeanFormal.IUT.ABCBridge.Geometry.FreyWeierstrassCurve
import LeanFormal.IUT.Foundations.Geometry.TateCurveArithmetic
import LeanFormal.IUT.Foundations.Geometry.TateUniformizationContract
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Tactic

/-!
# The Frey `j`-inverse as candidate analytic input for the Tate q-series interfaces

For an ABC triple `a + b = c`, Mathlib's actual `j`-invariant of the associated
Frey curve `y² = x (x - a) (x + b)` equals the rational expression
`256 (a² + a b + b²)³ / (a² b² c²)`; this is proved in
`LeanFormal.IUT.rationalFreyWeierstrassCurve_j_of_isABCTriple` and converted
below, by unfolding the two definitions involved, into the bridge
`rationalFreyWeierstrassCurve_j_eq_abcJInvariant_of_isABCTriple` with the
rational `j`-expression `abcJInvariant a b c`.

This module connects that actual `j` to the *analytic-input side* of the
formalized Tate q-series and completion interfaces:

* At each odd prime `p` in the bad support of the triple, i.e. `p ≠ 2` and
  `p ∣ a b c` (equivalently, by
  `IsABCTriple.prime_ne_two_dvd_abcJInvariant_den_iff`, `p` divides the reduced
  denominator of `j`), the actual valuation data forces `‖j‖_p > 1` and
  `‖j⁻¹‖_p < 1`, both for Mathlib's rational norm `padicNorm` and for the norm
  on `ℚ_[p]`.  The statements below take the explicit condition `p ≠ 2`,
  `p ∣ a b c` directly; the completion-side statements are additionally
  provided in the membership form `p ∈ abcOddBadPrimeSupport a b c`, which
  unfolds to `Nat.Prime p ∧ p ≠ 2 ∧ p ∣ a * b * c`
  (`IsABCTriple.mem_abcOddBadPrimeSupport_iff`).
* Consequently the candidate input `q := j⁻¹` satisfies the honest analytic
  hypotheses that the existing Tate q-series infrastructure imposes on an input
  parameter: `q ≠ 0`, `q ≠ 1`, `‖q‖ < 1`, contraction of positive powers,
  nonvanishing of the Lambert denominators `1 - qⁿ`, and Lambert-series
  summability via `LeanFormal.IUT.TateCurve.lambertSeries_summable`.  The
  canonical q-series curve `LeanFormal.IUT.TateCurve.weierstrassCurve ℚ_[p] q`
  is available at `q := j⁻¹`.
* The canonical q-series curve at `q := j⁻¹` is nondegenerate: `Δ ≠ 0`, it is
  an elliptic curve (`IsElliptic`), and the full arithmetic certificate
  `TateCurve.ArithmeticCertificate q` at `q := j⁻¹` is produced; see
  `freyAbcTateCandidateQ_arithmeticCertificate` and the surrounding lemmas.
* On the completion side, the rational finite place at `p` is constructed
  (`rationalFinitePlace`), its completion is identified with `ℚ_[p]` by the
  canonical `ℚ`-algebra equivalence `rationalFinitePlacePadicEquiv`, and the
  unit hypothesis of
  `LeanFormal.IUT.NumberFieldFinitePlace.tateParameterUnit` is instantiated at
  the image of `j⁻¹` under the canonical embedding: the unit
  `freyAbcTateCandidateQUnit` is a genuine `tateParameterUnit`, and
  `freyAbcTateCandidateQUnit_ne_one` is the instantiated
  `tateParameterUnit_ne_one`.  The candidate is strictly contracting in the
  completion as well: `Valued.v (j⁻¹) < 1` at the rational place
  (`freyAbcTateCandidateQAtRationalCompletion_valued_lt_one`) and its norm form
  `‖j⁻¹‖ < 1` for the canonical normed-field structure of the adic completion;
  hence `j⁻¹` is a `NumberFieldFinitePlace.FinitePlaceQCandidate` at the
  rational place (`freyAbcTateCandidateQFinitePlaceCandidate`).

## What is deliberately NOT claimed

This module does **not** prove, and must not be read as proving, that `q = j⁻¹`
is the genuine Tate parameter of the Frey curve, nor that the canonical Tate
q-series curve at `q = j⁻¹` is isomorphic to (a coordinate change of) the Frey
curve, nor any point uniformization or Galois equivariance statement.  Precisely
those are the missing C-layer obligations recorded in
`LeanFormal.IUT.CurveIndexedTateUniformization` and
`LeanFormal.IUT.SourceLocalTateBoundary`; no field of either structure is
populated here.  The only structure built from `j⁻¹` below is the
valuation-theoretic `FinitePlaceQCandidate` at the rational place
(`freyAbcTateCandidateQFinitePlaceCandidate`), which by construction asserts
nothing beyond nonvanishing and strict contraction; no comparison with an IUT
theta construction is asserted.

The arithmetic certificate at `q := j⁻¹` is produced below (see
`freyAbcTateCandidateQ_arithmeticCertificate`), so the expansion-criterion gap
recorded earlier is closed; what continues to be not claimed is any
identification of `q = j⁻¹` with the Frey Tate parameter (see above).  The
precise gap left open here:

* The completion-side contraction is now produced: `Valued.v (j⁻¹) < 1`, its
  norm form `‖j⁻¹‖ < 1`, and the `FinitePlaceQCandidate` at the rational place.
  What remains deliberately open is curve-level content: no uniformization of
  the Frey curve, no identification of `q = j⁻¹` with a Tate parameter, and no
  point comparison.
-/

namespace LeanFormal.IUT

noncomputable section

variable {a b c p : ℕ} [Fact p.Prime]

/-! ### `p`-adic norms of rationals from valuations -/

/-- A rational with negative `p`-adic valuation has `p`-adic norm strictly
greater than one. -/
theorem one_lt_padicNorm_of_padicValRat_neg {q : ℚ} (hv : padicValRat p q < 0) :
    1 < padicNorm p q := by
  have hq : q ≠ 0 := by
    intro hzero
    rw [hzero, padicValRat.zero] at hv
    exact lt_irrefl 0 hv
  have hp_one : (1 : ℚ) < (p : ℚ) := by
    exact_mod_cast (Fact.out : p.Prime).one_lt
  rw [padicNorm.eq_zpow_of_nonzero hq,
    show (1 : ℚ) = (p : ℚ) ^ (0 : ℤ) by simp]
  exact (zpow_lt_zpow_iff_right₀ hp_one).mpr (by omega)

/-- The inverse of a rational with negative `p`-adic valuation has `p`-adic norm
strictly less than one; this is exactly the contraction condition imposed by the
Tate q-series interfaces. -/
theorem padicNorm_inv_lt_one_of_padicValRat_neg {q : ℚ} (hv : padicValRat p q < 0) :
    padicNorm p q⁻¹ < 1 := by
  have hq : q ≠ 0 := by
    intro hzero
    rw [hzero, padicValRat.zero] at hv
    exact lt_irrefl 0 hv
  have hp_one : (1 : ℚ) < (p : ℚ) := by
    exact_mod_cast (Fact.out : p.Prime).one_lt
  rw [padicNorm.eq_zpow_of_nonzero (inv_ne_zero hq), padicValRat.inv, neg_neg,
    show (1 : ℚ) = (p : ℚ) ^ (0 : ℤ) by simp]
  exact (zpow_lt_zpow_iff_right₀ hp_one).mpr hv

/-- Mathlib's norm on `ℚ_[p]` restricts to `padicNorm` on the image of `ℚ`. -/
theorem norm_ratCast_eq_padicNorm (q : ℚ) :
    ‖(q : ℚ_[p])‖ = (padicNorm p q : ℝ) :=
  Padic.eq_padicNorm q

/-! ### The actual Frey `j` at an odd bad prime

The odd part of the bad support is the condition `p ≠ 2`, `p ∣ a b c`; all
statements below take this condition directly. -/

/-- An odd prime dividing `a b c` gives the negative `p`-adic valuation of the
rational Frey `j`-expression. -/
theorem abcJInvariant_padicValRat_neg_of_prime_ne_two_dvd_product
    (h : IsABCTriple a b c) (hp_two : p ≠ 2) (hdiv : p ∣ a * b * c) :
    padicValRat p (abcJInvariant a b c) < 0 :=
  h.abcJInvariant_padicValRat_neg_iff.mpr (Or.inl ⟨hp_two, hdiv⟩)

/-- At an odd bad prime the rational Frey `j`-expression has `p`-adic norm
greater than one. -/
theorem abcJInvariant_padicNorm_gt_one_of_prime_ne_two_dvd_product
    (h : IsABCTriple a b c) (hp_two : p ≠ 2) (hdiv : p ∣ a * b * c) :
    1 < padicNorm p (abcJInvariant a b c) :=
  one_lt_padicNorm_of_padicValRat_neg
    (abcJInvariant_padicValRat_neg_of_prime_ne_two_dvd_product h hp_two hdiv)

/-- At an odd bad prime the inverse of the rational Frey `j`-expression has
`p`-adic norm strictly less than one. -/
theorem abcJInvariant_padicNorm_inv_lt_one_of_prime_ne_two_dvd_product
    (h : IsABCTriple a b c) (hp_two : p ≠ 2) (hdiv : p ∣ a * b * c) :
    padicNorm p (abcJInvariant a b c)⁻¹ < 1 :=
  padicNorm_inv_lt_one_of_padicValRat_neg
    (abcJInvariant_padicValRat_neg_of_prime_ne_two_dvd_product h hp_two hdiv)

/-- The rational Frey `j`-expression is nonzero at an odd bad prime. -/
theorem abcJInvariant_ne_zero_of_prime_ne_two_dvd_product
    (h : IsABCTriple a b c) (hp_two : p ≠ 2) (hdiv : p ∣ a * b * c) :
    abcJInvariant a b c ≠ 0 := by
  intro hzero
  have hv := abcJInvariant_padicValRat_neg_of_prime_ne_two_dvd_product h hp_two hdiv
  rw [hzero, padicValRat.zero] at hv
  exact lt_irrefl 0 hv

/-- The rational Frey `j`-expression is never one at an odd bad prime. -/
theorem abcJInvariant_ne_one_of_prime_ne_two_dvd_product
    (h : IsABCTriple a b c) (hp_two : p ≠ 2) (hdiv : p ∣ a * b * c) :
    abcJInvariant a b c ≠ 1 := by
  intro hone
  have hgt := abcJInvariant_padicNorm_gt_one_of_prime_ne_two_dvd_product h hp_two hdiv
  rw [hone] at hgt
  simp at hgt

/-- At an odd bad prime the odd prime divides the reduced denominator of the
rational Frey `j`-expression. -/
theorem abcJInvariant_den_dvd_of_prime_ne_two_dvd_product
    (h : IsABCTriple a b c) (hp_two : p ≠ 2) (hdiv : p ∣ a * b * c) :
    p ∣ (abcJInvariant a b c).den :=
  (h.prime_ne_two_dvd_abcJInvariant_den_iff hp_two).mpr hdiv

/-- At an odd bad prime the rational Frey `j`-expression, viewed in `ℚ_[p]`, has
norm greater than one. -/
theorem abcJInvariant_cast_norm_gt_one_of_prime_ne_two_dvd_product
    (h : IsABCTriple a b c) (hp_two : p ≠ 2) (hdiv : p ∣ a * b * c) :
    1 < ‖((abcJInvariant a b c : ℚ_[p]))‖ := by
  rw [norm_ratCast_eq_padicNorm]
  exact_mod_cast abcJInvariant_padicNorm_gt_one_of_prime_ne_two_dvd_product h hp_two hdiv

/-- At an odd bad prime the inverse of the rational Frey `j`-expression, viewed
in `ℚ_[p]`, has norm strictly less than one. -/
theorem abcJInvariant_cast_inv_norm_lt_one_of_prime_ne_two_dvd_product
    (h : IsABCTriple a b c) (hp_two : p ≠ 2) (hdiv : p ∣ a * b * c) :
    ‖((abcJInvariant a b c : ℚ_[p]))⁻¹‖ < 1 := by
  rw [norm_inv]
  exact inv_lt_one_of_one_lt₀
    (abcJInvariant_cast_norm_gt_one_of_prime_ne_two_dvd_product h hp_two hdiv)

/-- The rational Frey `j`-expression is nonzero in `ℚ_[p]` at an odd bad
prime. -/
theorem abcJInvariant_cast_ne_zero_of_prime_ne_two_dvd_product
    (h : IsABCTriple a b c) (hp_two : p ≠ 2) (hdiv : p ∣ a * b * c) :
    ((abcJInvariant a b c : ℚ_[p])) ≠ 0 := by
  intro hzero
  have hgt := abcJInvariant_cast_norm_gt_one_of_prime_ne_two_dvd_product h hp_two hdiv
  rw [hzero, norm_zero] at hgt
  exact absurd hgt (by norm_num)

/-! ### The bridge to Mathlib's actual `j`-invariant -/

/-- The actual Mathlib `j`-invariant of the rational Frey model equals the
rational `j`-expression `abcJInvariant a b c`; proved by unfolding both sides
of the explicit formula `rationalFreyWeierstrassCurve_j_of_isABCTriple`. -/
theorem rationalFreyWeierstrassCurve_j_eq_abcJInvariant_of_isABCTriple
    {a b c : ℕ} (h : IsABCTriple a b c) :
    letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
    (rationalFreyWeierstrassCurve a b).j = abcJInvariant a b c := by
  letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
  rw [rationalFreyWeierstrassCurve_j_of_isABCTriple h]
  unfold abcJInvariant abcInvariantNumerator abcInvariantPolynomial abcInvariantDenominator
  push_cast
  ring

/-- The actual Mathlib `j`-invariant of the rational Frey model has negative
`p`-adic valuation at an odd bad prime. -/
theorem rationalFreyWeierstrassCurve_j_padicValRat_neg_of_prime_ne_two_dvd_product
    (h : IsABCTriple a b c) (hp_two : p ≠ 2) (hdiv : p ∣ a * b * c) :
    letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
    padicValRat p (rationalFreyWeierstrassCurve a b).j < 0 := by
  letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
  rw [rationalFreyWeierstrassCurve_j_eq_abcJInvariant_of_isABCTriple h]
  exact abcJInvariant_padicValRat_neg_of_prime_ne_two_dvd_product h hp_two hdiv

/-- The actual Mathlib `j`-invariant of the rational Frey model has `p`-adic
norm greater than one at an odd bad prime. -/
theorem rationalFreyWeierstrassCurve_j_padicNorm_gt_one_of_prime_ne_two_dvd_product
    (h : IsABCTriple a b c) (hp_two : p ≠ 2) (hdiv : p ∣ a * b * c) :
    letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
    1 < padicNorm p (rationalFreyWeierstrassCurve a b).j := by
  letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
  rw [rationalFreyWeierstrassCurve_j_eq_abcJInvariant_of_isABCTriple h]
  exact abcJInvariant_padicNorm_gt_one_of_prime_ne_two_dvd_product h hp_two hdiv

/-- The actual Mathlib `j`-invariant of the rational Frey model, viewed in
`ℚ_[p]`, has norm greater than one at an odd bad prime. -/
theorem rationalFreyWeierstrassCurve_j_cast_norm_gt_one_of_prime_ne_two_dvd_product
    (h : IsABCTriple a b c) (hp_two : p ≠ 2) (hdiv : p ∣ a * b * c) :
    letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
    1 < ‖(((rationalFreyWeierstrassCurve a b).j : ℚ) : ℚ_[p])‖ := by
  letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
  rw [rationalFreyWeierstrassCurve_j_eq_abcJInvariant_of_isABCTriple h]
  exact abcJInvariant_cast_norm_gt_one_of_prime_ne_two_dvd_product h hp_two hdiv

/-- The inverse of the actual Mathlib `j`-invariant of the rational Frey model,
viewed in `ℚ_[p]`, has norm strictly less than one at an odd bad prime. -/
theorem rationalFreyWeierstrassCurve_j_cast_inv_norm_lt_one_of_prime_ne_two_dvd_product
    (h : IsABCTriple a b c) (hp_two : p ≠ 2) (hdiv : p ∣ a * b * c) :
    letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
    ‖(((rationalFreyWeierstrassCurve a b).j : ℚ) : ℚ_[p])⁻¹‖ < 1 := by
  letI := rationalFreyWeierstrassCurve_isElliptic_of_isABCTriple h
  rw [rationalFreyWeierstrassCurve_j_eq_abcJInvariant_of_isABCTriple h]
  exact abcJInvariant_cast_inv_norm_lt_one_of_prime_ne_two_dvd_product h hp_two hdiv

/-! ### The candidate analytic input `q := j⁻¹`

The declarations below instantiate the honest analytic hypotheses of the Tate
q-series interfaces at `q := j⁻¹`.  They do not identify `q` with a Tate
parameter; see the module doc comment. -/

/-- The candidate analytic input `q := j⁻¹` attached to the actual Frey
`j`-invariant at a prime `p`, as an element of `ℚ_[p]`.  This element is the
subject of the analytic-input statements below; it is **not** claimed to be the
genuine Tate parameter of the Frey curve. -/
def freyAbcTateCandidateQ (p a b c : ℕ) [Fact p.Prime] : ℚ_[p] :=
  ((abcJInvariant a b c : ℚ_[p]))⁻¹

@[simp] theorem freyAbcTateCandidateQ_def (p a b c : ℕ) [Fact p.Prime] :
    freyAbcTateCandidateQ p a b c = ((abcJInvariant a b c : ℚ_[p]))⁻¹ := rfl

/-- The candidate input `q := j⁻¹` is nonzero: the first analytic hypothesis of
the Tate interfaces (`tateParameterUnit` needs exactly `q ≠ 0`). -/
theorem freyAbcTateCandidateQ_ne_zero
    (h : IsABCTriple a b c) (hp_two : p ≠ 2) (hdiv : p ∣ a * b * c) :
    freyAbcTateCandidateQ p a b c ≠ 0 := by
  rw [freyAbcTateCandidateQ_def]
  exact inv_ne_zero (abcJInvariant_cast_ne_zero_of_prime_ne_two_dvd_product h hp_two hdiv)

/-- The candidate input `q := j⁻¹` satisfies the contraction hypothesis
`‖q‖ < 1` of the Tate q-series interfaces. -/
theorem freyAbcTateCandidateQ_norm_lt_one
    (h : IsABCTriple a b c) (hp_two : p ≠ 2) (hdiv : p ∣ a * b * c) :
    ‖freyAbcTateCandidateQ p a b c‖ < 1 := by
  rw [freyAbcTateCandidateQ_def]
  exact abcJInvariant_cast_inv_norm_lt_one_of_prime_ne_two_dvd_product h hp_two hdiv

/-- The candidate input `q := j⁻¹` is not one: the hypothesis of
`NumberFieldFinitePlace.tateParameterUnit_ne_one`, via
`TateCurve.q_ne_one_of_norm_lt_one`. -/
theorem freyAbcTateCandidateQ_ne_one
    (h : IsABCTriple a b c) (hp_two : p ≠ 2) (hdiv : p ∣ a * b * c) :
    freyAbcTateCandidateQ p a b c ≠ 1 :=
  TateCurve.q_ne_one_of_norm_lt_one (freyAbcTateCandidateQ_norm_lt_one h hp_two hdiv)

/-- Powers of the candidate input `q := j⁻¹` are nonzero. -/
theorem freyAbcTateCandidateQ_pow_ne_zero
    (h : IsABCTriple a b c) (hp_two : p ≠ 2) (hdiv : p ∣ a * b * c) (n : ℕ) :
    freyAbcTateCandidateQ p a b c ^ n ≠ 0 :=
  TateCurve.q_power_ne_zero (freyAbcTateCandidateQ_norm_lt_one h hp_two hdiv) n
    (freyAbcTateCandidateQ_ne_zero h hp_two hdiv)

/-- Positive powers of the candidate input `q := j⁻¹` stay strictly contracted;
this is the power form of the Tate q-series hypothesis. -/
theorem freyAbcTateCandidateQ_pow_norm_lt_one
    (h : IsABCTriple a b c) (hp_two : p ≠ 2) (hdiv : p ∣ a * b * c) (n : ℕ)
    (hn : 0 < n) :
    ‖freyAbcTateCandidateQ p a b c ^ n‖ < 1 :=
  TateCurve.q_power_norm_lt_one (freyAbcTateCandidateQ_norm_lt_one h hp_two hdiv) n hn

/-- Positive powers of the candidate input `q := j⁻¹` are not one, so that the
Lambert denominators `1 - qⁿ` are nonzero. -/
theorem freyAbcTateCandidateQ_pow_ne_one
    (h : IsABCTriple a b c) (hp_two : p ≠ 2) (hdiv : p ∣ a * b * c) (n : ℕ)
    (hn : 0 < n) :
    freyAbcTateCandidateQ p a b c ^ n ≠ 1 :=
  TateCurve.q_power_ne_one (freyAbcTateCandidateQ_norm_lt_one h hp_two hdiv) n hn

/-- The Lambert denominators at the candidate parameter are nonzero. -/
theorem freyAbcTateCandidateQ_one_sub_pow_ne_zero
    (h : IsABCTriple a b c) (hp_two : p ≠ 2) (hdiv : p ∣ a * b * c) (n : ℕ)
    (hn : 0 < n) :
    1 - freyAbcTateCandidateQ p a b c ^ n ≠ 0 :=
  TateCurve.one_sub_q_power_ne_zero (freyAbcTateCandidateQ_norm_lt_one h hp_two hdiv) n hn

/-- The Tate-series interface `TateCurve.lambertSeries_summable` accepts
`q := j⁻¹` as analytic input: every Lambert series of the candidate parameter is
summable.  This instantiates only the contraction hypothesis `‖q‖ < 1`; it is
not a uniformization statement. -/
theorem freyAbcTateCandidateQ_lambertSeries_summable
    (h : IsABCTriple a b c) (hp_two : p ≠ 2) (hdiv : p ∣ a * b * c) (weight : ℕ) :
    Summable (fun n : ℕ ↦
      (n : ℚ_[p]) ^ weight * freyAbcTateCandidateQ p a b c ^ n /
        (1 - freyAbcTateCandidateQ p a b c ^ n)) :=
  TateCurve.lambertSeries_summable ℚ_[p] weight
    (freyAbcTateCandidateQ_norm_lt_one h hp_two hdiv)

/-- The canonical Tate q-series curve at the candidate input `q = j⁻¹`.  This is
the existing `TateCurve.weierstrassCurve` construction applied to the candidate
parameter; no identification with the Frey curve is claimed. -/
def freyAbcCandidateTateCurve (p a b c : ℕ) [Fact p.Prime] :
    WeierstrassCurve ℚ_[p] :=
  TateCurve.weierstrassCurve ℚ_[p] (freyAbcTateCandidateQ p a b c)

/-! ### The ellipticity certificate at `q = j⁻¹`: `Δ ≠ 0` and `IsElliptic`

At an odd prime `p` dividing `a b c` the valuation `v_p(j) = -2 v_p(a b c)`
forces `‖q‖ ≤ 1/9` for `q = j⁻¹`; the Lambert-series closed forms
`TateCurve.a4 = -5 s₃` and `TateCurve.a6 = -(5 s₃ + 7 s₅)/12` then discharge
the expansion criterion behind `TateCurve.canonical_delta_ne_zero_iff`, giving
`Δ ≠ 0` and ellipticity of the canonical q-series curve at the candidate
input.  No uniformization is claimed: this is not an identification of
`q = j⁻¹` with the Frey Tate parameter (see the module doc comment). -/

section TateCurveCertificate

open scoped BigOperators

set_option maxHeartbeats 1600000 in
-- Raised heartbeat budget for the p-adic norm estimates in this certificate block.
/-- The `p`-adic norm of a natural number, as an element of `ℚ_[p]`, is at
most one. -/
theorem padicNorm_natCast_le_one (n : ℕ) : ‖(n : ℚ_[p])‖ ≤ 1 := by
  simpa using Padic.norm_int_le_one (p := p) (n : ℤ)

set_option maxHeartbeats 1600000 in
-- Raised heartbeat budget for the p-adic norm estimates in this certificate block.
/-- At an odd prime `p`, the norm of `(12 : ℚ_[p])` is at least `1/3`: the
denominator `12` loses at most one factor `3`, while `4` is a `p`-adic unit. -/
theorem padicNorm_twelve_ge_invThree (hp_two : p ≠ 2) : (1 / 3 : ℝ) ≤ ‖(12 : ℚ_[p])‖ := by
  have h4cop : p.Coprime 4 := by
    refine (Nat.Prime.coprime_iff_not_dvd (Fact.out)).mpr ?_
    rintro ⟨k, hk⟩
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    have hle : p ≤ 4 := Nat.le_of_dvd (by norm_num) ⟨k, hk⟩
    have hp4 : p ≠ 4 := by
      rintro rfl
      exact absurd Fact.out (by decide : ¬ Nat.Prime 4)
    have hp3 : p = 3 := by omega
    subst hp3
    exact absurd ⟨k, hk⟩ (by decide : ¬ (3 : ℕ) ∣ 4)
  have h4 : ‖((4 : ℕ) : ℚ_[p])‖ = 1 := by
    rw [Padic.norm_natCast_eq_one_iff]
    exact h4cop
  have h12 : (12 : ℚ_[p]) = ((3 : ℕ) : ℚ_[p]) * ((4 : ℕ) : ℚ_[p]) := by norm_num
  rw [h12, norm_mul]
  by_cases hp : p = 3
  · subst hp
    have hpv : ‖((3 : ℕ) : ℚ_[3])‖ = (3 : ℝ)⁻¹ := Padic.norm_p
    rw [hpv, h4, mul_one]
    norm_num
  · have h3 : ‖((3 : ℕ) : ℚ_[p])‖ = 1 := by
      rw [Padic.norm_natCast_eq_one_iff]
      refine (Nat.Prime.coprime_iff_not_dvd (Fact.out)).mpr ?_
      rintro ⟨k, hk⟩
      have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
      have hle : p ≤ 3 := Nat.le_of_dvd (by norm_num) ⟨k, hk⟩
      have hp2' : p = 2 := by omega
      subst hp2'
      exact absurd ⟨k, hk⟩ (by decide : ¬ (2 : ℕ) ∣ 3)
    rw [h3, h4, mul_one]
    norm_num

set_option maxHeartbeats 1600000 in
-- Raised heartbeat budget for the p-adic norm estimates in this certificate block.
/-- For `‖q‖ < 1` and `m ≥ 1`, the factor `1 - qᵐ` is a unit of `ℚ_[p]` of
norm one. -/
theorem one_sub_pow_norm_eq_one (q : ℚ_[p]) (hq : ‖q‖ < 1) (m : ℕ) (hm : 0 < m) :
    ‖(1 : ℚ_[p]) - q ^ m‖ = 1 := by
  have hqm : ‖q ^ m‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq hm.ne'
  have hne : ‖(1 : ℚ_[p])‖ ≠ ‖-q ^ m‖ := by
    rw [norm_neg, norm_one]
    exact ne_of_gt hqm
  rw [sub_eq_add_neg, Padic.add_eq_max_of_ne hne, norm_neg, norm_one, max_eq_left hqm.le]

set_option maxHeartbeats 1600000 in
-- Raised heartbeat budget for the p-adic norm estimates in this certificate block.
/-- At an odd prime dividing `a b c`, the candidate input `q := j⁻¹` obeys
the explicit quantitative bound `‖q‖ ≤ 1/9`: the valuation of `j` is
`-2 v_p(a b c)` with `v_p(a b c) ≥ 1`, and `p ≥ 3`. -/
theorem freyAbcTateCandidateQ_norm_le_invNine
    (h : IsABCTriple a b c) (hp_two : p ≠ 2) (hdiv : p ∣ a * b * c) :
    ‖freyAbcTateCandidateQ p a b c‖ ≤ (1 / 9 : ℝ) := by
  have hval := h.abcJInvariant_padicValRat_of_prime_ne_two_dvd_product hp_two hdiv
  have hjne : abcJInvariant a b c ≠ 0 :=
    abcJInvariant_ne_zero_of_prime_ne_two_dvd_product h hp_two hdiv
  have hp3 : 3 ≤ p := by
    have h2 := (Fact.out : p.Prime).two_le
    omega
  have hp1 : (1 : ℚ) < (p : ℚ) := by
    exact_mod_cast (Fact.out : p.Prime).one_lt
  have hQ : (p : ℚ) ^ (-(2 * (padicValNat p (a * b * c) : ℤ))) ≤ (1 / 9 : ℚ) := by
    have hle : (p : ℚ) ^ (-(2 * (padicValNat p (a * b * c) : ℤ))) ≤
        (p : ℚ) ^ (-2 : ℤ) := by
      have hS0 : 0 < padicValNat p (a * b * c) :=
        (abcInvariant_prime_dvd_iff_padicValNat_pos h.abcInvariant_product_pos).mp hdiv
      rw [zpow_le_zpow_iff_right₀ hp1]
      omega
    have hsq : (3 : ℚ) ^ 2 ≤ (p : ℚ) ^ 2 := by
      exact pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hp3) 2
    calc (p : ℚ) ^ (-(2 * (padicValNat p (a * b * c) : ℤ)))
        ≤ (p : ℚ) ^ (-2 : ℤ) := hle
      _ = ((p : ℚ) ^ 2)⁻¹ := by rw [zpow_neg, zpow_ofNat]
      _ ≤ ((3 : ℚ) ^ 2)⁻¹ := by
          rw [inv_le_inv₀ (by positivity) (by norm_num)]
          exact hsq
      _ = (1 / 9 : ℚ) := by norm_num
  rw [freyAbcTateCandidateQ_def, ← Rat.cast_inv]
  rw [norm_ratCast_eq_padicNorm]
  rw [padicNorm.eq_zpow_of_nonzero (inv_ne_zero hjne), padicValRat.inv, hval]
  rw [show -(-(-2 * (padicValNat p (a * b * c) : ℤ))) =
    -(2 * (padicValNat p (a * b * c) : ℤ)) by ring]
  have hQR : (((p : ℚ) ^ (-(2 * (padicValNat p (a * b * c) : ℤ))) : ℚ) : ℝ) ≤
      ((1 / 9 : ℚ) : ℝ) :=
    Rat.cast_le.mpr hQ
  have h9 : ((1 / 9 : ℚ) : ℝ) = 1 / 9 := by norm_num
  rw [h9] at hQR
  exact hQR

set_option maxHeartbeats 1600000 in
-- Raised heartbeat budget for the p-adic norm estimates in this certificate block.
/-- Norm bound for the edge tail of a Lambert series starting at index `2`:
coefficients of norm at most one turn the tail into the geometric bound
`‖q‖² / (1 - ‖q‖)`. -/
theorem lambertSeries_edgeTail_norm_le (q : ℚ_[p]) (hq : ‖q‖ < 1)
    (c : ℕ → ℚ_[p]) (hc : ∀ n, ‖c n‖ ≤ 1) :
    ‖∑' n : ℕ, c n * q ^ (n + 2) / (1 - q ^ (n + 2))‖ ≤ ‖q‖ ^ 2 / (1 - ‖q‖) := by
  have hδ0 : 0 ≤ ‖q‖ := norm_nonneg q
  have hgeom : Summable (fun n : ℕ ↦ ‖q‖ ^ (n + 2)) :=
    ((summable_geometric_of_lt_one hδ0 hq).mul_left (‖q‖ ^ 2)).congr
      (fun n ↦ by rw [pow_add]; ring)
  have hTailNorm : Summable (fun n : ℕ ↦ ‖c n * q ^ (n + 2) / (1 - q ^ (n + 2))‖) :=
    Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _)
      (fun n ↦ by
        rw [norm_div, norm_mul, norm_pow,
          one_sub_pow_norm_eq_one q hq (n + 2) (by omega), div_one]
        exact mul_le_of_le_one_left (pow_nonneg hδ0 _) (hc n))
      hgeom
  calc ‖∑' n : ℕ, c n * q ^ (n + 2) / (1 - q ^ (n + 2))‖
      ≤ ∑' n : ℕ, ‖c n * q ^ (n + 2) / (1 - q ^ (n + 2))‖ :=
        norm_tsum_le_tsum_norm hTailNorm
    _ ≤ ∑' n : ℕ, ‖q‖ ^ (n + 2) :=
        Summable.tsum_le_tsum
          (fun n ↦ by
            rw [norm_div, norm_mul, norm_pow,
              one_sub_pow_norm_eq_one q hq (n + 2) (by omega), div_one]
            exact mul_le_of_le_one_left (pow_nonneg hδ0 _) (hc n))
          hTailNorm hgeom
    _ = ‖q‖ ^ 2 / (1 - ‖q‖) := by
        rw [show (∑' n : ℕ, ‖q‖ ^ (n + 2)) = ∑' n : ℕ, ‖q‖ ^ 2 * ‖q‖ ^ n from
          tsum_congr (fun n ↦ by rw [pow_add]; ring)]
        rw [tsum_mul_left, tsum_geometric_of_lt_one hδ0 hq, div_eq_mul_inv]

set_option maxHeartbeats 1600000 in
-- Raised heartbeat budget for the p-adic norm estimates in this certificate block.
/-- The weight-three Lambert series at a contracted input splits into its
geometric initial term `q / (1 - q)` and the explicit tail from index `2`. -/
theorem lambertSeries_three_eq_geometric_add_tail (q : ℚ_[p]) (hq : ‖q‖ < 1) :
    TateCurve.lambertSeries ℚ_[p] 3 q =
      q / (1 - q) +
        ∑' n : ℕ, ((n + 2 : ℕ) : ℚ_[p]) ^ 3 * q ^ (n + 2) / (1 - q ^ (n + 2)) := by
  have hsum := TateCurve.lambertSeries_summable ℚ_[p] 3 hq
  have hsplit := hsum.sum_add_tsum_nat_add 2
  have hleft : Finset.sum (Finset.range 2)
      (fun i : ℕ ↦ (i : ℚ_[p]) ^ 3 * q ^ i / (1 - q ^ i)) = q / (1 - q) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    simp
  rw [hleft] at hsplit
  exact (show TateCurve.lambertSeries ℚ_[p] 3 q =
      ∑' n : ℕ, (n : ℚ_[p]) ^ 3 * q ^ n / (1 - q ^ n) from rfl).trans hsplit.symm

set_option maxHeartbeats 1600000 in
-- Raised heartbeat budget for the p-adic norm estimates in this certificate block.
/-- The weight-five Lambert series at a contracted input splits into its
geometric initial term `q / (1 - q)` and the explicit tail from index `2`. -/
theorem lambertSeries_five_eq_geometric_add_tail (q : ℚ_[p]) (hq : ‖q‖ < 1) :
    TateCurve.lambertSeries ℚ_[p] 5 q =
      q / (1 - q) +
        ∑' n : ℕ, ((n + 2 : ℕ) : ℚ_[p]) ^ 5 * q ^ (n + 2) / (1 - q ^ (n + 2)) := by
  have hsum := TateCurve.lambertSeries_summable ℚ_[p] 5 hq
  have hsplit := hsum.sum_add_tsum_nat_add 2
  have hleft : Finset.sum (Finset.range 2)
      (fun i : ℕ ↦ (i : ℚ_[p]) ^ 5 * q ^ i / (1 - q ^ i)) = q / (1 - q) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    simp
  rw [hleft] at hsplit
  exact (show TateCurve.lambertSeries ℚ_[p] 5 q =
      ∑' n : ℕ, (n : ℚ_[p]) ^ 5 * q ^ n / (1 - q ^ n) from rfl).trans hsplit.symm

set_option maxHeartbeats 1600000 in
-- Raised heartbeat budget for the p-adic norm estimates in this certificate block.
/-- The discriminant expansion `a₄² - a₆ - 64 a₄³ - 432 a₆² + 72 a₄ a₆` of
the canonical Tate q-series curve at `q := j⁻¹` is nonzero: with
`b = 5 s₃ + 7 s₅` the dominant term `b / 12` has norm at least `5‖q‖/24`,
while the remaining polynomial part is bounded by `9‖q‖/64`. -/
theorem freyAbcCandidateTateCurve_delta_expansion_ne_zero
    (h : IsABCTriple a b c) (hp_two : p ≠ 2) (hdiv : p ∣ a * b * c) :
    TateCurve.a4 ℚ_[p] (freyAbcTateCandidateQ p a b c) ^ 2 -
        TateCurve.a6 ℚ_[p] (freyAbcTateCandidateQ p a b c) -
        64 * TateCurve.a4 ℚ_[p] (freyAbcTateCandidateQ p a b c) ^ 3 -
        432 * TateCurve.a6 ℚ_[p] (freyAbcTateCandidateQ p a b c) ^ 2 +
        72 * TateCurve.a4 ℚ_[p] (freyAbcTateCandidateQ p a b c) *
          TateCurve.a6 ℚ_[p] (freyAbcTateCandidateQ p a b c) ≠ 0 := by
  set q := freyAbcTateCandidateQ p a b c
  have hq_le : ‖q‖ ≤ 1 / 9 := freyAbcTateCandidateQ_norm_le_invNine h hp_two hdiv
  have hq_lt : ‖q‖ < 1 := freyAbcTateCandidateQ_norm_lt_one h hp_two hdiv
  have hq_ne : q ≠ 0 := freyAbcTateCandidateQ_ne_zero h hp_two hdiv
  have hδ0 : 0 ≤ ‖q‖ := norm_nonneg q
  have hδpos : 0 < ‖q‖ := norm_pos_iff.mpr hq_ne
  set A := q / (1 - q) with hAdef
  set T3 := ∑' n : ℕ, ((n + 2 : ℕ) : ℚ_[p]) ^ 3 * q ^ (n + 2) / (1 - q ^ (n + 2)) with hT3def
  set T5 := ∑' n : ℕ, ((n + 2 : ℕ) : ℚ_[p]) ^ 5 * q ^ (n + 2) / (1 - q ^ (n + 2)) with hT5def
  set s3 := TateCurve.lambertSeries ℚ_[p] 3 q with hs3def
  set s5 := TateCurve.lambertSeries ℚ_[p] 5 q with hs5def
  set b := 5 * s3 + 7 * s5 with hbdef
  set C := 25 * s3 ^ 2 + 8000 * s3 ^ 3 - 3 * b ^ 2 + 30 * s3 * b with hCdef
  have h1q : ‖(1 : ℚ_[p]) - q‖ = 1 := by
    simpa [pow_one] using one_sub_pow_norm_eq_one q hq_lt 1 (by norm_num)
  have hA : ‖A‖ = ‖q‖ := by
    rw [hAdef, norm_div, h1q, div_one]
  have hc3 : ∀ n : ℕ, ‖((n + 2 : ℕ) : ℚ_[p]) ^ 3‖ ≤ 1 := fun n ↦ by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (padicNorm_natCast_le_one (n + 2))
  have hc5 : ∀ n : ℕ, ‖((n + 2 : ℕ) : ℚ_[p]) ^ 5‖ ≤ 1 := fun n ↦ by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (padicNorm_natCast_le_one (n + 2))
  have hT3_le : ‖T3‖ ≤ ‖q‖ ^ 2 / (1 - ‖q‖) :=
    lambertSeries_edgeTail_norm_le q hq_lt (fun n ↦ ((n + 2 : ℕ) : ℚ_[p]) ^ 3) hc3
  have hT5_le : ‖T5‖ ≤ ‖q‖ ^ 2 / (1 - ‖q‖) :=
    lambertSeries_edgeTail_norm_le q hq_lt (fun n ↦ ((n + 2 : ℕ) : ℚ_[p]) ^ 5) hc5
  have hT3_small : ‖T3‖ ≤ ‖q‖ / 8 := by
    have h2 : ‖q‖ ^ 2 / (1 - ‖q‖) ≤ ‖q‖ / 8 := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 - ‖q‖)]
      nlinarith [hq_le, hδ0]
    linarith
  have hT5_small : ‖T5‖ ≤ ‖q‖ / 8 := by
    have h2 : ‖q‖ ^ 2 / (1 - ‖q‖) ≤ ‖q‖ / 8 := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 - ‖q‖)]
      nlinarith [hq_le, hδ0]
    linarith
  have h5n : ‖(5 : ℚ_[p])‖ ≤ 1 := padicNorm_natCast_le_one 5
  have h7n : ‖(7 : ℚ_[p])‖ ≤ 1 := padicNorm_natCast_le_one 7
  have h12_nle : ‖(12 : ℚ_[p])‖ ≤ 1 := padicNorm_natCast_le_one 12
  have h12_nge : (1 / 3 : ℝ) ≤ ‖(12 : ℚ_[p])‖ := padicNorm_twelve_ge_invThree hp_two
  have hs3e : s3 = A + T3 := by
    rw [hs3def, hAdef, hT3def]
    exact lambertSeries_three_eq_geometric_add_tail q hq_lt
  have hs5e : s5 = A + T5 := by
    rw [hs5def, hAdef, hT5def]
    exact lambertSeries_five_eq_geometric_add_tail q hq_lt
  have hs3n : ‖s3‖ ≤ 9 * ‖q‖ / 8 := by
    rw [hs3e]
    calc ‖A + T3‖ ≤ ‖A‖ + ‖T3‖ := norm_add_le _ _
      _ ≤ ‖q‖ + ‖q‖ / 8 := add_le_add hA.le hT3_small
      _ = 9 * ‖q‖ / 8 := by ring
  have hs5n : ‖s5‖ ≤ 9 * ‖q‖ / 8 := by
    rw [hs5e]
    calc ‖A + T5‖ ≤ ‖A‖ + ‖T5‖ := norm_add_le _ _
      _ ≤ ‖q‖ + ‖q‖ / 8 := add_le_add hA.le hT5_small
      _ = 9 * ‖q‖ / 8 := by ring
  have h5s : ‖5 * s3‖ ≤ 9 * ‖q‖ / 8 := by
    rw [norm_mul]
    calc ‖(5 : ℚ_[p])‖ * ‖s3‖ ≤ 1 * (9 * ‖q‖ / 8) :=
          mul_le_mul h5n hs3n (norm_nonneg _) zero_le_one
      _ = 9 * ‖q‖ / 8 := one_mul _
  have h7s : ‖7 * s5‖ ≤ 9 * ‖q‖ / 8 := by
    rw [norm_mul]
    calc ‖(7 : ℚ_[p])‖ * ‖s5‖ ≤ 1 * (9 * ‖q‖ / 8) :=
          mul_le_mul h7n hs5n (norm_nonneg _) zero_le_one
      _ = 9 * ‖q‖ / 8 := one_mul _
  have hbn : ‖b‖ ≤ 9 * ‖q‖ / 8 := by
    calc ‖b‖ = ‖5 * s3 + 7 * s5‖ := by rw [hbdef]
      _ ≤ max ‖5 * s3‖ ‖7 * s5‖ := Padic.nonarchimedean _ _
      _ ≤ max (9 * ‖q‖ / 8) (9 * ‖q‖ / 8) := max_le_max h5s h7s
      _ = 9 * ‖q‖ / 8 := max_self _
  have h5t : ‖5 * T3‖ ≤ ‖q‖ / 8 := by
    rw [norm_mul]
    calc ‖(5 : ℚ_[p])‖ * ‖T3‖ ≤ 1 * (‖q‖ / 8) :=
          mul_le_mul h5n hT3_small (norm_nonneg _) zero_le_one
      _ = ‖q‖ / 8 := one_mul _
  have h7t : ‖7 * T5‖ ≤ ‖q‖ / 8 := by
    rw [norm_mul]
    calc ‖(7 : ℚ_[p])‖ * ‖T5‖ ≤ 1 * (‖q‖ / 8) :=
          mul_le_mul h7n hT5_small (norm_nonneg _) zero_le_one
      _ = ‖q‖ / 8 := one_mul _
  have hR : ‖5 * T3 + 7 * T5‖ ≤ ‖q‖ / 8 := by
    calc ‖5 * T3 + 7 * T5‖ ≤ max ‖5 * T3‖ ‖7 * T5‖ := Padic.nonarchimedean _ _
      _ ≤ max (‖q‖ / 8) (‖q‖ / 8) := max_le_max h5t h7t
      _ = ‖q‖ / 8 := max_self _
  have hb_eq : b = (12 : ℚ_[p]) * A + (5 * T3 + 7 * T5) := by
    rw [hbdef, hs3e, hs5e]
    ring
  have hb_low : 5 * ‖q‖ / 24 ≤ ‖b‖ := by
    have hsub : ‖(12 : ℚ_[p]) * A‖ ≤ ‖b‖ + ‖5 * T3 + 7 * T5‖ := by
      have heq : b - (5 * T3 + 7 * T5) = (12 : ℚ_[p]) * A := by rw [hb_eq]; ring
      calc ‖(12 : ℚ_[p]) * A‖ = ‖b - (5 * T3 + 7 * T5)‖ := by rw [heq]
        _ ≤ ‖b‖ + ‖5 * T3 + 7 * T5‖ := norm_sub_le _ _
    have h12A : ‖(12 : ℚ_[p]) * A‖ = ‖(12 : ℚ_[p])‖ * ‖q‖ := by rw [norm_mul, hA]
    nlinarith [hsub, h12A, h12_nge, hR, hδ0]
  have h1 : ‖25 * s3 ^ 2‖ ≤ (9 * ‖q‖ / 8) ^ 2 := by
    rw [norm_mul, norm_pow]
    calc ‖(25 : ℚ_[p])‖ * ‖s3‖ ^ 2 ≤ 1 * (9 * ‖q‖ / 8) ^ 2 :=
          mul_le_mul (padicNorm_natCast_le_one 25)
            (pow_le_pow_left₀ (norm_nonneg s3) hs3n 2) (pow_nonneg (norm_nonneg s3) 2) zero_le_one
      _ = (9 * ‖q‖ / 8) ^ 2 := one_mul _
  have h2cube : ‖8000 * s3 ^ 3‖ ≤ (9 * ‖q‖ / 8) ^ 3 := by
    rw [norm_mul, norm_pow]
    calc ‖(8000 : ℚ_[p])‖ * ‖s3‖ ^ 3 ≤ 1 * (9 * ‖q‖ / 8) ^ 3 :=
          mul_le_mul (padicNorm_natCast_le_one 8000)
            (pow_le_pow_left₀ (norm_nonneg s3) hs3n 3) (pow_nonneg (norm_nonneg s3) 3) zero_le_one
      _ = (9 * ‖q‖ / 8) ^ 3 := one_mul _
  have h2 : ‖8000 * s3 ^ 3‖ ≤ (9 * ‖q‖ / 8) ^ 2 := by
    have hle1 : 9 * ‖q‖ / 8 ≤ 1 := by nlinarith [hq_le]
    have hmono : (9 * ‖q‖ / 8) ^ 3 ≤ (9 * ‖q‖ / 8) ^ 2 :=
      pow_le_pow_of_le_one (by nlinarith [hδ0]) hle1 (by norm_num : 2 ≤ 3)
    linarith
  have h3 : ‖3 * b ^ 2‖ ≤ (9 * ‖q‖ / 8) ^ 2 := by
    rw [norm_mul, norm_pow]
    calc ‖(3 : ℚ_[p])‖ * ‖b‖ ^ 2 ≤ 1 * (9 * ‖q‖ / 8) ^ 2 :=
          mul_le_mul (padicNorm_natCast_le_one 3)
            (pow_le_pow_left₀ (norm_nonneg b) hbn 2) (pow_nonneg (norm_nonneg b) 2) zero_le_one
      _ = (9 * ‖q‖ / 8) ^ 2 := one_mul _
  have h4 : ‖30 * s3 * b‖ ≤ (9 * ‖q‖ / 8) ^ 2 := by
    rw [norm_mul, norm_mul]
    calc ‖(30 : ℚ_[p])‖ * ‖s3‖ * ‖b‖ ≤ 1 * (9 * ‖q‖ / 8) * (9 * ‖q‖ / 8) :=
          mul_le_mul
            (mul_le_mul (padicNorm_natCast_le_one 30) hs3n (norm_nonneg _) zero_le_one)
            hbn (norm_nonneg _) (by nlinarith [hδ0])
      _ = (9 * ‖q‖ / 8) ^ 2 := by ring
  have hCn : ‖C‖ ≤ 81 * ‖q‖ ^ 2 / 64 := by
    rw [hCdef]
    have hsum_max : ‖25 * s3 ^ 2 + 8000 * s3 ^ 3‖ ≤ max ‖25 * s3 ^ 2‖ ‖8000 * s3 ^ 3‖ :=
      Padic.nonarchimedean _ _
    have hsub_max : ‖25 * s3 ^ 2 + 8000 * s3 ^ 3 - 3 * b ^ 2‖ ≤
        max ‖25 * s3 ^ 2 + 8000 * s3 ^ 3‖ ‖3 * b ^ 2‖ := by
      have hh := Padic.nonarchimedean (25 * s3 ^ 2 + 8000 * s3 ^ 3) (-(3 * b ^ 2))
      rw [norm_neg] at hh
      simpa [sub_eq_add_neg] using hh
    calc ‖25 * s3 ^ 2 + 8000 * s3 ^ 3 - 3 * b ^ 2 + 30 * s3 * b‖
        ≤ max ‖25 * s3 ^ 2 + 8000 * s3 ^ 3 - 3 * b ^ 2‖ ‖30 * s3 * b‖ :=
          Padic.nonarchimedean _ _
      _ ≤ max (max ‖25 * s3 ^ 2 + 8000 * s3 ^ 3‖ ‖3 * b ^ 2‖) ‖30 * s3 * b‖ :=
          max_le_max hsub_max le_rfl
      _ ≤ max (max (max ‖25 * s3 ^ 2‖ ‖8000 * s3 ^ 3‖) ‖3 * b ^ 2‖) ‖30 * s3 * b‖ :=
          max_le_max (max_le_max hsum_max le_rfl) le_rfl
      _ ≤ max (max (max ((9 * ‖q‖ / 8) ^ 2) ((9 * ‖q‖ / 8) ^ 2)) ((9 * ‖q‖ / 8) ^ 2))
            ((9 * ‖q‖ / 8) ^ 2) :=
          max_le_max (max_le_max (max_le_max h1 h2) h3) h4
      _ = 81 * ‖q‖ ^ 2 / 64 := by rw [max_self, max_self, max_self]; ring
  have hCsmall : ‖C‖ ≤ 9 * ‖q‖ / 64 := by
    have h81 : (81 : ℝ) * ‖q‖ ^ 2 / 64 ≤ 9 * ‖q‖ / 64 := by nlinarith [hq_le, hδ0]
    linarith
  have hEform : TateCurve.a4 ℚ_[p] q ^ 2 - TateCurve.a6 ℚ_[p] q -
      64 * TateCurve.a4 ℚ_[p] q ^ 3 - 432 * TateCurve.a6 ℚ_[p] q ^ 2 +
      72 * TateCurve.a4 ℚ_[p] q * TateCurve.a6 ℚ_[p] q = b / 12 + C := by
    rw [hCdef, hbdef]
    rw [TateCurve.a4, TateCurve.a6]
    rw [← hs3def, ← hs5def]
    ring
  have hb12_low : 5 * ‖q‖ / 24 ≤ ‖b / 12‖ := by
    have hpos12 : 0 < ‖(12 : ℚ_[p])‖ := norm_pos_iff.mpr (by norm_num)
    rw [norm_div]
    have hinv : 1 ≤ (‖(12 : ℚ_[p])‖)⁻¹ := (one_le_inv₀ hpos12).mpr h12_nle
    calc 5 * ‖q‖ / 24 ≤ ‖b‖ := hb_low
      _ = ‖b‖ * 1 := (mul_one ‖b‖).symm
      _ ≤ ‖b‖ * (‖(12 : ℚ_[p])‖)⁻¹ := mul_le_mul_of_nonneg_left hinv (norm_nonneg b)
      _ = ‖b‖ / ‖(12 : ℚ_[p])‖ := (div_eq_mul_inv ‖b‖ _).symm
  have hlt : ‖C‖ < ‖b / 12‖ := by
    have hcmp : 9 * ‖q‖ / 64 < 5 * ‖q‖ / 24 := by nlinarith [hδpos]
    linarith
  have hne0 : b / 12 + C ≠ 0 := by
    intro hzero
    have hnorm : ‖b / 12 + C‖ = 0 := by rw [hzero, norm_zero]
    rw [Padic.add_eq_max_of_ne (ne_of_lt hlt).symm, max_eq_left (le_of_lt hlt)] at hnorm
    have hpos : 0 < ‖b / 12‖ :=
      lt_of_lt_of_le (by linarith [hδpos] : 0 < 5 * ‖q‖ / 24) hb12_low
    exact (ne_of_gt hpos) hnorm
  rw [hEform]
  exact hne0

set_option maxHeartbeats 1600000 in
-- Raised heartbeat budget for the p-adic norm estimates in this certificate block.
/-- The discriminant of the canonical Tate q-series curve at `q := j⁻¹` is
nonzero, via the expansion criterion
`TateCurve.ArithmeticCertificate.canonical_delta_nonzero_of_expansion`. -/
theorem freyAbcCandidateTateCurve_delta_ne_zero
    (h : IsABCTriple a b c) (hp_two : p ≠ 2) (hdiv : p ∣ a * b * c) :
    (freyAbcCandidateTateCurve p a b c).Δ ≠ 0 := by
  have hheart := freyAbcCandidateTateCurve_delta_expansion_ne_zero h hp_two hdiv
  exact TateCurve.ArithmeticCertificate.canonical_delta_nonzero_of_expansion (K := ℚ_[p])
    (q := freyAbcTateCandidateQ p a b c) hheart

set_option maxHeartbeats 1600000 in
-- Raised heartbeat budget for the p-adic norm estimates in this certificate block.
/-- The canonical Tate q-series curve at `q := j⁻¹` is an elliptic curve, by
`TateCurve.canonical_is_elliptic_of_delta_ne_zero`.  This is a nondegeneracy
statement about the canonical q-series curve; no identification with the Frey
curve is claimed. -/
theorem freyAbcCandidateTateCurve_isElliptic
    (h : IsABCTriple a b c) (hp_two : p ≠ 2) (hdiv : p ∣ a * b * c) :
    (freyAbcCandidateTateCurve p a b c).IsElliptic :=
  TateCurve.canonical_is_elliptic_of_delta_ne_zero
    (freyAbcTateCandidateQ_norm_lt_one h hp_two hdiv)
    (freyAbcTateCandidateQ_ne_zero h hp_two hdiv)
    (freyAbcCandidateTateCurve_delta_ne_zero h hp_two hdiv)

set_option maxHeartbeats 1600000 in
-- Raised heartbeat budget for the p-adic norm estimates in this certificate block.
/-- The full arithmetic certificate `TateCurve.ArithmeticCertificate` at
`q := j⁻¹`: `q ≠ 0`, `‖q‖ < 1`, and `Δ ≠ 0`. -/
theorem freyAbcTateCandidateQ_arithmeticCertificate
    (h : IsABCTriple a b c) (hp_two : p ≠ 2) (hdiv : p ∣ a * b * c) :
    TateCurve.ArithmeticCertificate (freyAbcTateCandidateQ p a b c) :=
  TateCurve.ArithmeticCertificate.mk
    (freyAbcTateCandidateQ_ne_zero h hp_two hdiv)
    (freyAbcTateCandidateQ_norm_lt_one h hp_two hdiv)
    (freyAbcCandidateTateCurve_delta_ne_zero h hp_two hdiv)

end TateCurveCertificate

/-! ### The completion side: the rational place at `p` and the q-unit

The rational finite place at `p` is built from the standard height-one
correspondence for `ℤ`, and its completion is identified with `ℚ_[p]` by the
canonical `ℚ`-algebra equivalence (`Padic.adicCompletionEquiv`).  The candidate
`j⁻¹` is viewed in that completion through the canonical embedding of `ℚ`, and
the unit hypothesis of `NumberFieldFinitePlace.tateParameterUnit` is
instantiated.  No uniformization, coordinate change, or point comparison is
claimed. -/

/-- The height-one prime of `ℤ` at `p`, as a height-one spectrum over the ring of
integers of `ℚ`. -/
noncomputable def rationalHeightOneSpectrum (p : ℕ) [Fact p.Prime] :
    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := NumberField.RingOfIntegers ℚ)).symm
    ⟨p, Fact.out⟩

/-- The rational finite place at `p`. -/
noncomputable def rationalFinitePlace (p : ℕ) [Fact p.Prime] :
    NumberField.FinitePlace ℚ :=
  NumberField.FinitePlace.mk (rationalHeightOneSpectrum p)

/-- The underlying height-one prime of the rational finite place at `p` is the
one built above, so `NumberFieldFinitePlace.Completion (rationalFinitePlace p)`
is the adic completion of `ℚ` at `p`. -/
theorem rationalFinitePlace_underlyingPrime (p : ℕ) [Fact p.Prime] :
    NumberFieldFinitePlace.underlyingPrime (rationalFinitePlace p) =
      rationalHeightOneSpectrum p :=
  NumberField.FinitePlace.maximalIdeal_mk (rationalHeightOneSpectrum p)

/-- The canonical `ℚ`-algebra equivalence between `ℚ_[p]` and the completion of
`ℚ` at its finite place `p`. -/
noncomputable def rationalFinitePlacePadicEquiv (p : ℕ) [Fact p.Prime] :
    ℚ_[p] ≃A[ℚ] (rationalHeightOneSpectrum p).adicCompletion ℚ :=
  Padic.adicCompletionEquiv (R := NumberField.RingOfIntegers ℚ) ⟨p, Fact.out⟩

/-- The canonical embedding `ℚ → Completion` is injective: it is the rational
cast into a characteristic-zero field. -/
theorem rationalFinitePlace_algebraMap_injective (p : ℕ) [Fact p.Prime] :
    Function.Injective (algebraMap ℚ
      (NumberFieldFinitePlace.Completion (rationalFinitePlace p))) := by
  intro x y h
  exact Rat.cast_injective h

/-- The canonical embedding `ℚ → Completion` does not kill nonzero
rationals. -/
theorem rationalFinitePlace_algebraMap_ne_zero (p : ℕ) [Fact p.Prime]
    (q : ℚ) (hq : q ≠ 0) :
    algebraMap ℚ (NumberFieldFinitePlace.Completion (rationalFinitePlace p)) q ≠ 0 := by
  intro hzero
  exact hq (rationalFinitePlace_algebraMap_injective p (by simpa using hzero))

/-- The canonical embedding `ℚ → Completion` does not send non-one rationals to
one. -/
theorem rationalFinitePlace_algebraMap_ne_one (p : ℕ) [Fact p.Prime]
    (q : ℚ) (hq : q ≠ 1) :
    algebraMap ℚ (NumberFieldFinitePlace.Completion (rationalFinitePlace p)) q ≠ 1 := by
  intro hone
  exact hq (rationalFinitePlace_algebraMap_injective p (by simpa using hone))

/-- The canonical embedding `ℚ → Completion` preserves the valuation: the image
of `q : ℚ` carries the height-one valuation of the rational place at `p`.  The
`algebraMap` of the completion at a division ring is the rational cast
`Rat.cast`; the proof pushes the rational cast from the completion of `ℚ` into
the underlying uniform completion of `WithVal`. -/
theorem rationalFinitePlace_valued_algebraMap (q : ℚ) :
    Valued.v (algebraMap ℚ (NumberFieldFinitePlace.Completion (rationalFinitePlace p)) q) =
    (NumberFieldFinitePlace.underlyingPrime (rationalFinitePlace p)).valuation ℚ q := by
  have hcast : algebraMap ℚ (NumberFieldFinitePlace.Completion (rationalFinitePlace p)) q =
      (Rat.cast q : IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        (NumberFieldFinitePlace.underlyingPrime (rationalFinitePlace p))) := rfl
  rw [hcast, IsDedekindDomain.HeightOneSpectrum.adicCompletion.valuedAdicCompletion_def]
  have htoCompletion :
      (Rat.cast q : IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        (NumberFieldFinitePlace.underlyingPrime (rationalFinitePlace p))).toCompletion =
      (Rat.cast q : ((NumberFieldFinitePlace.underlyingPrime
        (rationalFinitePlace p)).valuation ℚ).Completion) :=
    map_ratCast (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv ℚ
      (NumberFieldFinitePlace.underlyingPrime (rationalFinitePlace p))).toRingHom q
  rw [htoCompletion]
  have hcoe :
      (Rat.cast q : ((NumberFieldFinitePlace.underlyingPrime
        (rationalFinitePlace p)).valuation ℚ).Completion) =
      (↑(q : WithVal ((NumberFieldFinitePlace.underlyingPrime
          (rationalFinitePlace p)).valuation ℚ)) :
        ((NumberFieldFinitePlace.underlyingPrime
          (rationalFinitePlace p)).valuation ℚ).Completion) :=
    (map_ratCast (UniformSpace.Completion.coeRingHom (α := WithVal
      ((NumberFieldFinitePlace.underlyingPrime (rationalFinitePlace p)).valuation ℚ))) q).symm
  rw [hcoe, Valued.extensionValuation_apply_coe]
  change Valued.v (WithVal.toVal
    ((NumberFieldFinitePlace.underlyingPrime (rationalFinitePlace p)).valuation ℚ) q) = _
  rw [WithVal.valued_toVal]

/-- The candidate `j⁻¹` viewed in the `p`-adic completion of `ℚ` through the
canonical embedding.  Under the identification `rationalFinitePlacePadicEquiv`
this is the same element as `freyAbcTateCandidateQ`; it is **not** claimed to be
a Tate parameter. -/
noncomputable def freyAbcTateCandidateQAtRationalCompletion (p a b c : ℕ) [Fact p.Prime] :
    NumberFieldFinitePlace.Completion (rationalFinitePlace p) :=
  algebraMap ℚ (NumberFieldFinitePlace.Completion (rationalFinitePlace p))
    (abcJInvariant a b c)⁻¹

/-- The completion-side candidate is nonzero at an odd bad prime. -/
theorem freyAbcTateCandidateQAtRationalCompletion_ne_zero
    (h : IsABCTriple a b c) (hp_two : p ≠ 2) (hdiv : p ∣ a * b * c) :
    freyAbcTateCandidateQAtRationalCompletion p a b c ≠ 0 := by
  rw [freyAbcTateCandidateQAtRationalCompletion]
  exact rationalFinitePlace_algebraMap_ne_zero p (abcJInvariant a b c)⁻¹
    (inv_ne_zero (abcJInvariant_ne_zero_of_prime_ne_two_dvd_product h hp_two hdiv))

/-- The completion-side candidate is not one at an odd bad prime. -/
theorem freyAbcTateCandidateQAtRationalCompletion_ne_one
    (h : IsABCTriple a b c) (hp_two : p ≠ 2) (hdiv : p ∣ a * b * c) :
    freyAbcTateCandidateQAtRationalCompletion p a b c ≠ 1 := by
  rw [freyAbcTateCandidateQAtRationalCompletion]
  exact rationalFinitePlace_algebraMap_ne_one p (abcJInvariant a b c)⁻¹
    (fun hone => abcJInvariant_ne_one_of_prime_ne_two_dvd_product h hp_two hdiv
      (inv_eq_one.mp hone))

/-- At an odd bad prime the completion-side candidate `j⁻¹` is strictly
contracting: its valuation at the rational place is `< 1`.  This is the
inequality recorded by
`NumberFieldFinitePlace.FinitePlaceQCandidate.valuation_lt_one`. -/
theorem freyAbcTateCandidateQAtRationalCompletion_valued_lt_one
    (h : IsABCTriple a b c) (hp_two : p ≠ 2) (hdiv : p ∣ a * b * c) :
    Valued.v (freyAbcTateCandidateQAtRationalCompletion p a b c) < 1 := by
  rw [freyAbcTateCandidateQAtRationalCompletion,
    rationalFinitePlace_valued_algebraMap (q := (abcJInvariant a b c)⁻¹)]
  rw [rationalFinitePlace_underlyingPrime p]
  have hden := abcJInvariant_den_dvd_of_prime_ne_two_dvd_product h hp_two hdiv
  have hvj : 1 < (Rat.padicValuation p) (abcJInvariant a b c) :=
    lt_of_not_ge fun hle => (Rat.padicValuation_le_one_iff.mp hle) hden
  have hvq : (Rat.padicValuation p) (abcJInvariant a b c)⁻¹ < 1 := by
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ hvj
  have hp' : (↑(Rat.HeightOneSpectrum.primesEquiv (rationalHeightOneSpectrum p)) : ℕ) = p := by
    simp [rationalHeightOneSpectrum]
  have he : ((rationalHeightOneSpectrum p).valuation ℚ).IsEquiv (Rat.padicValuation p) := by
    simpa only [hp'] using
      Rat.HeightOneSpectrum.valuation_equiv_padicValuation (rationalHeightOneSpectrum p)
  exact (Valuation.isEquiv_iff_val_lt_one.mp he).mpr hvq

/-- Norm form of the completion-side contraction at an odd bad prime: in the
canonical normed-field structure of the adic completion the candidate `j⁻¹`
has norm `< 1`. -/
theorem freyAbcTateCandidateQAtRationalCompletion_norm_lt_one
    (h : IsABCTriple a b c) (hp_two : p ≠ 2) (hdiv : p ∣ a * b * c) :
    ‖freyAbcTateCandidateQAtRationalCompletion p a b c‖ < 1 := by
  rw [Valued.toNormedField.norm_lt_one_iff]
  exact freyAbcTateCandidateQAtRationalCompletion_valued_lt_one h hp_two hdiv

/-- Membership form of the completion-side contraction: `p` an odd prime in
the bad support `abcOddBadPrimeSupport a b c`. -/
theorem freyAbcTateCandidateQAtRationalCompletion_valued_lt_one_of_mem
    (h : IsABCTriple a b c) (hp : p ∈ abcOddBadPrimeSupport a b c) :
    Valued.v (freyAbcTateCandidateQAtRationalCompletion p a b c) < 1 := by
  obtain ⟨-, hp_two, hdiv⟩ := (IsABCTriple.mem_abcOddBadPrimeSupport_iff h).mp hp
  exact freyAbcTateCandidateQAtRationalCompletion_valued_lt_one h hp_two hdiv

/-- Norm form of the membership statement
`p ∈ abcOddBadPrimeSupport a b c`. -/
theorem freyAbcTateCandidateQAtRationalCompletion_norm_lt_one_of_mem
    (h : IsABCTriple a b c) (hp : p ∈ abcOddBadPrimeSupport a b c) :
    ‖freyAbcTateCandidateQAtRationalCompletion p a b c‖ < 1 := by
  obtain ⟨-, hp_two, hdiv⟩ := (IsABCTriple.mem_abcOddBadPrimeSupport_iff h).mp hp
  exact freyAbcTateCandidateQAtRationalCompletion_norm_lt_one h hp_two hdiv

/-- The candidate `j⁻¹` packaged as the valuation-theoretic q-candidate of the
rational place at `p`: nonzero, distinct from one, and strictly contracting.
This records only the q-parameter valuation kernel; it asserts no Tate
uniformization and identifies no curve with the quotient by `q^ℤ`. -/
noncomputable def freyAbcTateCandidateQFinitePlaceCandidate
    (h : IsABCTriple a b c) (hp_two : p ≠ 2) (hdiv : p ∣ a * b * c) :
    NumberFieldFinitePlace.FinitePlaceQCandidate (rationalFinitePlace p) where
  q := freyAbcTateCandidateQAtRationalCompletion p a b c
  q_ne_zero := freyAbcTateCandidateQAtRationalCompletion_ne_zero h hp_two hdiv
  valuation_lt_one :=
    freyAbcTateCandidateQAtRationalCompletion_valued_lt_one h hp_two hdiv

/-- The q-unit of the completion interface at the candidate `j⁻¹`: the actual
`NumberFieldFinitePlace.tateParameterUnit` applied at the rational place `p`.
Beyond the place, its only input is `q ≠ 0`. -/
noncomputable def freyAbcTateCandidateQUnit
    (h : IsABCTriple a b c) (hp_two : p ≠ 2) (hdiv : p ∣ a * b * c) :
    (AlgebraicClosure
      (NumberFieldFinitePlace.Completion (rationalFinitePlace p)))ˣ :=
  NumberFieldFinitePlace.tateParameterUnit (rationalFinitePlace p)
    (freyAbcTateCandidateQAtRationalCompletion p a b c)
    (freyAbcTateCandidateQAtRationalCompletion_ne_zero h hp_two hdiv)

/-- The instantiated q-unit is not one: the `q ≠ 1` conclusion of
`NumberFieldFinitePlace.tateParameterUnit_ne_one` at the candidate `j⁻¹`. -/
theorem freyAbcTateCandidateQUnit_ne_one
    (h : IsABCTriple a b c) (hp_two : p ≠ 2) (hdiv : p ∣ a * b * c) :
    freyAbcTateCandidateQUnit h hp_two hdiv ≠ 1 :=
  NumberFieldFinitePlace.tateParameterUnit_ne_one (rationalFinitePlace p)
    (freyAbcTateCandidateQAtRationalCompletion p a b c)
    (freyAbcTateCandidateQAtRationalCompletion_ne_zero h hp_two hdiv)
    (freyAbcTateCandidateQAtRationalCompletion_ne_one h hp_two hdiv)

end

end LeanFormal.IUT
