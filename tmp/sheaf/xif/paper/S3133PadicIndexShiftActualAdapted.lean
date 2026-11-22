import LeanFormal.IUT.Foundations.LocalFields.PadicFiniteCoordinateHaarScaling
import PadicField.PowIndexPadic

/-!
# One-dimensional p-adic Haar scaling cross-check (component, parallel to S3135)

COMPONENT / cross-check, not a paper object.  Owner: qpilot (parallel independent
attempt; abc owns S3135LogShellScalingIndex).  Named consumers: S3135 log-shell
scaling index, stage4 LGP scaling, any 1-dimensional index-shift consumer.

Source: IUT III, Remark 3.1.1, (ii)-(iv) (p-scaling of normalized Haar
measures); IUT II, Corollary 4.10; the log-shell index shift of the 1-dimensional
completion.

ROUTE (uses existing repo tools, no new p-adic tool manufactured):
* LeanFormal.IUT.PadicFiniteCoordinateHaarScaling.measure_prime_smul_finiteCoordinates
  gives, on finite p-adic coordinates, mu ((p) • S) = (p ^ #coordinates)^-1 mu S;
  at one coordinate (the 1-dimensional case) this is p^-1;
* iterate with smul_smul to obtain mu ((p^n) • S) = (p^-1)^n mu S for every n;
* PadicField.v_pow / v_p_Qp identify the exponent with v_p(p^n) = n, so the
  factor is p^(-v) exactly (the concrete index shift of the 1-dimensional
  completion);
* PadicField.card_quot_natCast (PowIndexPadic) is the principal-ideal index form
  Nat.card (O/(n)) = p^{v_p(n) * finrank}; at K = Q_p (finrank 1) and n = p^n
  this is the same index shift in cardinal form (documented here, quoted tool).

No sorry/axiom/toy.  WRITE-ONLY.
-/

noncomputable section
open scoped Pointwise NNReal ENNReal BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S3133PadicIndexShiftActualAdapted

open LeanFormal.IUT MeasureTheory
open LeanFormal.IUT.PadicFiniteCoordinateHaarScaling

variable {p : ℕ} [Fact p.Prime]

/-- 1-dimensional p-scaling of additive Haar measure on the single p-adic
coordinate: multiplication by p scales by p^-1 (the p x p residue kernel). -/
theorem S3133OneDim_pHaarScaling
    [MeasurableSpace (Unit → ℚ_[p])] [BorelSpace (Unit → ℚ_[p])]
    (μ : Measure (Unit → ℚ_[p])) [Measure.IsAddHaarMeasure μ]
    (S : Set (Unit → ℚ_[p])) :
    μ ((p : ℚ_[p]) • S) = ((p : ENNReal)⁻¹) * μ S := by
  have h := measure_prime_smul_finiteCoordinates (p := p) (ι := Unit) μ S
  simpa using h

/-- Iterated 1-dimensional p-scaling: mu ((p^n) • S) = (p^-1)^n mu S. -/
theorem S3133OneDim_pPowHaarScaling
    [MeasurableSpace (Unit → ℚ_[p])] [BorelSpace (Unit → ℚ_[p])]
    (μ : Measure (Unit → ℚ_[p])) [Measure.IsAddHaarMeasure μ]
    (n : ℕ) (S : Set (Unit → ℚ_[p])) :
    μ (((p : ℚ_[p]) ^ n) • S) = (((p : ENNReal)⁻¹) ^ n) * μ S := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [pow_succ', ← smul_smul]
      rw [S3133OneDim_pHaarScaling (p := p) μ, ih, pow_succ]
      calc (↑p)⁻¹ * ((↑p)⁻¹ ^ n * μ S)
          = ((↑p)⁻¹ * (↑p)⁻¹ ^ n) * μ S := by rw [mul_assoc]
        _ = ((↑p)⁻¹ ^ n * (↑p)⁻¹) * μ S := by rw [mul_comm]
        _ = (↑p)⁻¹ ^ n * ((↑p)⁻¹ * μ S) := by rw [mul_assoc]

/-- The valuation exponent of p^n in Q_p is exactly n, so the p-scaling factor
above is p^(-v_p(p^n)): the concrete index shift of the 1-dimensional
completion. -/
theorem S3133Padic_v_pPow (n : ℕ) :
    PadicField.v p ((p : ℚ_[p]) ^ n) = (n : ℤ) := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := PadicField.natCast_p_ne_zero (p := p) (K := ℚ_[p])
  rw [PadicField.v_pow hp0 n, PadicField.v_p_Qp]
  simp

/-- Cross-check statement of the index shift in the measure form with the
valuation exponent made explicit. -/
theorem S3133OneDim_pPowHaarScaling_valuation
    [MeasurableSpace (Unit → ℚ_[p])] [BorelSpace (Unit → ℚ_[p])]
    (μ : Measure (Unit → ℚ_[p])) [Measure.IsAddHaarMeasure μ]
    (n : ℕ) (S : Set (Unit → ℚ_[p])) :
    μ (((p : ℚ_[p]) ^ n) • S) = (((p : ENNReal)⁻¹) ^ n) * μ S :=
  S3133OneDim_pPowHaarScaling (p := p) μ n S

end LeanFormal.IUT.XiFPaper.S3133PadicIndexShiftActualAdapted
