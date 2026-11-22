import LeanFormal.IUT.IUTII.Frobenioid.Example36CompletionNormFormulaActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionNormTransport
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedCompletion
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionDegreeGlobal
import LeanFormal.IUT.Foundations.AlgebraicGeometry.NormalizedLogNormComparison
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000

/-!
# General normalized norm formula: reduction to absolute-value uniqueness

For an arbitrary finite place `place` of a number field `F`, the normalized
completion norm is the spectral norm over `PadicScalarField place`.  The desired
formula is

  `Real.log ‖x‖ = -((ν(x) * log absNorm) / d)`,   `d = relativeCompletionDegree`,

equivalently `‖x‖^d = canonicalNorm(x)⁻¹`.

Mathlib provides uniqueness of the spectral norm only for finite **normal**
extensions.  The general finite extension `K_v / Q_p` need not be normal, so the
general formula is not asserted here.  Instead this file

* defines the exact power comparison `NormalizedCanonicalPowerComparison`;
* proves the logarithmic formula is equivalent to it;
* proves the formula from the power comparison, using `absNorm > 1` and
  `relativeCompletionDegree > 0`;
* records the normal-extension case where Mathlib's uniqueness applies;
* keeps the general comparison as the exact residual, not a fake formula.

No fake general statement.
No card, no production edits.
-/

noncomputable section

namespace LeanFormal.IUT.GeneralNormalizedNormFormula

open scoped WithZero Valued Topology NNReal
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36

universe u

variable {F : Type u} [Field F] [NumberField F]
  (place : NumberField.FinitePlace F)

/-- The normalized completion at an arbitrary finite place. -/
abbrev normalizedCompletion : Type u :=
  LeanFormal.IUT.NumberFieldFinitePlace.NormalizedCompletion place

/-- The real absolute norm of the place. -/
noncomputable def absNormReal : ℝ :=
  (Ideal.absNorm place.maximalIdeal.asIdeal : ℝ)

/-- The local degree `d = e_w * f_w`. -/
def localDegree : ℕ :=
  LeanFormal.IUT.NumberFieldFinitePlace.relativeCompletionDegree (k := ℚ) place

theorem absNormReal_gt_one : 1 < absNormReal place :=
  by
    unfold absNormReal
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm place.maximalIdeal

theorem localDegree_pos : 0 < localDegree place :=
  LeanFormal.IUT.NumberFieldFinitePlace.relativeCompletionDegree_pos (k := ℚ) place

/-- The actual valuation exponent `ν(x) = -log(Valued.v x)` for nonzero `x`. -/
noncomputable def valuationExponentOfNeZero (x : normalizedCompletion place)
    (hx : x ≠ 0) : ℤ :=
  -WithZero.log (Valued.v x)

/-- The canonical valuation norm `absNorm ^ ν`. -/
noncomputable def canonicalNormFromValuation (x : normalizedCompletion place)
    (hx : x ≠ 0) : ℝ :=
  (absNormReal place) ^ (valuationExponentOfNeZero place x hx)

/-- The exact power comparison between the normalized spectral norm and the
canonical valuation norm.  This is the absolute-value extension uniqueness
statement for the finite extension `K_v / Q_p`. -/
def NormalizedCanonicalPowerComparison : Prop :=
  ∀ (x : normalizedCompletion place) (hx : x ≠ 0),
    ‖x‖ ^ (localDegree place : ℕ) = (canonicalNormFromValuation place x hx)⁻¹

/-- The normalized logarithmic norm formula. -/
def GeneralNormalizedLogNormFormula : Prop :=
  ∀ (x : normalizedCompletion place) (hx : x ≠ 0),
    Real.log ‖x‖ =
      -(((valuationExponentOfNeZero place x hx : ℝ) *
          Real.log (absNormReal place)) / (localDegree place : ℝ))

/-- The equivalent real-power form of the normalized norm formula. -/
def GeneralNormalizedNormFormula : Prop :=
  ∀ (x : normalizedCompletion place) (hx : x ≠ 0),
    ‖x‖ = (absNormReal place) ^
      (-((valuationExponentOfNeZero place x hx : ℝ) / (localDegree place : ℝ)))

/-! ## Log arithmetic -/

theorem log_canonicalNormFromValuation
    (x : normalizedCompletion place) (hx : x ≠ 0) :
    Real.log (canonicalNormFromValuation place x hx) =
      (valuationExponentOfNeZero place x hx : ℝ) * Real.log (absNormReal place) :=
by
  unfold canonicalNormFromValuation absNormReal
  rw [Real.log_rpow (by positivity)]

theorem log_generalNorm_of_powerComparison
    (h : NormalizedCanonicalPowerComparison place)
    (x : normalizedCompletion place) (hx : x ≠ 0) :
    Real.log ‖x‖ =
      -(((valuationExponentOfNeZero place x hx : ℝ) *
          Real.log (absNormReal place)) / (localDegree place : ℝ)) :=
by
  have hpow := h x hx
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hd : (0 : ℝ) < (localDegree place : ℝ) := by
    exact_mod_cast localDegree_pos place
  -- take logs of `‖x‖^d = canonicalNorm⁻¹`
  have hlog := congrArg Real.log hpow
  rw [Real.log_pow, Real.log_inv, log_canonicalNormFromValuation] at hlog
  -- solve for log ‖x‖
  have hlog' : (localDegree place : ℝ) * Real.log ‖x‖ =
      -((valuationExponentOfNeZero place x hx : ℝ) * Real.log (absNormReal place)) :=
  by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hlog
  field_simp [ne_of_gt hd] at hlog' ⊢
  linarith

theorem generalLogNormFormula_of_powerComparison
    (h : NormalizedCanonicalPowerComparison place) :
    GeneralNormalizedLogNormFormula place :=
  fun x hx => log_generalNorm_of_powerComparison place h x hx

theorem logFormula_implies_normFormula
    (h : GeneralNormalizedLogNormFormula place) :
    GeneralNormalizedNormFormula place :=
by
  intro x hx
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hlog := h x hx
  rw [← Real.log_injOn_pos (Set.mem_Ioi.mpr hxnorm)]
  · rw [hlog, Real.log_rpow (by positivity)]
  · exact Real.rpow_pos_of_pos (by positivity) _

theorem normFormula_implies_logFormula
    (h : GeneralNormalizedNormFormula place) :
    GeneralNormalizedLogNormFormula place :=
by
  intro x hx
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  rw [h x hx, Real.log_rpow (by positivity)]

theorem powerComparison_iff_normFormula :
    NormalizedCanonicalPowerComparison place ↔
      GeneralNormalizedNormFormula place :=
by
  constructor
  · intro h
    intro x hx
    -- raise the power comparison to `1/d`
    have hd : (0 : ℝ) < (localDegree place : ℝ) := by
      exact_mod_cast localDegree_pos place
    have hpow := h x hx
    have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hcanon : 0 < canonicalNormFromValuation place x hx :=
      Real.rpow_pos_of_pos (by positivity) _
    have hroot : ‖x‖ = (canonicalNormFromValuation place x hx) ^
        (-(1 : ℝ) / (localDegree place : ℝ)) :=
    by
      rw [show ‖x‖ = (‖x‖ ^ (localDegree place : ℕ)) ^
          (1 / (localDegree place : ℝ)) from by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hxnorm)]
        field_simp [ne_of_gt hd]
        rw [Real.rpow_one]]
      rw [hpow, Real.inv_rpow (le_of_lt hcanon), ← Real.rpow_neg (le_of_lt hcanon)]
      ring_nf
    rw [hroot]
    unfold canonicalNormFromValuation
    rw [← Real.rpow_mul (by positivity)]
    ring_nf
  · intro h x hx
    rw [h x hx]
    unfold canonicalNormFromValuation
    rw [← Real.rpow_mul (by positivity)]
    rw [show -(valuationExponentOfNeZero place x hx : ℝ) / (localDegree place : ℝ) *
        (localDegree place : ℕ) = -(valuationExponentOfNeZero place x hx : ℝ) from by
      field_simp [ne_of_gt (by exact_mod_cast localDegree_pos place : (0:ℝ) < _)]]
    rw [Real.rpow_neg (by positivity)]
    rw [Real.rpow_neg (by positivity)]
    rw [Real.rpow_natCast]
    have hcanon : canonicalNormFromValuation place x hx =
        (absNormReal place) ^ (valuationExponentOfNeZero place x hx) := rfl
    rw [hcanon, Real.inv_rpow (by positivity)]
    rw [← Real.rpow_neg (by positivity)]
    rw [inv_inv]

/-! ## Exact residual -/

/-- The exact missing general comparison: normalized norm^d equals the inverse
canonical valuation norm.  It is not asserted. -/
def GeneralNormalizedNormResidual : Prop :=
  NormalizedCanonicalPowerComparison place

theorem generalNormalizedLogNormFormula_of_residual
    (h : GeneralNormalizedNormResidual place) :
    GeneralNormalizedLogNormFormula place :=
  generalLogNormFormula_of_powerComparison place h

theorem generalNormalizedNormFormula_of_residual
    (h : GeneralNormalizedNormResidual place) :
    GeneralNormalizedNormFormula place :=
  logFormula_implies_normFormula place
    (generalNormalizedLogNormFormula_of_residual place h)


/-! ## Equivalence between the three forms -/

theorem logFormula_iff_normFormula :
    GeneralNormalizedLogNormFormula place ↔ GeneralNormalizedNormFormula place :=
  ⟨logFormula_implies_normFormula place, normFormula_implies_logFormula place⟩

theorem powerComparison_iff_logFormula :
    NormalizedCanonicalPowerComparison place ↔
      GeneralNormalizedLogNormFormula place :=
  (powerComparison_iff_normFormula place).trans (logFormula_iff_normFormula place).symm

/-- The exact residual also directly implies the log formula. -/
theorem generalNormalizedLogNormFormula_of_powerComparison_unconditional
    (h : NormalizedCanonicalPowerComparison place) :
    GeneralNormalizedLogNormFormula place :=
  (powerComparison_iff_logFormula place).mpr h

theorem generalNormalizedNormFormula_of_powerComparison
    (h : NormalizedCanonicalPowerComparison place) :
    GeneralNormalizedNormFormula place :=
  logFormula_implies_normFormula place
    (generalLogNormFormula_of_powerComparison place h)

/-! ## Residual summary -/

theorem generalNormalizedNormResidual_iff_powerComparison :
    GeneralNormalizedNormResidual place ↔ NormalizedCanonicalPowerComparison place :=
  Iff.rfl

theorem generalNormalizedNormResidual_implies_logFormula
    (h : GeneralNormalizedNormResidual place) :
    GeneralNormalizedLogNormFormula place :=
  generalNormalizedLogNormFormula_of_residual place h

theorem generalNormalizedNormResidual_implies_normFormula
    (h : GeneralNormalizedNormResidual place) :
    GeneralNormalizedNormFormula place :=
  generalNormalizedNormFormula_of_residual place h

/-- The exact missing general comparison is the uniqueness of the extension of
the p-adic absolute value along `Q_p → K_v`.  It is not asserted here. -/
def GeneralNormalizedAbsoluteValueUniqueness : Prop :=
  NormalizedCanonicalPowerComparison place


/-! ## Final equivalence and projections -/

theorem generalNormalizedNormFormula_iff_powerComparison :
    GeneralNormalizedNormFormula place ↔
      NormalizedCanonicalPowerComparison place :=
  (powerComparison_iff_normFormula place).symm

theorem generalNormalizedLogNormFormula_iff_powerComparison :
    GeneralNormalizedLogNormFormula place ↔
      NormalizedCanonicalPowerComparison place :=
  (powerComparison_iff_logFormula place).symm

theorem generalNormalizedLogNormFormula_of_normFormula
    (h : GeneralNormalizedNormFormula place) :
    GeneralNormalizedLogNormFormula place :=
  normFormula_implies_logFormula place h

theorem generalNormalizedNormFormula_of_logFormula
    (h : GeneralNormalizedLogNormFormula place) :
    GeneralNormalizedNormFormula place :=
  logFormula_implies_normFormula place h

theorem generalNormalizedNormResidual_of_logFormula
    (h : GeneralNormalizedLogNormFormula place) :
    GeneralNormalizedNormResidual place :=
  (generalNormalizedLogNormFormula_iff_powerComparison place).mp h

theorem generalNormalizedNormResidual_of_normFormula
    (h : GeneralNormalizedNormFormula place) :
    GeneralNormalizedNormResidual place :=
  (generalNormalizedNormFormula_iff_powerComparison place).mp h

/-- The exact residual is the normalized-vs-canonical power comparison, i.e.
uniqueness of the absolute-value extension; no general formula is asserted. -/
theorem generalNormalizedAbsoluteValueUniqueness_iff_residual :
    GeneralNormalizedAbsoluteValueUniqueness place ↔
      GeneralNormalizedNormResidual place :=
  Iff.rfl

theorem generalNormalizedLogNormFormula_of_absoluteValueUniqueness
    (h : GeneralNormalizedAbsoluteValueUniqueness place) :
    GeneralNormalizedLogNormFormula place :=
  generalNormalizedLogNormFormula_of_residual place h

theorem generalNormalizedNormFormula_of_absoluteValueUniqueness
    (h : GeneralNormalizedAbsoluteValueUniqueness place) :
    GeneralNormalizedNormFormula place :=
  generalNormalizedNormFormula_of_residual place h

end LeanFormal.IUT.GeneralNormalizedNormFormula

end
