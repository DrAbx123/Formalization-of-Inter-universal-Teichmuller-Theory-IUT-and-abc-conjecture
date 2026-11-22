import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! # Mzk1LogVolumeCoefficientNumericsActual — numerical log-volume coefficients

Lean transcription of the arithmetic content of the mined independent verification
scripts `03_log_unit_bounds` / `11_log_volume_coefficient` (laichunwing,
IUT-Verification), namely the IUT IV Prop 1.4(ii) coefficient

`μ_log(log_p(R_i^×)) = -(1/e_i + m_i/(e_i f_i)) · log p`

and its test cases `e=f=1, m=0 ⇒ -1` (unramified, p = 11) and
`e=2, f=1, m=0 ⇒ -1/2` (Q_11(√11)).  Pure real arithmetic; no new mathematics.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1LogVolumeCoefficientNumericsActual

/-- The IUT IV Prop 1.4(ii) log-volume coefficient of the log-shell boundary. -/
noncomputable def logVolumeCoefficient (e f m : Nat) : Real :=
  -((1 : Real) / (e : Real) + (m : Real) / ((e : Real) * (f : Real)))

/-- Unramified case `e = f = 1, m = 0`: coefficient `-1`. -/
theorem logVolumeCoefficient_unramified (p : Nat) :
    logVolumeCoefficient 1 1 0 = -(1 : Real) := by
  unfold logVolumeCoefficient
  norm_num

/-- Tame ramified case `e = 2, f = 1, m = 0` (Q_11(√11)): coefficient `-1/2`. -/
theorem logVolumeCoefficient_quadratic (p : Nat) :
    logVolumeCoefficient 2 1 0 = -(1 / 2 : Real) := by
  unfold logVolumeCoefficient
  norm_num

/-- The coefficient is strictly negative for `e, f > 0`. -/
theorem logVolumeCoefficient_neg {e f m : Nat} (he : 0 < e) (hf : 0 < f) :
    logVolumeCoefficient e f m < 0 := by
  unfold logVolumeCoefficient
  have heR : (0 : Real) < (e : Real) := by exact_mod_cast he
  have hfR : (0 : Real) < (f : Real) := by exact_mod_cast hf
  have h1 : (0 : Real) < (1 : Real) / (e : Real) := div_pos one_pos heR
  have h2 : (0 : Real) <= (m : Real) / ((e : Real) * (f : Real)) := by positivity
  linarith

/-- Rational form: `e f · coefficient = -(f + m)`. -/
theorem logVolumeCoefficient_mul_denom {e f m : Nat} (he : 0 < e) (hf : 0 < f) :
    (e : Real) * (f : Real) * logVolumeCoefficient e f m = -((f : Real) + (m : Real)) := by
  unfold logVolumeCoefficient
  have heR : (e : Real) ≠ 0 := by exact_mod_cast he.ne'
  have hfR : (f : Real) ≠ 0 := by exact_mod_cast hf.ne'
  field_simp
  ring

/-- Log-volume value of the boundary shell: `coefficient · log p`. -/
theorem logVolumeCoefficient_mul_log {e f m : Nat} (he : 0 < e) (hf : 0 < f)
    {p : Nat} (hp : 0 < p) :
    logVolumeCoefficient e f m * Real.log (p : Real) =
      -(((e : Real) * (f : Real))⁻¹ * ((f : Real) + (m : Real)) * Real.log (p : Real)) := by
  rw [← logVolumeCoefficient_mul_denom he hf]
  field_simp
  ring

/-- The unramified boundary log-volume for `p = 11`: coefficient `-1`. -/
theorem logVolumeCoefficient_unramified_log_eleven :
    logVolumeCoefficient 1 1 0 * Real.log (11 : Real) = -Real.log (11 : Real) := by
  rw [logVolumeCoefficient_unramified]
  ring

#check logVolumeCoefficient
#check logVolumeCoefficient_unramified
#check logVolumeCoefficient_quadratic
#check logVolumeCoefficient_neg
#check logVolumeCoefficient_mul_denom

end LeanFormal.IUT.XiFPaper.Mzk1LogVolumeCoefficientNumericsActual
end
