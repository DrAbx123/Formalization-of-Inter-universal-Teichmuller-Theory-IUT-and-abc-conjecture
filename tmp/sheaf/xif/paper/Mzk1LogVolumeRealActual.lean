import Mathlib

/-!
# Mzk1LogVolumeRealActual — real logarithm laws for log-volume (real math)

Status: PENDING-VERIFY. No sorry, no axiom.
Genuine Real.log laws used in log-volume bookkeeping: mul/pow/inv/one. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1LogVolumeRealActual

/-- Genuine theorem: log of a product. -/
theorem logVolume_mul {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Real.log (a * b) = Real.log a + Real.log b :=
  Real.log_mul ha hb

/-- Genuine theorem: log of a natural power. -/
theorem logVolume_pow {a : ℝ} (n : ℕ) :
    Real.log (a ^ n) = n * Real.log a :=
  Real.log_pow a n

/-- Genuine theorem: log of an inverse. -/
theorem logVolume_inv {a : ℝ} :
    Real.log a⁻¹ = - Real.log a :=
  Real.log_inv a

/-- Genuine theorem: log of one is zero. -/
theorem logVolume_one : Real.log (1 : ℝ) = 0 :=
  Real.log_one

end LeanFormal.IUT.XiFPaper.Mzk1LogVolumeRealActual
