import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Normed.Field.Basic

#check @norm_zsmul
#check @norm_nsmul
#check @Complex.real_smul
#check @Algebra.smul_def
#check @Complex.coe_algebraMap
#check @Complex.ofReal_eq_coe
#check @inv_mul_cancel₀
#check @Complex.ofReal_intCast
#check @Complex.ofReal_natCast
#check @Int.cast_abs
#check @abs_nonneg
#check @abs_of_nonneg
#check @Complex.ext_iff
#check @mul_inv_cancel₀
#check @Complex.ofReal_div
#check @div_mul_cancel₀
#check @mul_one_div_cancel
example (r : ℝ) (z : ℂ) : (↑r : ℂ) * z = r • z := Complex.real_smul r z
example (n : ℤ) (z : ℂ) : ‖n • z‖ = |(n:ℝ)| * ‖z‖ := norm_zsmul n z
