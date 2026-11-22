import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Complex

#check @Complex.re_add_im
#check @Complex.ext
#check @Complex.norm_I
#check @Complex.norm_ofReal
#check @Complex.norm_real
#check @Complex.ofReal_mul
#check @Complex.ofReal_one
#check @Complex.ofReal_zero
#check @Complex.norm_mul
#check @norm_mul
#check @norm_inv
#check @abs_le
#check @Complex.abs_arg_le_pi
#check @Complex.norm_eq_one_iff
#check @Complex.exp_mul_I
#check @Real.cos_arg
#check @Complex.cos_arg
#check @Complex.sin_arg
#check @Complex.normSq
#check @Complex.sq_norm
#check @Complex.mul_conj
#check @Complex.exp_eq_one_iff
#check @zsmul_eq_mul
#check @Int.cast_smul_eq_zsmul
#check @nsmul_eq_mul

example (n : ℤ) (z : ℂ) : n • z = (n : ℂ) * z := by
  rw [zsmul_eq_mul]
