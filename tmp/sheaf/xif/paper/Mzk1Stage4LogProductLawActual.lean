import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! # Mzk1Stage4LogProductLawActual (stage4 lane; log form of the product law)

A661 module: the LOG FORM of the `badInvScale` product law (mainline next-step 1):
for finite nonzero ENNReal factors, the real logarithm of the product is the sum of the
real logarithms of the factors.  Self-contained (Mathlib only).  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4LogProductLawActual

open scoped ENNReal BigOperators

/-- Log of a product of two finite nonzero ENNReal factors. -/
theorem log_toReal_mul {a b : ENNReal} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (haT : a ≠ ⊤) (hbT : b ≠ ⊤) :
    Real.log ((a * b).toReal) = Real.log a.toReal + Real.log b.toReal := by
  rw [ENNReal.toReal_mul]
  refine Real.log_mul ?_ ?_
  · exact ENNReal.toReal_ne_zero.mpr ⟨ha0, haT⟩
  · exact ENNReal.toReal_ne_zero.mpr ⟨hb0, hbT⟩

/-- Log of a power of a finite nonzero ENNReal factor. -/
theorem log_toReal_pow {a : ENNReal} (ha0 : a ≠ 0) (haT : a ≠ ⊤) (n : Nat) :
    Real.log ((a ^ n).toReal) = (n : Real) * Real.log a.toReal := by
  rw [ENNReal.toReal_pow]
  rw [Real.log_pow]

/-- Log form on a two-factor product (the local factor times the base measure). -/
theorem log_toReal_mul_factor {c mu : ENNReal} (hc0 : c ≠ 0) (hcT : c ≠ ⊤)
    (hmu0 : mu ≠ 0) (hmuT : mu ≠ ⊤) :
    Real.log ((c * mu).toReal) = Real.log c.toReal + Real.log mu.toReal :=
  log_toReal_mul hc0 hmu0 hcT hmuT

/-- Log-form status rows: which pieces of the mainline next-step are covered here. -/
def logFormStatus : List (String × String) :=
  [ ("local factor times base", "log_toReal_mul / log_toReal_mul_factor (Lana/badInvScale product law)")
  , ("powers", "log_toReal_pow (prime-power local factors)")
  , ("sum over bad places", "combine with stage4 BadPartArithmeticActual.badPart_log")
  , ("normalized s1902 form", "still hull/mainline (needs s1902HaarScale cancellation)")
  ]

/-- The log-form status record has four rows. -/
theorem logFormStatus_length : logFormStatus.length = 4 := rfl

#check log_toReal_mul
#check log_toReal_pow
#check log_toReal_mul_factor
#check logFormStatus_length

end LeanFormal.IUT.XiFPaper.Mzk1Stage4LogProductLawActual
end
