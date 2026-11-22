import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! # Mzk1Stage4CarrierScalingLogLawSupportActual (stage4 lane; log-law support)

A664 module: stage4 support for `PaperRegionScalingLaw` via the carrier scaling log
law — single-factor log identities for the inverse prime-power Haar factors used by
`badInvScale_productHaar_pi`, plus the real positive-factor log laws.  These are the
log-algebra pieces of the mainline next-step (log form of the product law); the
normalized-s1902 form still belongs to the hull/mainline files.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4CarrierScalingLogLawSupportActual

open scoped ENNReal BigOperators

/-- `log (1/a * b) = -log a + log b` for positive reals. -/
theorem log_inv_mul {a b : Real} (ha : 0 < a) (hb : 0 < b) :
    Real.log (a⁻¹ * b) = -Real.log a + Real.log b := by
  rw [Real.log_mul (inv_ne_zero (ne_of_gt ha)) (ne_of_gt hb), Real.log_inv]

/-- `log ((x^n)⁻¹) = -n log x` for positive reals. -/
theorem log_inv_pow {x : Real} (hx : 0 < x) (n : Nat) :
    Real.log ((x ^ n)⁻¹) = -(n : Real) * Real.log x := by
  rw [Real.log_inv, Real.log_pow]
  ring

/-- `log (∏ᵢ (xᵢ ^ nᵢ)⁻¹) = -Σᵢ nᵢ log xᵢ` for positive reals. -/
theorem log_prod_inv_pow {ι : Type*} (s : Finset ι) (x : ι → Real) (n : ι → Nat)
    (hx : ∀ i ∈ s, 0 < x i) :
    Real.log (∏ i ∈ s, (x i ^ n i)⁻¹) =
      -∑ i ∈ s, (n i : Real) * Real.log (x i) := by
  rw [Real.log_prod]
  · rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [Real.log_inv, Real.log_pow]
  · intro i hi
    exact inv_ne_zero (pow_ne_zero _ (ne_of_gt (hx i hi)))

/-- The log of an inverse prime-power ENNReal factor. -/
theorem log_toReal_inv_pow {a : ENNReal} (ha0 : a ≠ 0) (haT : a ≠ ⊤) (n : Nat) :
    Real.log (((a ^ n)⁻¹).toReal) = -(n : Real) * Real.log a.toReal := by
  have hane : a.toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨ha0, haT⟩
  rw [ENNReal.toReal_inv, ENNReal.toReal_pow]
  rw [Real.log_inv, Real.log_pow]
  ring

/-- Support status rows for the carrier scaling log law. -/
def logLawSupportRows : List (String × String) :=
  [ ("positive-factor log laws", "log_inv_mul, log_inv_pow, log_prod_inv_pow")
  , ("ENNReal inverse prime-power factor", "log_toReal_inv_pow (badInvScale local factor)")
  , ("combine with product law", "stage4 LogProductLawActual.log_toReal_mul + top-level product")
  , ("normalized s1902 form", "hull/mainline: needs s1902HaarScale cancellation (not faked here)")
  ]

/-- The support record has four rows. -/
theorem logLawSupportRows_length : logLawSupportRows.length = 4 := rfl

#check log_inv_mul
#check log_inv_pow
#check log_prod_inv_pow
#check log_toReal_inv_pow
#check logLawSupportRows_length

end LeanFormal.IUT.XiFPaper.Mzk1Stage4CarrierScalingLogLawSupportActual
end
