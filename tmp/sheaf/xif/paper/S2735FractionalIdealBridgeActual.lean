import tmp.sheaf.xif.paper.ArithmeticLineBundleActual
import Mathlib.RingTheory.FractionalIdeal.Norm

noncomputable section
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2735FractionalIdealBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaperArithmeticLineBundle

universe u

variable {l : PrimeGeFive} (A : InitialThetaArithmeticData.{u} l)

/-- The actual `Ideal O_K → FractionalIdeal O_K K` bridge used by the q-pilot
line bundle: the fractional-ideal norm of the coerced ideal is the ideal norm. -/
theorem S2735_coeIdeal_absNorm
    (I : Ideal (SourceOK (A := A))) :
    FractionalIdeal.absNorm
      ((I : FractionalIdeal (nonZeroDivisors (SourceOK (A := A))) A.K)) =
      Ideal.absNorm I :=
  FractionalIdeal.coeIdeal_absNorm I

/-- The coercion is injective, so the q-pilot ideal is recovered from its
fractional-ideal line bundle. -/
theorem S2735_coeIdeal_injective :
    Function.Injective
      (fun I : Ideal (SourceOK (A := A)) =>
        (I : FractionalIdeal (nonZeroDivisors (SourceOK (A := A))) A.K)) :=
  FractionalIdeal.coeIdeal_injective' (le_rfl)

/-- Nonzero q-pilot ideals give nonzero fractional line bundles. -/
theorem S2735_coeIdeal_ne_zero
    {I : Ideal (SourceOK (A := A))} (hI : I ≠ ⊥) :
    (I : FractionalIdeal (nonZeroDivisors (SourceOK (A := A))) A.K) ≠ 0 :=
  FractionalIdeal.coeIdeal_ne_zero' (le_rfl) |>.mpr hI

/-- The log of the fractional-ideal norm of the q-pilot line bundle equals the
log of the ideal norm, when the ideal is nonzero. -/
theorem S2735_coeIdeal_log_absNorm
    (I : Ideal (SourceOK (A := A))) (hI : Ideal.absNorm I ≠ 0) :
    Real.log (FractionalIdeal.absNorm
      ((I : FractionalIdeal (nonZeroDivisors (SourceOK (A := A))) A.K)) : Real) =
      Real.log (Ideal.absNorm I : Real) := by
  rw [S2735_coeIdeal_absNorm]

#check S2735_coeIdeal_absNorm
#check S2735_coeIdeal_injective
#check S2735_coeIdeal_ne_zero
#check S2735_coeIdeal_log_absNorm
#print axioms S2735_coeIdeal_absNorm

end LeanFormal.IUT.XiFPaper.S2735FractionalIdealBridgeActual
end
