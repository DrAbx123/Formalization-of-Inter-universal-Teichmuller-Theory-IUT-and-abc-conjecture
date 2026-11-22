import tmp.sheaf.xif.paper.S2735QPilotLineBundleActual

noncomputable section
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2735FractionalCoercionBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaperArithmeticLineBundle
open LeanFormal.IUT.XiFPaper.S2735QPilotLineBundleActual

variable (l : PrimeGeFive)

/-- Fractional-ideal coercion bridge: the absolute norm of the extended q-pilot
line bundle is the product of the q-pilot norm and the extended ideal norm. -/
theorem S2735_absNorm_qPilotLineBundleExtended
    (J : Ideal (SourceOK (A := S2735Arithmetic l))) :
    FractionalIdeal.absNorm (qPilotLineBundleExtended l J) =
      FractionalIdeal.absNorm (qPilotLineBundle l) *
        FractionalIdeal.absNorm
          (J : FractionalIdeal (nonZeroDivisors
            (SourceOK (A := S2735Arithmetic l))) (S2735Arithmetic l).K) := by
  unfold qPilotLineBundleExtended qPilotIdealExtended
  rw [FractionalIdeal.coeIdeal_mul, map_mul]
  rfl

/-- Expanded form with the actual bad-prime norm. -/
theorem S2735_absNorm_qPilotLineBundleExtended_eq
    (J : Ideal (SourceOK (A := S2735Arithmetic l))) :
    FractionalIdeal.absNorm (qPilotLineBundleExtended l J) =
      (5 * 5 * 2161 * 2161 : ℚ) *
        FractionalIdeal.absNorm
          (J : FractionalIdeal (nonZeroDivisors
            (SourceOK (A := S2735Arithmetic l))) (S2735Arithmetic l).K) := by
  rw [S2735_absNorm_qPilotLineBundleExtended, qPilotFractional_absNorm]

#check S2735_absNorm_qPilotLineBundleExtended
#check S2735_absNorm_qPilotLineBundleExtended_eq
#print axioms S2735_absNorm_qPilotLineBundleExtended
end LeanFormal.IUT.XiFPaper.S2735FractionalCoercionBridgeActual
end
