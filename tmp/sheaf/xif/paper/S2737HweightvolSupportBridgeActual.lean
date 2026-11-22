import tmp.sheaf.xif.paper.S2736QPilotLineBundleHweightvol

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2736QPilotLineBundleHweightvol
open LeanFormal.IUT.XiFPaper.S2735QPilotLineBundleActual
open LeanFormal.IUT.XiFPaperArithmeticLineBundle
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2737HweightvolSupportBridgeActual

variable {l : PrimeGeFive}

/-- Exact norm decomposition of the q-pilot line bundle extended by J. -/
theorem S2737_absNorm_extended_eq
    (J : Ideal (SourceOK (A := S2735Arithmetic l))) :
    FractionalIdeal.absNorm (qPilotLineBundleExtended (l := l) J) =
      (Ideal.absNorm (qPilotIdeal l) : Rat) * (Ideal.absNorm J : Rat) := by
  rw [qPilotLineBundleExtended, qPilotIdealExtended,
    FractionalIdeal.coeIdeal_absNorm, map_mul]
  push_cast
  ring

/-- Exact log-volume formula in terms of the q-pilot norm and the support norm. -/
theorem S2737_logVolume_eq
    (J : Ideal (SourceOK (A := S2735Arithmetic l))) :
    S2736QPilotLineBundleLogVolume (l := l) J =
      Real.log
        ((((Ideal.absNorm (qPilotIdeal l) : Rat) *
          (Ideal.absNorm J : Rat) : Rat) : Real)) := by
  rw [S2736QPilotLineBundleLogVolume, S2737_absNorm_extended_eq]

#check S2737_absNorm_extended_eq
#check S2737_logVolume_eq
#print axioms S2737_absNorm_extended_eq
#print axioms S2737_logVolume_eq

end LeanFormal.IUT.XiFPaper.S2737HweightvolSupportBridgeActual
end
