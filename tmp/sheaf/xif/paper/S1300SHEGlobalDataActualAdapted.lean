import tmp.sheaf.xif.paper.GlobalThetaHullVsQPilotComparisonActual
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S1300SHEGlobalDataActualAdapted
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.GlobalThetaHullVsQPilotComparisonActual
universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv} [Fintype V]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (R : ∀ v : V, I.SourceImageRealization v) (n : ThetaPilotCarrier l)

structure S1300SHEGlobalData : Type where
  qPilotMagnitude : Real
  hullLogVolume : Real
  hullSignedLogVolume : Real
  qPilotMagnitude_eq : qPilotMagnitude = -I.qPilotSignedLogVolume
  hullLogVolume_eq : hullLogVolume = globalThetaHullLogVolume (I := I) R n
  hullSignedLogVolume_eq : hullSignedLogVolume = -hullLogVolume

noncomputable def S1300SHEGlobalData.of : S1300SHEGlobalData I R n where
  qPilotMagnitude := qPilotMagnitude (I := I)
  hullLogVolume := globalThetaHullLogVolume (I := I) R n
  hullSignedLogVolume := thetaHullSignedLogVolume (I := I) R n
  qPilotMagnitude_eq := rfl
  hullLogVolume_eq := rfl
  hullSignedLogVolume_eq := rfl

#check S1300SHEGlobalData
#check S1300SHEGlobalData.of
end LeanFormal.IUT.XiFPaper.S1300SHEGlobalDataActualAdapted
end
