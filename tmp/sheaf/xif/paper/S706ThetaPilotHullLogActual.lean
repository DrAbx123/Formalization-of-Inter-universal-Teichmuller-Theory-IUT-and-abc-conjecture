import tmp.sheaf.xif.paper.PaperLevelXiFTargetProofActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S706ThetaPilotHullLogActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

noncomputable def thetaPilotHullLog (b : Bad (nativePlaceSelection T)) : Real :=
  perBThetaHullLog T b

noncomputable def qPilotLog (b : Bad (nativePlaceSelection T)) : Real :=
  perBQPilotLog T b

noncomputable def globalThetaPilotHullLog : Real :=
  globalThetaHullLog T

noncomputable def globalQPilotLog : Real :=
  LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual.globalQPilotLog T

noncomputable def thetaPilotMagnitude : Real := -globalThetaPilotHullLog T

noncomputable def qPilotMagnitude : Real := -globalQPilotLog T

def ThetaPilotQpilotComparison : Prop :=
  thetaPilotMagnitude T ≤ qPilotMagnitude T

theorem thetaPilotQpilotComparison :
    ThetaPilotQpilotComparison T := by
  unfold ThetaPilotQpilotComparison thetaPilotMagnitude qPilotMagnitude
    globalThetaPilotHullLog globalQPilotLog
  have h := globalQPilotLog_le_globalThetaHullLog T
  linarith

structure ThetaPilotLogVolumeData where
  perBHullLog : Bad (nativePlaceSelection T) → Real
  perBHullLog_eq : perBHullLog = thetaPilotHullLog T
  perBQPilotLog : Bad (nativePlaceSelection T) → Real
  perBQPilotLog_eq : perBQPilotLog = qPilotLog T
  globalHullLog : Real
  globalHullLog_eq : globalHullLog = globalThetaPilotHullLog T
  globalQLog : Real
  globalQLog_eq : globalQLog = LeanFormal.IUT.XiFPaper.S706ThetaPilotHullLogActual.globalQPilotLog T
  comparison : globalQLog ≤ globalHullLog

noncomputable def thetaPilotLogVolumeData : ThetaPilotLogVolumeData T where
  perBHullLog := thetaPilotHullLog T
  perBHullLog_eq := rfl
  perBQPilotLog := qPilotLog T
  perBQPilotLog_eq := rfl
  globalHullLog := globalThetaPilotHullLog T
  globalHullLog_eq := rfl
  globalQLog := LeanFormal.IUT.XiFPaper.S706ThetaPilotHullLogActual.globalQPilotLog T
  globalQLog_eq := rfl
  comparison := globalQPilotLog_le_globalThetaHullLog T

end LeanFormal.IUT.XiFPaper.S706ThetaPilotHullLogActual
end