import tmp.sheaf.xif.paper.PaperLevelXiFTargetProofActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1068CorrectedPaperTargetActual

/- INTERMEDIATE MODEL ONLY.  The definitions and theorem below use
   PaperLevelXiFTargetProofActual (c_norm spectral model), not the paper
   canonical qPilot(order) vs root-stack theta hull(order/(2l)) target.
   Do not cite S1068 as the paper target. -/

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- INTERMEDIATE c_norm model: signed qPilot (NOT paper order). -/
noncomputable def qPilotSigned : Real :=
  globalQPilotLog T

/-- INTERMEDIATE c_norm model: signed Theta hull (NOT paper order/(2l)). -/
noncomputable def thetaHullSigned : Real :=
  globalThetaHullLog T

/-- INTERMEDIATE signed inequality in the c_norm model.  This is not the
paper canonical qPilot(order) <= theta hull(order/(2l)) target. -/
theorem qPilotSigned_le_thetaHullSigned :
    qPilotSigned T ≤ thetaHullSigned T :=
  globalQPilotLog_le_globalThetaHullLog T

/-- INTERMEDIATE target proposition (not paper). -/
def S1068PaperSignedTarget : Prop :=
  qPilotSigned T ≤ thetaHullSigned T

theorem s1068PaperSignedTarget_holds :
    S1068PaperSignedTarget T :=
  qPilotSigned_le_thetaHullSigned T

/-- Per-b signed inequality, actual. -/
theorem perB_qPilotSigned_le_thetaHullSigned
    (b : Bad (nativePlaceSelection T)) :
    perBQPilotLog T b ≤ perBThetaHullLog T b :=
  perBQPilotLog_le_perBThetaHullLog T b

end LeanFormal.IUT.XiFPaper.S1068CorrectedPaperTargetActual

end
