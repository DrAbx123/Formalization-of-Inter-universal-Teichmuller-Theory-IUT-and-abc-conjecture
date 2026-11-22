import tmp.sheaf.xif.paper.PaperLevelXiFTargetProofActual
import tmp.sheaf.xif.paper.GlobalQPilotProcessionLogVolumeActual
import tmp.sheaf.xif.paper.BadPlaceProcessionNormalizedComparisonActual
import tmp.sheaf.xif.paper.S766QPilot2LNormalizationActual
import tmp.sheaf.xif.paper.S694ThetaAverageNormalizationActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S860GlobalCor312AuditActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual
open LeanFormal.IUT.XiFPaper.GlobalQPilotProcessionLogVolumeActual
open LeanFormal.IUT.XiFPaper.BadPlaceProcessionNormalizedComparisonActual
open LeanFormal.IUT.XiFPaper.S766QPilot2LNormalizationActual
open LeanFormal.IUT.XiFPaper.S694ThetaAverageNormalizationActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- Actual V_bad weighted q-pilot scalar used by PaperLevelXiFTargetProofActual. -/
noncomputable def weightedQPilot : Real :=
  PaperLevelXiFTargetProofActual.globalQPilotLog T

/-- Actual Theta hull scalar from PaperLevelXiFTargetProofActual. -/
noncomputable def thetaHullScalar : Real :=
  PaperLevelXiFTargetProofActual.globalThetaHullLog T

theorem classicalComparison_actual : weightedQPilot T ≤ thetaHullScalar T :=
  PaperLevelXiFTargetProofActual.globalQPilotLog_le_globalThetaHullLog T

/-- Exact 2l-corrected paper target. -/
def CorrectedQPilotTarget : Prop :=
  weightedQPilot T ≤ (2 * (l.value : Real)) * thetaHullScalar T

/-- Actual bad-place procession target (procession-normalized Theta <= q). -/
def ProcessionTargetActual : Prop :=
  BadPlaceProcessionNormalizedComparisonActual.ProcessionNormalizedTarget T

/-- Paper label weight correction from S694. -/
def PaperProcessionWeightGap : Prop :=
  (∀ (f : PaperThetaLabel l → Real),
    paperThetaLabelAverage f =
      paperThetaLabelWeight l * ∑ i, f i)

structure GlobalCor312Audit where
  weightedQPilot : Real
  weightedQPilot_eq : weightedQPilot = LeanFormal.IUT.XiFPaper.S860GlobalCor312AuditActual.weightedQPilot T
  unweightedQPilot : Real
  thetaHullScalar : Real
  thetaHullScalar_eq : thetaHullScalar = LeanFormal.IUT.XiFPaper.S860GlobalCor312AuditActual.thetaHullScalar T
  vbadWeightReconciliation : Prop
  processionNormalization : Prop
  ind1 : Prop
  ind2 : Prop
  ind3 : Prop
  classicalComparison : weightedQPilot ≤ thetaHullScalar
  correctedComparison : Prop

noncomputable def globalCor312Audit
    (unweightedQPilot : Real)
    (hvbad : Prop)
    (hproc : ProcessionTargetActual T)
    (hi1 hi2 hi3 : Prop) :
    GlobalCor312Audit T where
  weightedQPilot := LeanFormal.IUT.XiFPaper.S860GlobalCor312AuditActual.weightedQPilot T
  weightedQPilot_eq := rfl
  unweightedQPilot := unweightedQPilot
  thetaHullScalar := LeanFormal.IUT.XiFPaper.S860GlobalCor312AuditActual.thetaHullScalar T
  thetaHullScalar_eq := rfl
  vbadWeightReconciliation := hvbad
  processionNormalization := ProcessionTargetActual T
  ind1 := hi1
  ind2 := hi2
  ind3 := hi3
  classicalComparison := classicalComparison_actual T
  correctedComparison := CorrectedQPilotTarget T

end LeanFormal.IUT.XiFPaper.S860GlobalCor312AuditActual
end