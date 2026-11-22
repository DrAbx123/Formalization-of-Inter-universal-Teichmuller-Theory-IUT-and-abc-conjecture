import tmp.sheaf.xif.paper.S919GlobalWeightedInequalityActual
import tmp.sheaf.xif.paper.S779RootHullNonzeroFixActual
import tmp.sheaf.xif.paper.PaperLevelXiFTargetProofActual
import tmp.sheaf.xif.paper.S1070S1063IntermediateAuditActual

-- S1064: weighted global from the correct per-b qPilotClassical <= theta
-- nonzero inequality.  S1063 file is absent, so the per-b inequality is
-- recorded as the exact minimal input; s994VR is NOT used as qPilot.

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000

namespace LeanFormal.IUT.XiFPaper.S1064GlobalQpilotClassicalThetaNonzeroActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual
open LeanFormal.IUT.XiFPaper.S779RootHullNonzeroFixActual
open LeanFormal.IUT.XiFPaper.S919GlobalWeightedInequalityActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- Correct global classical qPilot: weighted perBQPilotLog, not s994VR. -/
noncomputable def qPilotClassicalLogGlobal : Real :=
  weightedPaperV (l := l) T (perBQPilotLog (l := l) T)

/-- Global nonzero theta hull log. -/
noncomputable def thetaHullNonzeroGlobal : Real :=
  weightedPaperV (l := l) T
    (fun b => paperRootThetaHullLogNonzero (l := l) T b Measure.addHaar)

/-- Exact minimal per-b input: classical qPilot <= nonzero theta hull log. -/
def S1064PerBInequality : Prop :=
  ∀ b : Bad (nativePlaceSelection T),
    perBQPilotLog (l := l) T b ≤
      paperRootThetaHullLogNonzero (l := l) T b Measure.addHaar

/-- Weighted global inequality from the S1063 per-b inequality. -/
theorem qPilotClassicalLogGlobal_le_thetaHullNonzeroGlobal_of_perB
    (h : S1064PerBInequality (l := l) T) :
    qPilotClassicalLogGlobal (l := l) T ≤
      thetaHullNonzeroGlobal (l := l) T :=
  weightedPaperV_mono (l := l) T h

/-- INTERMEDIATE normalized-model per-b from S1070; not paper-level. -/
theorem s1064NormalizedModelPerB_actual :
    perBQPilotLog (l := l) T b ≤ perBThetaHullLog (l := l) T b :=
  S1070S1063IntermediateAuditActual.s1070NormalizedModelPerB (l := l) T b

#check qPilotClassicalLogGlobal
#check thetaHullNonzeroGlobal
#check qPilotClassicalLogGlobal_le_thetaHullNonzeroGlobal_of_perB
#check s1064NormalizedModelPerB_actual
#check S1064PerBInequality

end LeanFormal.IUT.XiFPaper.S1064GlobalQpilotClassicalThetaNonzeroActual

end