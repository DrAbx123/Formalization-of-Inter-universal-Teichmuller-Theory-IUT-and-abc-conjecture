import tmp.sheaf.xif.paper.S860GlobalCor312AuditActual
import tmp.sheaf.xif.paper.S801PaperHullLogActual
import tmp.sheaf.xif.paper.S793PaperLeastLambdaOHullActual
import tmp.sheaf.xif.paper.S797PaperOrderRegionContainmentActual
import tmp.sheaf.xif.paper.S775PaperOrderQPilotCorrectionActual
import tmp.sheaf.xif.paper.S773RootCorrectedPaperTargetActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S868GlobalPaperTargetInterfaceActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.S860GlobalCor312AuditActual
open LeanFormal.IUT.XiFPaper.S801PaperHullLogActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.S797PaperOrderRegionContainmentActual
open LeanFormal.IUT.XiFPaper.S775PaperOrderQPilotCorrectionActual
open LeanFormal.IUT.XiFPaper.S773RootCorrectedPaperTargetActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- Actual least-hull paper region equality, filling the non-global hull field. -/
theorem leastHullPaperRegion_actual (b : Bad (nativePlaceSelection T)) :
    paperLeastLambdaOHull T b =
      paperQPilotRegionPaperOrder T b :=
  paperLeastLambdaOHull_eq_paperQPilotRegion T b

/-- Exact paper hull-log formula gap at b (S801 data). -/
def PaperHullLogFormulaGap (b : Bad (nativePlaceSelection T)) : Prop :=
  PaperHullLogFormulaRequired (l := l) T b

structure GlobalPaperTargetInterface where
  weightedQPilot : Real
  weightedQPilot_eq : weightedQPilot = S860GlobalCor312AuditActual.weightedQPilot T
  thetaHullScalar : Real
  thetaHullScalar_eq : thetaHullScalar = S860GlobalCor312AuditActual.thetaHullScalar T
  correctedTarget :
    weightedQPilot ≤ (2 * (l.value : Real)) * thetaHullScalar
  lStarProcession : Prop
  vbadWeightReconciliation : Prop
  ind1 : Prop
  ind2 : Prop
  ind3 : Prop
  leastHullPaperRegion : Prop
  paperHullFormulaGap : Prop

/-- The paper global signed conclusion from the corrected magnitude inequality. -/
def PaperGlobalCor312Conclusion (I : GlobalPaperTargetInterface T) : Prop :=
  -I.thetaHullScalar ≤ -I.weightedQPilot / (2 * (l.value : Real))

theorem paperCor312_of_globalInterface
    (I : GlobalPaperTargetInterface T) :
    PaperGlobalCor312Conclusion T I := by
  unfold PaperGlobalCor312Conclusion
  have h2 : (0 : Real) < 2 * (l.value : Real) := by
    have := l.prime.pos
    positivity
  rw [le_div_iff₀ h2]
  have h := I.correctedTarget
  nlinarith

noncomputable def globalPaperTargetInterface
    (hlstar : Prop) (hvbad : Prop) (hi1 hi2 hi3 : Prop)
    (hleast : Prop) (hformula : Prop)
    (hcorrected :
      S860GlobalCor312AuditActual.weightedQPilot T ≤
        (2 * (l.value : Real)) * S860GlobalCor312AuditActual.thetaHullScalar T) :
    GlobalPaperTargetInterface T where
  weightedQPilot := S860GlobalCor312AuditActual.weightedQPilot T
  weightedQPilot_eq := rfl
  thetaHullScalar := S860GlobalCor312AuditActual.thetaHullScalar T
  thetaHullScalar_eq := rfl
  correctedTarget := hcorrected
  lStarProcession := hlstar
  vbadWeightReconciliation := hvbad
  ind1 := hi1
  ind2 := hi2
  ind3 := hi3
  leastHullPaperRegion := hleast
  paperHullFormulaGap := hformula

end LeanFormal.IUT.XiFPaper.S868GlobalPaperTargetInterfaceActual
end