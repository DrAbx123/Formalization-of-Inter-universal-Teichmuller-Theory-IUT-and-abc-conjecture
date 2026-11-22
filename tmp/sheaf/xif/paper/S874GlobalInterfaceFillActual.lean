import tmp.sheaf.xif.paper.S868GlobalPaperTargetInterfaceActual
import tmp.sheaf.xif.paper.S801PaperHullLogActual
import tmp.sheaf.xif.paper.S857OtriLogVolumeInterfaceActual

/-! # S874: filling the global paper target interface

S801 gives the actual least-hull/paper-qPilot region equality at every bad
place.  The global corrected target is reduced to per-b 2l inequalities and
the global Vbad weighted sum.  The remaining exact inputs are the per-b
paper hull-log formula data and the global 2l corrected target itself. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S874GlobalInterfaceFillActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S860GlobalCor312AuditActual
open LeanFormal.IUT.XiFPaper.S801PaperHullLogActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.S797PaperOrderRegionContainmentActual
open LeanFormal.IUT.XiFPaper.S868GlobalPaperTargetInterfaceActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- Actual least-hull / paper qPilot region equality at all bad places. -/
def leastHullPaperRegionGlobal : Prop :=
  ∀ b : Bad (nativePlaceSelection T),
    paperLeastLambdaOHull (l := l) T b = paperQPilotRegionPaperOrder T b

theorem leastHullPaperRegionGlobal_actual :
    leastHullPaperRegionGlobal (l := l) T :=
  fun b => S801PaperHullLogActual.paperLeastLambdaOHull_eq_paperQPilotRegion
    (l := l) T b

/-- Exact paper hull-log formula data at all bad places. -/
def paperHullFormulaGapGlobal : Prop :=
  ∀ b : Bad (nativePlaceSelection T),
    PaperHullLogFormulaRequired (l := l) T b

/-- Exact per-b corrected target: the 2l factor is applied per place. -/
def correctedTargetPerB : Prop :=
  ∀ b : Bad (nativePlaceSelection T),
    perBQPilotLog (l := l) T b ≤
      (2 * (l.value : Real)) * perBThetaHullLog (l := l) T b

/-- Actual weighted reduction: per-b 2l inequalities imply the global corrected
target after Vbad weights. -/
theorem correctedTarget_of_perB
    (h : correctedTargetPerB (l := l) T) :
    S860GlobalCor312AuditActual.weightedQPilot T ≤
      (2 * (l.value : Real)) *
        S860GlobalCor312AuditActual.thetaHullScalar T := by
  unfold S860GlobalCor312AuditActual.weightedQPilot
    S860GlobalCor312AuditActual.thetaHullScalar globalQPilotLog globalThetaHullLog
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b _
  have hw : 0 ≤ nativeBadLocalWeight T b :=
    nativeBadLocalWeight_nonneg T b
  calc
    nativeBadLocalWeight T b * perBQPilotLog (l := l) T b ≤
      nativeBadLocalWeight T b *
        ((2 * (l.value : Real)) * perBThetaHullLog (l := l) T b) :=
      mul_le_mul_of_nonneg_left (h b) hw
    _ = (2 * (l.value : Real)) *
        (nativeBadLocalWeight T b * perBThetaHullLog (l := l) T b) := by ring

/-- Global interface with the actual least-hull field and exact formula-gap
field, conditional only on the global corrected target. -/
noncomputable def globalPaperTargetInterfaceFilled
    (hcorrected :
      S860GlobalCor312AuditActual.weightedQPilot T ≤
        (2 * (l.value : Real)) *
          S860GlobalCor312AuditActual.thetaHullScalar T) :
    GlobalPaperTargetInterface T :=
  globalPaperTargetInterface (l := l) T
    (S860GlobalCor312AuditActual.PaperProcessionWeightGap (l := l))
    (S860GlobalCor312AuditActual.ProcessionTargetActual T)
    (S860GlobalCor312AuditActual.PaperProcessionWeightGap (l := l))
    (S860GlobalCor312AuditActual.ProcessionTargetActual T)
    (S860GlobalCor312AuditActual.CorrectedQPilotTarget T)
    (leastHullPaperRegionGlobal (l := l) T)
    (paperHullFormulaGapGlobal (l := l) T)
    hcorrected

end LeanFormal.IUT.XiFPaper.S874GlobalInterfaceFillActual
end
