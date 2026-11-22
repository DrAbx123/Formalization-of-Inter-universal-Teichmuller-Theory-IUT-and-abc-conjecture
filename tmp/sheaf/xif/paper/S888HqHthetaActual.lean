import tmp.sheaf.xif.paper.S877WeightedIdentificationActual
import tmp.sheaf.xif.paper.S810LeastHullPaperCarrierActual
import tmp.sheaf.xif.paper.S734PaperCoefficientBridgeActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S888HqHthetaActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.S876CorrectedGlobalTargetActual
open LeanFormal.IUT.XiFPaper.S877WeightedIdentificationActual
open LeanFormal.IUT.XiFPaper.S810LeastHullPaperCarrierActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- Corrected Htheta, without the spurious extra 2l. -/
def HthetaNoTwoL : Prop :=
  S860GlobalCor312AuditActual.thetaHullScalar T =
    paperLeastHullWeightedLog T

/-- S877 Htheta means HthetaNoTwoL plus the extra equation 2l*L = L. -/
theorem s877_htheta_iff_extra (hno : HthetaNoTwoL T) :
    HthetaCorrected T ↔
      (2 * (l.value : Real)) * paperLeastHullWeightedLog T =
        paperLeastHullWeightedLog T := by
  unfold HthetaCorrected
  rw [hno]

/-- Corrected target follows from HqCorrected and HthetaNoTwoL. -/
theorem correctedGlobalTarget_of_hq_hthetaNo
    (hdata : ∀ b : Bad (nativePlaceSelection T), PaperLeastHullData T b)
    (hq : HqCorrected T) (htheta : HthetaNoTwoL T) :
    CorrectedGlobalTarget T := by
  unfold CorrectedGlobalTarget
  rw [hq, htheta]
  rw [paperQPilotWeightedLeast_eq_leastHullWeighted T hdata]

/-- Hq exact weighted c_norm=order condition. -/
def HqWeightedCNormOrder : Prop :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b *
      ((qVFamNormalizedCoefficient (l := l) T b -
        ((qVFamily T b).order : Real)) *
        Real.log (qVFamTensorP T b : Real)) = 0

/-- Htheta via least hull: the old per-b paper hull log equals the least-hull
log at every b. -/
def HthetaLeastHullCondition : Prop :=
  ∀ b : Bad (nativePlaceSelection T),
    S810LeastHullPaperCarrierActual.S810LeastEqualsOldUnion T b

/-- Exact minimal gap of S888. -/
def CorrectedHqHthetaMinimalGap : Prop :=
  HqWeightedCNormOrder T ∧ HthetaNoTwoL T

end LeanFormal.IUT.XiFPaper.S888HqHthetaActual
end