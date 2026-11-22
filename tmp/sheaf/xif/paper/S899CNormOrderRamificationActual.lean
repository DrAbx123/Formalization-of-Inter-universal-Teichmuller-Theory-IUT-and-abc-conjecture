import tmp.sheaf.xif.paper.S894HqPositiveActual
import tmp.sheaf.xif.paper.S826CNormOrderRamificationActual
import tmp.sheaf.xif.paper.S840QVFamRamificationAuditActual
import tmp.sheaf.xif.paper.S819PaperRootCompletionGeneratorActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S899CNormOrderRamificationActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientOrderAuditActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S819PaperRootCompletionGeneratorActual
open LeanFormal.IUT.XiFPaper.S826CNormOrderRamificationActual
open LeanFormal.IUT.XiFPaper.S840QVFamRamificationAuditActual
open LeanFormal.IUT.XiFPaper.S888HqHthetaActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.S894HqPositiveActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Actual e = paperRamificationExponent norm compatibility, per place. -/
def S899NormCompatibility : Prop :=
  ∀ b : Bad (nativePlaceSelection T),
    QVFamNormalizedNormCompatibility T b
      ((paperRamificationExponent (l := l) T b : Real))

/-- e_v = 1, per place, for the paper ramification exponent. -/
def S899RamificationOne : Prop :=
  ∀ b : Bad (nativePlaceSelection T),
    paperRamificationExponent (l := l) T b = 1

/-- S826 + actual paperRamificationExponent: e_v = 1 gives c_norm = order. -/
theorem cNorm_eq_order_of_ramification_one
    (hcompat : QVFamNormalizedNormCompatibility T b
      ((paperRamificationExponent (l := l) T b : Real)))
    (he : paperRamificationExponent (l := l) T b = 1) :
    qVFamNormalizedCoefficient (l := l) T b = ((qVFamily T b).order : Real) := by
  have hepos : (0 : Real) < (paperRamificationExponent (l := l) T b : Real) := by
    exact_mod_cast qVFamRamificationExponent_pos (l := l) T b
  have he1 : ((paperRamificationExponent (l := l) T b : Real)) = 1 := by
    rw [he]
    norm_num
  exact (qVFamNormalizedCoefficient_eq_order_iff_e_eq_one (l := l) T b
    ((paperRamificationExponent (l := l) T b : Real)) hepos hcompat).mpr he1

/-- Actual HqWeightedCNormOrder under e_v=1 and the S826 norm compatibility. -/
theorem hqWeightedCNormOrder_of_ramification_one
    (hcompat : S899NormCompatibility (l := l) T)
    (he : S899RamificationOne (l := l) T) :
    HqWeightedCNormOrder (l := l) T := by
  apply hqWeightedCNormOrder_of_cNorm_eq_order (l := l) T
  intro b
  exact cNorm_eq_order_of_ramification_one (l := l) T b (hcompat b) (he b)

/-- Pointwise e_v=1 form with explicit place. -/
theorem hq_term_eq_zero_of_ramification_one
    (hcompat : S899NormCompatibility (l := l) T)
    (he : S899RamificationOne (l := l) T)
    (b : Bad (nativePlaceSelection T)) :
    nativeBadLocalWeight T b *
      ((qVFamNormalizedCoefficient (l := l) T b -
        ((qVFamily T b).order : Real)) *
        Real.log (qVFamTensorP T b : Real)) = 0 := by
  have hb := cNorm_eq_order_of_ramification_one (l := l) T b (hcompat b) (he b)
  rw [hb]
  ring

/-- Exact conditional hypotheses; no inhabitant is asserted. -/
def S899HqConditionalHypotheses : Prop :=
  S899NormCompatibility (l := l) T ∧ S899RamificationOne (l := l) T

/-- Exact remaining actual Hq target. -/
def S899HqActualRequired : Prop :=
  HqWeightedCNormOrder (l := l) T

end LeanFormal.IUT.XiFPaper.S899CNormOrderRamificationActual

end
