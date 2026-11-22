import tmp.sheaf.xif.paper.S899CNormOrderRamificationActual
import tmp.sheaf.xif.paper.S827PaperValueGroupNormCardActual
import tmp.sheaf.xif.paper.S836NormFormulaFixAuditActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S901NormCompatibilityActual

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
open LeanFormal.IUT.XiFPaper.S827PaperValueGroupNormCardActual
open LeanFormal.IUT.XiFPaper.S836NormFormulaFixAuditActual
open LeanFormal.IUT.XiFPaper.S888HqHthetaActual
open LeanFormal.IUT.XiFPaper.S899CNormOrderRamificationActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- Exact paper norm formula: per-b QVFamNormalizedNormCompatibility at the
actual paperRamificationExponent. -/
def S901PaperNormFormula : Prop :=
  ∀ b : Bad (nativePlaceSelection T),
    QVFamNormalizedNormCompatibility T b
      ((paperRamificationExponent (l := l) T b : Real))

theorem s901PaperNormFormula_iff_S899NormCompatibility :
    S901PaperNormFormula (l := l) T ↔ S899NormCompatibility (l := l) T :=
  Iff.rfl

/-- Integration: the paper norm formula directly supplies S899's compatibility. -/
theorem s899NormCompatibility_of_paperNormFormula
    (h : S901PaperNormFormula (l := l) T) :
    S899NormCompatibility (l := l) T :=
  h

/-- Conditional Hq under the paper norm formula and e_v=1. -/
theorem hqWeightedCNormOrder_of_paperNormFormula_ramificationOne
    (hformula : S901PaperNormFormula (l := l) T)
    (he : S899RamificationOne (l := l) T) :
    HqWeightedCNormOrder T :=
  hqWeightedCNormOrder_of_ramification_one (l := l) T hformula he

/-- S827 card package at all places. -/
def S901PaperNormValuationCards : Prop :=
  ∀ b : Bad (nativePlaceSelection T), PaperNormValuationCard T b

/-- S827 ramification alignment at all places. -/
def S901RamificationAlignments : Prop :=
  ∀ b : Bad (nativePlaceSelection T), PaperRamificationAlignment T b

/-- Exact minimal analytic datum: S827 card + alignment, together with the
still-missing norm formula.  No inhabitant is asserted. -/
def S901CardAlignmentPackage : Prop :=
  S901PaperNormValuationCards (l := l) T ∧
    S901RamificationAlignments (l := l) T

/-- The exact remaining formula target. -/
def S901NormFormulaRequired : Prop :=
  S901PaperNormFormula (l := l) T

/-- S836 dependency chain is recorded but not claimed compiled. -/
def S901NormFormulaDependencyChain : List String :=
  NormFormulaDependencyChain

end LeanFormal.IUT.XiFPaper.S901NormCompatibilityActual

end
