import tmp.sheaf.xif.paper.S799LeastLambdaOPaperTargetActual
import tmp.sheaf.xif.paper.S782FiniteRootStackExtensionActual

/-! # S809: paper least lambda-O hull log via completion data or root stack

S799 proves the paper least hull log formula conditional on a completion
`ArithmeticTuplePureFractionalScalingData`.  That datum supplies a completion
generator of norm p^(-c), which need not exist for c = order/(2l).  This file
records the exact alternative: the finite root-stack extension L(mu_2l), its
actual additive Haar, the actual stack root section, and the exact bridges
still needed.  No completion root is used.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S809PaperLeastHullRootStackBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.S799LeastLambdaOPaperTargetActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
variable (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu]

/-- Exact target: paper least hull log equals the paper coefficient formula. -/
def PaperLeastHullLogFormulaTarget : Prop :=
  paperLeastLambdaOHullLog (l := l) T b mu =
    -((∑ _ : qVFamTensorV, paperRootCoefficientFamily (l := l) T b ()) *
      Real.log (qVFamTensorP T b : Real))

/-- S799's exact completion scaling datum. -/
structure PaperLeastHullCompletionData where
  data : ArithmeticTuplePureFractionalScalingData
    (qVFamTensorPlaces T b) qVFamTensorTuple (paperRootCoefficientFamily (l := l) T b)

def PaperLeastHullCompletionDataGap : Prop :=
  Nonempty (PaperLeastHullCompletionData (l := l) T b)

theorem paperLeastHullLogFormula_of_completionData
    (D : PaperLeastHullCompletionData (l := l) T b) :
    PaperLeastHullLogFormulaTarget (l := l) T b mu := by
  unfold PaperLeastHullLogFormulaTarget
  exact paperLeastLambdaOHullLog_eq_formula (l := l) T b mu D.data

/-- The actual root-stack section is a unit of the finite L(mu_2l) extension. -/
noncomputable def stackRootUnit : (rootStackExtension (l := l) T b)ˣ :=
  (stackRootSection (l := l) T b).1

theorem stackRootUnit_pow_twoL :
    stackRootUnit (l := l) T b ^ (2 * l.value) =
      (stackQSection (l := l) T b).1 :=
  congrArg Prod.fst (stackRootSection_pow (l := l) T b)

/-- Exact norm bridge still needed: the stack root unit has the paper root
norm p^(-sum paperRootCoefficientFamily). -/
def StackRootUnitNormBridge : Prop :=
  ‖(stackRootUnit (l := l) T b : rootStackExtension (l := l) T b)‖ =
    Real.rpow (qVFamTensorP T b : Real)
      (-(∑ _ : qVFamTensorV, paperRootCoefficientFamily (l := l) T b ()))

/-- Exact Haar bridge still needed: the finite-extension Haar normalized by
the stack root ball gives the paper least hull log. -/
def StackHaarNormalizationBridge : Prop :=
  Real.log
    ((rootStackHaar (l := l) T b
      (Metric.closedBall (0 : rootStackExtension (l := l) T b)
        ‖(stackRootUnit (l := l) T b : rootStackExtension (l := l) T b)‖)).toReal) =
    paperLeastLambdaOHullLog (l := l) T b mu

/-- Exact minimal bridge: completion scaling datum OR the two root-stack
bridges.  No completion root is asserted. -/
def PaperLeastHullLogExactBridge : Prop :=
  PaperLeastHullCompletionDataGap (l := l) T b ∨
    (StackRootUnitNormBridge (l := l) T b ∧
      StackHaarNormalizationBridge (l := l) T b mu)

end LeanFormal.IUT.XiFPaper.S809PaperLeastHullRootStackBridgeActual

end
