import tmp.sheaf.xif.paper.S887RootStackHaarDetViaS861EActual
import tmp.sheaf.xif.paper.S885RootStackUniformizerNormActual

/-! # S897: E character/norm via DVR/uniformizer data

S878 reduces the E character/norm comparison to the exact factor-norm
formula `RootStackHaarFactorNormPow dQpFactor`.  S885 packages the exact
DVR/uniformizer data whose `factor_norm_pow` field is precisely that formula.
This file proves the conditional actual implication and records the exact
minimal E uniformizer input.  No no-go and no fake formula.
-/

noncomputable section
open scoped BigOperators Pointwise NNReal ENNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S897ECharacterNormViaUniformizerActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open LeanFormal.IUT.XiFPaper.S831StackHaarDimensionActual
open LeanFormal.IUT.XiFPaper.S878RootStackCharacterNormDirectActual
open LeanFormal.IUT.XiFPaper.S885RootStackUniformizerNormActual
open LeanFormal.IUT.XiFPaper.S887RootStackHaarDetViaS861EActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- From the exact factor-norm formula, the E character/norm comparison at
`dQpFactor` follows. -/
theorem rootStackCharacterNormComparisonAtDQp_of_factorNormPow
    (h : RootStackHaarFactorNormPow (l := l) T b (dQpFactor (l := l) T b)) :
    RootStackCharacterNormComparisonAtDQp (l := l) T b := by
  unfold RootStackCharacterNormComparisonAtDQp RootStackCharacterNormComparisonAt
  exact stackCharacterNormComparison_of_factorNormPow (l := l) T b _ h

/-- Exact conditional actual: S885 uniformizer data gives the E character/norm
comparison at dQpFactor. -/
theorem rootStackCharacterNormComparisonAtDQp_of_uniformizerData
    (D : S885UniformizerData (l := l) T b) :
    RootStackCharacterNormComparisonAtDQp (l := l) T b :=
  rootStackCharacterNormComparisonAtDQp_of_factorNormPow (l := l) T b D.factor_norm_pow

/-- Exact minimal E uniformizer/norm input. -/
def S897ECharacterNormExactInput : Prop :=
  S885UniformizerDataRequired (l := l) T b

/-- Given the exact input, the E character/norm comparison is available. -/
theorem rootStackCharacterNormComparisonAtDQp_of_exactInput
    (h : S897ECharacterNormExactInput (l := l) T b) :
    RootStackCharacterNormComparisonAtDQp (l := l) T b := by
  rcases h with ⟨D⟩
  exact rootStackCharacterNormComparisonAtDQp_of_uniformizerData (l := l) T b D

end LeanFormal.IUT.XiFPaper.S897ECharacterNormViaUniformizerActual

end
