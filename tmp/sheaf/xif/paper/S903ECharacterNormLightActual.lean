import tmp.sheaf.xif.paper.S878RootStackCharacterNormDirectActual
import tmp.sheaf.xif.paper.S885RootStackUniformizerNormActual
/-! # S903: lightweight E character/norm comparison (no S887 expansion)
Uses S878's factor-norm reduction and S885's exact E uniformizer datum; does
not import S887/S902. -/
noncomputable section
open scoped BigOperators Pointwise NNReal ENNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S903ECharacterNormLightActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open LeanFormal.IUT.XiFPaper.S831StackHaarDimensionActual
open LeanFormal.IUT.XiFPaper.S824RootStackyHaarVolumeActual
open LeanFormal.IUT.XiFPaper.S878RootStackCharacterNormDirectActual
open LeanFormal.IUT.XiFPaper.S885RootStackUniformizerNormActual
open MeasureTheory
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
/-- Exact E factor-norm input. -/
def S903ECharacterNormExactInput : Prop :=
  RootStackHaarFactorNormPow (l := l) T b (dQpFactor (l := l) T b)
/-- Lightweight reduction: exact factor-norm input gives the E comparison. -/
theorem s903_hchar_of_exactInput
    (h : S903ECharacterNormExactInput (l := l) T b) :
    StackCharacterNormComparison (l := l) T b (dQpFactor (l := l) T b) :=
  stackCharacterNormComparison_of_factorNormPow (l := l) T b _ h
/-- Exact unit/uniformizer data (S885) still needed for a direct proof. -/
def S903EUniformizerExactDataRequired : Prop :=
  S885UniformizerDataRequired (l := l) T b
/-- S885 data gives the factor-norm input; hence the E comparison. -/
theorem s903_hchar_of_uniformizerData
    (D : S885UniformizerData (l := l) T b) :
    StackCharacterNormComparison (l := l) T b (dQpFactor (l := l) T b) :=
  s903_hchar_of_exactInput (l := l) T b D.factor_norm_pow
end LeanFormal.IUT.XiFPaper.S903ECharacterNormLightActual
