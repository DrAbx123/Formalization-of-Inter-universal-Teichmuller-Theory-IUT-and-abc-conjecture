import tmp.sheaf.xif.paper.S1337GeneralFactorNormPowActual
import tmp.sheaf.xif.paper.S897ECharacterNormViaUniformizerActual
import tmp.sheaf.xif.paper.S886ENormExtensionFormulaActual
import tmp.sheaf.xif.paper.S865RootHaarFactorNormPowActual

noncomputable section
open scoped BigOperators Pointwise NNReal ENNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S1363S885ConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open LeanFormal.IUT.XiFPaper.S831StackHaarDimensionActual
open LeanFormal.IUT.XiFPaper.S824RootStackyHaarVolumeActual
open LeanFormal.IUT.XiFPaper.S878RootStackCharacterNormDirectActual
open LeanFormal.IUT.XiFPaper.S885RootStackUniformizerNormActual
open LeanFormal.IUT.XiFPaper.S887RootStackHaarDetViaS861EActual
open LeanFormal.IUT.XiFPaper.S897ECharacterNormViaUniformizerActual
open LeanFormal.IUT.XiFPaper.S1337GeneralFactorNormPowActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Actual S885 data gives the S878 DVR uniformizer datum. -/
theorem s1363RootStackUniformizerNormDataRequired_actual :
    RootStackUniformizerNormDataRequired (l := l) T b :=
  s885RootStackUniformizerNormDataRequired_of_data
    (l := l) T b (s1337UniformizerData_actual (l := l) T b)

/-- Actual S885 data gives the E character/norm comparison at dQpFactor. -/
theorem s1363RootStackCharacterNormComparisonAtDQp_actual :
    RootStackCharacterNormComparisonAtDQp (l := l) T b :=
  rootStackCharacterNormComparisonAtDQp_of_uniformizerData
    (l := l) T b (s1337UniformizerData_actual (l := l) T b)

/-- Actual S885 data gives the S824 stack character/norm comparison. -/
theorem s1363StackCharacterNormComparison_actual :
    StackCharacterNormComparison (T := T) (b := b) (dQpFactor T b) :=
  stackCharacterNormComparison_of_factorNormPow (T := T) (b := b)
    (dQpFactor T b) (s1337RootStackHaarFactorNormPow_actual T b)

end LeanFormal.IUT.XiFPaper.S1363S885ConsumerActual

end
