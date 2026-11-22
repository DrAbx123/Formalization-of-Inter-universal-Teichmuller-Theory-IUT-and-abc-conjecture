import tmp.sheaf.xif.paper.S1216EUniformizerDecompositionActual

noncomputable section
open scoped BigOperators Pointwise NNReal ENNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S1260UniformizerFactorReductionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open LeanFormal.IUT.XiFPaper.S831StackHaarDimensionActual
open LeanFormal.IUT.XiFPaper.S878RootStackCharacterNormDirectActual
open LeanFormal.IUT.XiFPaper.S885RootStackUniformizerNormActual
open LeanFormal.IUT.XiFPaper.S1116ERootStackDVRInstanceActual
open LeanFormal.IUT.XiFPaper.S1207EUniformizerActual
open LeanFormal.IUT.XiFPaper.S1216EUniformizerDecompositionActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- E Haar factor is multiplicative. -/
theorem rootStackHaarFactor_mul (u v : (rootStackExtension T b)ˣ) :
    rootStackHaarFactor T b (u * v) =
      rootStackHaarFactor T b u * rootStackHaarFactor T b v := by
  unfold rootStackHaarFactor
  rw [map_mul, ENNReal.coe_mul]

/-- E Haar factor is a zpow homomorphism. -/
theorem rootStackHaarFactor_zpow (u : (rootStackExtension T b)ˣ) (n : Int) :
    rootStackHaarFactor T b (u ^ n) =
      rootStackHaarFactor T b u ^ n := by
  unfold rootStackHaarFactor
  rw [map_zpow]
  exact ENNReal.coe_zpow (by
    exact_mod_cast (MeasureTheory.distribHaarChar_pos (A := rootStackExtension T b)
      (g := u)).ne')

end LeanFormal.IUT.XiFPaper.S1260UniformizerFactorReductionActual

end
