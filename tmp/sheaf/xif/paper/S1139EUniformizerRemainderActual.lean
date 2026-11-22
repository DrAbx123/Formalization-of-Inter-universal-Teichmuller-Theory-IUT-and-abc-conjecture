import tmp.sheaf.xif.paper.S1116ERootStackDVRInstanceActual
import tmp.sheaf.xif.paper.S1124EUnitFactorActual

noncomputable section
open scoped BigOperators Pointwise NNReal ENNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S1139EUniformizerRemainderActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open LeanFormal.IUT.XiFPaper.S831StackHaarDimensionActual
open LeanFormal.IUT.XiFPaper.S878RootStackCharacterNormDirectActual
open LeanFormal.IUT.XiFPaper.S885RootStackUniformizerNormActual
open LeanFormal.IUT.XiFPaper.S1116ERootStackDVRInstanceActual
open LeanFormal.IUT.XiFPaper.S1124EUnitFactorActual
open LeanFormal.IUT.LocalFieldIntegralUnits
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- The S1116 actual DVR uniformizer, as a field unit of E. -/
noncomputable def rootStackUniformizerField : (rootStackExtension T b)ˣ :=
  Units.mk0 (algebraMap (Integers (rootStackExtension T b))
    (rootStackExtension T b) (rootStackUniformizer (l := l) T b)) (by
      intro h
      have hzero : rootStackUniformizer (l := l) T b = 0 :=
        IsFractionRing.injective (Integers (rootStackExtension T b))
          (rootStackExtension T b) h
      exact (rootStackUniformizer_irreducible (l := l) T b).ne_zero hzero)

/-- Exact norm<1 condition for the actual S1116 uniformizer. -/
def S1139UniformizerNormLtOne : Prop :=
  ‖(rootStackUniformizerField (l := l) T b :
    rootStackExtension T b)‖ < 1

/-- Exact DVR decomposition condition for the actual S1116 uniformizer. -/
def S1139DVRDecomposition : Prop :=
  S885UnitDecomposition (l := l) T b (rootStackUniformizerField (l := l) T b)

/-- Exact uniformizer-factor condition. -/
def S1139UniformizerFactor : Prop :=
  S885UniformizerFactor (l := l) T b (rootStackUniformizerField (l := l) T b)

/-- Exact factor-norm power formula. -/
def S1139FactorNormPow : Prop :=
  RootStackHaarFactorNormPow (l := l) T b (dQpFactor (l := l) T b)

/-- Exact remaining E uniformizer data on the actual S1116 uniformizer. -/
def S1139ExactMinimum : Prop :=
  S1139UniformizerNormLtOne (l := l) T b ∧
    S1139DVRDecomposition (l := l) T b ∧
      S1139UniformizerFactor (l := l) T b ∧
        S1139FactorNormPow (l := l) T b

/-- The exact minimum plus S1124 actual unit-factor yields S885 data. -/
noncomputable def s1139UniformizerData_of_exact
    (h : S1139ExactMinimum (l := l) T b) :
    S885UniformizerData (l := l) T b where
  pi := rootStackUniformizerField (l := l) T b
  pi_norm_lt_one := h.1
  unit_factor_one := s1124UnitFactorOne_actual (l := l) T b
  decomposition := h.2.1
  uniformizer_factor := h.2.2.1
  factor_norm_pow := h.2.2.2

/-- Exact minimum suffices for S885 data required. -/
theorem s1139RootStackUniformizerNormDataRequired_of_exact
    (h : S1139ExactMinimum (l := l) T b) :
    S885UniformizerDataRequired (l := l) T b :=
  ⟨s1139UniformizerData_of_exact (l := l) T b h⟩

end LeanFormal.IUT.XiFPaper.S1139EUniformizerRemainderActual

end
