import tmp.sheaf.xif.paper.S878RootStackCharacterNormDirectActual

/-! # S885: E=rootStackExtension uniformizer/norm datum

A DVR uniformizer pi_E of Integers(E), the unit-factor proposition, the
uniformizer-factor proposition and the DVR decomposition are bundled as exact
input.  From them the S878 RootStackUniformizerNormData is filled.  The actual
DVR existence proof and the E norm formula are not fabricated; they are the
exact minimal inputs S885UniformizerDataRequired. -/

noncomputable section
open scoped BigOperators Pointwise NNReal ENNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S885RootStackUniformizerNormActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open LeanFormal.IUT.XiFPaper.S831StackHaarDimensionActual
open LeanFormal.IUT.XiFPaper.S878RootStackCharacterNormDirectActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Exact unit-factor proposition. -/
def S885UnitFactorOne : Prop :=
  ∀ u : (rootStackExtension T b)ˣ,
    ‖(u : rootStackExtension T b)‖ = 1 →
      rootStackHaarFactor (l := l) T b u = 1

/-- Exact DVR decomposition at a chosen uniformizer. -/
def S885UnitDecomposition (pi : (rootStackExtension T b)ˣ) : Prop :=
  ∀ u : (rootStackExtension T b)ˣ,
    ∃ (n : Int) (eps : (rootStackExtension T b)ˣ),
      u = eps * pi ^ n ∧ ‖(eps : rootStackExtension T b)‖ = 1

/-- Exact uniformizer-factor proposition. -/
def S885UniformizerFactor (pi : (rootStackExtension T b)ˣ) : Prop :=
  rootStackHaarFactor (l := l) T b pi =
    ENNReal.ofReal
      (‖(pi : rootStackExtension T b)‖ ^ (dQpFactor (l := l) T b))

/-- Exact minimal E uniformizer/norm input. -/
structure S885UniformizerData where
  pi : (rootStackExtension T b)ˣ
  pi_norm_lt_one : ‖(pi : rootStackExtension T b)‖ < 1
  unit_factor_one : S885UnitFactorOne (l := l) T b
  decomposition : S885UnitDecomposition (l := l) T b pi
  uniformizer_factor : S885UniformizerFactor (l := l) T b pi
  factor_norm_pow : RootStackHaarFactorNormPow (l := l) T b
    (dQpFactor (l := l) T b)

/-- Fill S878 RootStackUniformizerNormData from the exact uniformizer input. -/
noncomputable def s885RootStackUniformizerNormData_of_data
    (data : S885UniformizerData (l := l) T b) :
    RootStackUniformizerNormData (l := l) T b where
  uniformizer := data.pi
  dvr_uniformizer := ‖(data.pi : rootStackExtension T b)‖ < 1
  unit_factor_one := S885UnitFactorOne (l := l) T b
  uniformizer_factor := S885UniformizerFactor (l := l) T b data.pi
  factor_norm_pow := RootStackHaarFactorNormPow (l := l) T b
    (dQpFactor (l := l) T b)

/-- S878 uniformizer datum follows from the exact input. -/
theorem s885RootStackUniformizerNormDataRequired_of_data
    (data : S885UniformizerData (l := l) T b) :
    RootStackUniformizerNormDataRequired (l := l) T b :=
  ⟨s885RootStackUniformizerNormData_of_data (l := l) T b data⟩

/-- Exact minimal required input. -/
def S885UniformizerDataRequired : Prop :=
  Nonempty (S885UniformizerData (l := l) T b)

/-- Exact factor-norm target equivalently reduced to the uniformizer data. -/
def S885RootStackCharacterNormExactGoal : Prop :=
  RootStackHaarFactorNormPow (l := l) T b (dQpFactor (l := l) T b)

end LeanFormal.IUT.XiFPaper.S885RootStackUniformizerNormActual

end
