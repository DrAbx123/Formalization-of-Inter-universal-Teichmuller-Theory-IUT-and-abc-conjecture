import tmp.sheaf.xif.paper.S885RootStackUniformizerNormActual
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual

/-! # S893: exact minimal instance requirements for E=rootStackExtension

Mathlib already gives E a NontriviallyNormedField structure because E is an
IntermediateField.  The tree has S782 CompleteSpace/ProperSpace/FiniteDimensional
instances.  The still-missing instances needed for the integer-ring DVR and the
uniformizer are recorded exactly below:

  IsUltrametricDist (rootNormedAmbient T b)
  NormedAlgebra Qp (rootNormedExtension T b)
  NormedAlgebra Qp (rootStackExtension T b)

No instance and no uniformizer is fabricated. -/

noncomputable section
open scoped BigOperators Pointwise NNReal ENNReal Valued
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S893RootStackDVRInstanceActual

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

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Exact missing instance 1: ambient ultrametricity. -/
def S893AmbientUltrametricRequired : Prop :=
  IsUltrametricDist (rootNormedAmbient T b)

/-- Exact missing instance 2: Qp-normed-algebra structure on L. -/
def S893NormedAlgebraQpLRequired : Prop :=
  Nonempty (NormedAlgebra ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b))

/-- Exact missing instance 3: Qp-normed-algebra structure on E. -/
def S893NormedAlgebraQpERequired : Prop :=
  Nonempty (NormedAlgebra ℚ_[(qVFamTensorP T b)] (rootStackExtension T b))

/-- Exact bundle of the remaining instance requirements. -/
def S893RootStackDVRInstanceInputs : Prop :=
  S893AmbientUltrametricRequired (l := l) T b ∧
    S893NormedAlgebraQpLRequired (l := l) T b ∧
      S893NormedAlgebraQpERequired (l := l) T b

/-- Exact uniformizer data required after DVR (S885). -/
def S893UniformizerDataRequired : Prop :=
  S885UniformizerDataRequired (l := l) T b

/-- Exact combined requirement for filling S885 uniformly. -/
def S893RootStackDVRUniformizerRequired : Prop :=
  S893RootStackDVRInstanceInputs (l := l) T b ∧
    S893UniformizerDataRequired (l := l) T b

end LeanFormal.IUT.XiFPaper.S893RootStackDVRInstanceActual

end
