import tmp.sheaf.xif.paper.PaperRootExtensionHaarActual
import Mathlib.Topology.Algebra.Valued.NormedValued
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnits
import Mathlib.RingTheory.Valuation.Integers

/-! # Actual NNReal-valued structure on the finite root extension -/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section
open scoped BigOperators Pointwise NNReal Valued

namespace LeanFormal.IUT.XiFPaper.PaperRootExtensionValuedActual

open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- L is ultrametric as a subfield of the ultrametric ambient. -/
noncomputable instance rootNormedExtensionUltrametric :
    IsUltrametricDist (rootNormedExtension T b) := by
  letI h : IsUltrametricDist (rootNormedAmbient T b) :=
    inferInstanceAs (IsUltrametricDist (SourceAlgebraicClosure (qVFamTensorPlace T b)))
  infer_instance

/-- Actual NNReal-valued structure on L, obtained from the spectral norm. -/
noncomputable instance rootNormedExtensionValuedNNReal :
    Valued (rootNormedExtension T b) ℝ≥0 :=
  NormedField.toValued

/-- Actual integral ring of L for the NNReal-valued structure. -/
abbrev rootNormedExtensionIntegers : Type :=
  Integers (rootNormedExtension T b)

/-- Exact obstruction: the norm value group is ℝ≥0, not the discrete value group
WithZero (Multiplicative ℤ); hence no uniformizer/discrete DVR is produced from
this structure alone. -/
structure RootNormedExtensionDiscreteValuationGap where
  discreteValued : Valued (rootNormedExtension T b)
    (WithZero (Multiplicative ℤ))
  discreteIntegers : Type
  discreteIntegers_eq : discreteIntegers = Integers (rootNormedExtension T b)
  isDVR : Prop

/-- Exact missing discrete DVR/uniformizer object. -/
def RootNormedExtensionDiscreteValuationGapRequired : Prop :=
  Nonempty (RootNormedExtensionDiscreteValuationGap (T := T) (b := b))

end LeanFormal.IUT.XiFPaper.PaperRootExtensionValuedActual

end