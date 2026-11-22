import tmp.sheaf.xif.paper.S238ProductTensorHullHaarActual
import tmp.sheaf.xif.paper.RootTensorHaarTransportActual

/-! # S239: exact obstruction for product Haar scalar comparison

The S227 transported tensor Haar is a measure for the transported
MeasurableSpace; the independent blockHaar is a measure for the norm-Borel
MeasurableSpace on rootTensorBlock.  They are not measures of the same type,
so Haar uniqueness cannot be applied directly.  This file records the exact
missing API; no scalar equality is faked.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S239ProductHaarScalarActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.S227TensorHullHaarActual
open LeanFormal.IUT.XiFPaper.RootTensorHaarTransportActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Exact missing common measurable/Haar API on the tensor block. -/
structure ProductHaarScalarGap where
  tensorMeasurable : MeasurableSpace (rootTensorBlock T b)
  blockMeasurable : MeasurableSpace (rootTensorBlock T b)
  commonHaar : Prop

def ProductHaarScalarGapRequired : Prop :=
  Nonempty (ProductHaarScalarGap (T := T) b)

end LeanFormal.IUT.XiFPaper.S239ProductHaarScalarActual

end
