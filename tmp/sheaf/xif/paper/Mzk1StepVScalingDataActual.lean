import tmp.sheaf.xif.paper.Mzk1StepVVolumeActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceStepVAssembly
import Mathlib.Tactic

/-!
# Mzk1StepVScalingDataActual

Task-122: construction of ArithmeticTuplePureFractionalScalingData for the
one-factor StepV coefficient.

Given actual generators g_i with norms
  ||g_i|| = p ^ (-(stepVScalingCoefficient i)),
the production constructor arithmeticTuplePureFractionalScalingData_ofGenerator
fills all fields of ArithmeticTuplePureFractionalScalingData.  Composing with
stepVRegion_volume_eq_of_scalingData gives the unconditional (given generators)
volume identity
  arithmeticTupleNormalizedLogVolume (stepVRegion label) = S3029StepVTerm label.

The exact remaining source object is StepVQRootSource: actual generators
qroot^{label^2} at istar (and unit generators at the zero factors) together with
their norm identity.  It is recorded as a named source gap, not asserted.

No sorry/axiom/True/PUnit/toy.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1StepVScalingDataActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.Mzk1StepVVolumeActual
open LeanFormal.IUT.XiFPaper.S3029StepVAlignmentActual
open MeasureTheory

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] [DecidableEq ι] {V : ι -> Type w} [∀ i, Fintype (V i)]
variable (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
variable (tuple : (i : ι) -> V i) (istar : ι)
variable (jValue : CommonPrimeCompletion (places istar (tuple istar)))
variable (l label : Nat)

/-- Actual scaling data from explicit generators with the StepV norm. -/
noncomputable def stepVScalingDataOfGenerator
    (g : (i : ι) -> CommonPrimeCompletion (places i (tuple i)))
    (hg : forall i, ‖g i‖ =
      (p : Real) ^ (-(stepVScalingCoefficient places tuple istar jValue l label i))) :
    ArithmeticTuplePureFractionalScalingData (p := p) places tuple
      (stepVScalingCoefficient places tuple istar jValue l label) :=
  arithmeticTuplePureFractionalScalingData_ofGenerator
    (p := p) places tuple
    (stepVScalingCoefficient places tuple istar jValue l label) g hg

/-- Volume identity with explicit actual generators. -/
theorem stepVRegion_volume_eq_ofGenerator
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    (mu : Measure (ArithmeticTensorTupleBlock places tuple)) [Measure.IsAddHaarMeasure mu]
    (g : (i : ι) -> CommonPrimeCompletion (places i (tuple i)))
    (hg : forall i, ‖g i‖ =
      (p : Real) ^ (-(stepVScalingCoefficient places tuple istar jValue l label i))) :
    arithmeticTupleNormalizedLogVolume places tuple mu
        (stepVRegion places tuple istar jValue l label) =
      S3029StepVTerm places tuple istar jValue l label :=
  stepVRegion_volume_eq_of_scalingData (p := p) places tuple istar jValue l mu label
    (stepVScalingDataOfGenerator (p := p) places tuple istar jValue l label g hg)

/-- Exact source object for the actual qroot generators: all factors, with the
non-istar factors having norm one (coefficient zero). -/
structure StepVQRootSource where
  generator : (i : ι) -> CommonPrimeCompletion (places i (tuple i))
  generator_norm : forall i, ‖generator i‖ =
    (p : Real) ^ (-(stepVScalingCoefficient places tuple istar jValue l label i))

/-- The exact remaining source gap: existence of the qroot^{label^2}/unit
generators with the required norms. -/
def StepVQRootSourceGap : Prop :=
  Nonempty (StepVQRootSource (p := p) places tuple istar jValue l label)

#check stepVScalingDataOfGenerator
#check stepVRegion_volume_eq_ofGenerator
#check StepVQRootSource
#check StepVQRootSourceGap

end LeanFormal.IUT.XiFPaper.Mzk1StepVScalingDataActual

end
