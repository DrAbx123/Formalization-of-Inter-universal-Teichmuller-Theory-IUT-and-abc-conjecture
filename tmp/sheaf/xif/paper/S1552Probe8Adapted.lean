import tmp.sheaf.xif.paper.S1512ProductHaarScalingActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlacePadicScalarStructure

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace

namespace Probe8
variable (P : NumberField.FinitePlace ℚ)

example (x y : Completion (comap P)) :
    rationalCompletionPadicEquiv P (x + y) =
      rationalCompletionPadicEquiv P x + rationalCompletionPadicEquiv P y :=
  map_add (rationalCompletionPadicEquiv P) x y

example (x y : Completion (comap P)) :
    rationalCompletionPadicEquiv P (x * y) =
      rationalCompletionPadicEquiv P x * rationalCompletionPadicEquiv P y :=
  map_mul (rationalCompletionPadicEquiv P) x y

example : Function.Injective (rationalCompletionPadicEquiv P) :=
  (rationalCompletionPadicEquiv P).injective

example : Function.Surjective (rationalCompletionPadicEquiv P) :=
  (rationalCompletionPadicEquiv P).surjective

example (x : Completion (comap P)) :
    (rationalCompletionPadicEquiv P).symm (rationalCompletionPadicEquiv P x) = x :=
  (rationalCompletionPadicEquiv P).left_inv x

example : Continuous (rationalCompletionPadicEquiv P) :=
  (rationalCompletionPadicEquiv P).continuous

example : Continuous (rationalCompletionPadicEquiv P).symm :=
  (rationalCompletionPadicEquiv P).symm.continuous

end Probe8
