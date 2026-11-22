import tmp.sheaf.n8.closure.C7DonorProof
import tmp.sheaf.n8.closure.C7EvalCompletionHullAttempt
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceHolomorphicIntegralClosure
import Mathlib

/-!
# C7 theta-image containment attempt

T11 gives T.thetaImage n j = C3.tensorLanding (T.thetaCompletion n j).  The
thetaCompletion map is an arbitrary interface field; no production theorem puts
its tensorLanding image in the canonical hull.  This file reduces containment to
the exact tensorLanding condition and records the preferred unit-region donor
(thetaCompletion lands in the canonical unit reference, plus unit-reference
containment in the canonical hull).  It does not use a constant map.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C7ThetaContainmentAttempt

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory
open ABCBridge.N8.C4Actual
open ABCBridge.N8.C7Actual
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.SourceThetaToIQ
open LeanFormal.IUT.N8Closure.C7Native
open LeanFormal.IUT.N8Closure.C7DonorProof

universe ua uv upi umon ui uL uG

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {LAdd : Type uG} [AddGroup LAdd]
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (D : SourceWitnessedOutputData (l := l) (V := V) I (Multiplicative LAdd))
variable [MeasurableSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
variable (mu : Measure (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple))
variable [Measure.IsAddHaarMeasure mu]
variable (T : SourceThetaIQInterface (I := I) C3)
variable (n : ThetaPilotCarrier l)
variable (x : I.ThetaPilotPoint D.place.v)

/-- Exact tensorLanding reduction of theta containment. -/
theorem thetaImageContainment_iff_tensorLanding :
    ThetaImageContainmentDonor (C3 := C3) T n ↔
      ∀ j : SignedLabel l.value,
        C3.tensorLanding (T.thetaCompletion n j) ∈
          arithmeticTupleCanonicalHull C3.tensorPlaces C3.tensorTuple := by
  constructor
  · intro h j
    rw [← T.thetaImage_eq n j]
    exact h j
  · intro h j
    rw [T.thetaImage_eq n j]
    exact h j

/-- Preferred exact donor: thetaCompletion lands in the actual canonical unit
reference, and that unit reference is contained in the canonical hull. -/
def ThetaUnitHullDonor : Prop :=
  (∀ j : SignedLabel l.value,
      C3.tensorLanding (T.thetaCompletion n j) ∈
        arithmeticTupleCanonicalUnitReference C3.tensorPlaces C3.tensorTuple) ∧
    (arithmeticTupleCanonicalUnitReference C3.tensorPlaces C3.tensorTuple :
        Set (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)) ⊆
      arithmeticTupleCanonicalHull C3.tensorPlaces C3.tensorTuple

end LeanFormal.IUT.N8Closure.C7ThetaContainmentAttempt
