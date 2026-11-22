import tmp.sheaf.n8.closure.C7UToIQProof
import tmp.sheaf.n8.closure.C7Native
import tmp.sheaf.n8.closure.SourceThetaToIQ
import Mathlib

/-!
# C7 actual source U-to-IQ attempt

The actual C4 evaluation lands in I.ThetaPilotPoint, while T11 thetaImage lands
through C3.tensorLanding from CommonPrimeCompletion.  There is no production map
from ThetaPilotPoint to CommonPrimeCompletion in the tree.  This file records the
exact missing eval-to-completion donor and proves that it, together with the
canonical-hull containment, constructs the actual SourceUToIQMap.  No constant
or weak map is used.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C7U2IQSourceAttempt

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory
open ABCBridge.N8.C4Actual
open ABCBridge.N8.C7Actual
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.N8Closure.SourceLogKummerRealization
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.SourceAlgorithmCompatibility
open LeanFormal.IUT.N8Closure.SourceThetaToIQ
open LeanFormal.IUT.N8Closure.C7Native
open LeanFormal.IUT.N8Closure.C7SourceU
open LeanFormal.IUT.N8Closure.C7UToIQProof

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

/-- Exact missing map: the actual C4 value-point carrier to the completion
used by C3.tensorLanding, with the T11 theta-image compatibility. -/
structure EvalToCompletionDonor where
  evalToCompletion : I.ThetaPilotPoint D.place.v →
    CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) C3.place
  eval_theta_compat : ∀ c : SignedLabel l.value,
    C3.tensorLanding (evalToCompletion (D.eval n x c)) = T.thetaImage n c

/-- Additional exact condition: the induced map carries the actual source U
into the canonical IQ hull. -/
def EvalToCompletionHullCondition
    (M : EvalToCompletionDonor (C3 := C3) (D := D) (T := T) (n := n) (x := x)) : Prop :=
  ∀ y ∈ sourceU (D := D) n x,
    C3.tensorLanding (M.evalToCompletion y) ∈
      arithmeticTupleCanonicalHull C3.tensorPlaces C3.tensorTuple

/-- The eval-to-completion donor plus the canonical-hull condition constructs
the actual SourceUToIQMap explicitly through C3.tensorLanding.  This is not a
constant map: it is the composite evalToCompletion then tensorLanding. -/
def actualSourceUToIQMap_of_completionDonor
    (M : EvalToCompletionDonor (C3 := C3) (D := D) (T := T) (n := n) (x := x))
    (hM : EvalToCompletionHullCondition (C3 := C3) (D := D) (T := T) (n := n) (x := x) M) :
    ActualSourceUToIQMap (C3 := C3) (D := D) (T := T) (n := n) (x := x) where
  toIQ y := C3.tensorLanding (M.evalToCompletion y)
  eval_compat c := M.eval_theta_compat c
  u_image_mem_canonicalHull := hM

/-- Conditional closure: the exact eval-to-completion donor and hull condition
give a nonempty actual SourceUToIQMap. -/
theorem actualSourceUToIQMap_nonempty_of_completionDonor
    (M : EvalToCompletionDonor (C3 := C3) (D := D) (T := T) (n := n) (x := x))
    (hM : EvalToCompletionHullCondition (C3 := C3) (D := D) (T := T) (n := n) (x := x) M) :
    Nonempty (ActualSourceUToIQMap (C3 := C3) (D := D) (T := T) (n := n) (x := x)) :=
  ⟨actualSourceUToIQMap_of_completionDonor (C3 := C3) (D := D) (T := T)
    (n := n) (x := x) M hM⟩

end LeanFormal.IUT.N8Closure.C7U2IQSourceAttempt
