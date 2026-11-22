import tmp.sheaf.n8.closure.C7CanonicalUnitHullInclusionAttempt
import tmp.sheaf.n8.closure.T11Actual
import Mathlib

/-!
# C7 theta-completion source attempt

The actual T11 interface is constructed from C3.qUnit and the label's Gaussian
exponent (T11Actual.thetaIQInterfaceActual).  Its thetaCompletion is the actual
completion candidate, not an arbitrary interface field.

The unit-reference membership for this actual completion is reduced to the
actual qUnit power condition

  C3.tensorLanding ((C3.qUnit) ^ gaussExponent) in canonicalUnitReference.

Only tensorLanding_q (q lands at C3.tensorUnit) is available; there is no
tensorLanding power law and no tensorUnit membership theorem.  That membership is
the single named gap; no arbitrary completion is introduced.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C7ThetaCompletionSourceAttempt

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
open ABCBridge.N8.T11Actual
open LeanFormal.IUT.N8Closure.C7CanonicalUnitHullInclusionAttempt

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
variable (n : ThetaPilotCarrier l)
variable (x : I.ThetaPilotPoint D.place.v)

/-- The actual T11 interface built from C3.qUnit. -/
abbrev actualThetaInterface : SourceThetaIQInterface (I := I) C3 :=
  thetaIQInterfaceActual (I := I) C3

/-- The actual interface is compatible with thetaScale and thetaImage by rfl. -/
theorem actualThetaInterface_compatible :
    (actualThetaInterface (I := I) C3).thetaScale = thetaScale (I := I) C3 ∧
      (∀ n j, (actualThetaInterface (I := I) C3).thetaImage n j =
        C3.tensorLanding (thetaCompletionActual (I := I) C3 n j)) :=
  ⟨rfl, fun n j => rfl⟩

/-- The actual qUnit completion is the qUnit raised to the label's Gaussian
exponent. -/
theorem thetaCompletionActual_eq_qUnit_pow
    (n : ThetaPilotCarrier l) (j : SignedLabel l.value) :
    thetaCompletionActual (I := I) C3 n j =
      ((C3.qUnit : (CommonPrimeCompletion
        (K := I.initial.arithmetic.Fmod) C3.place)ˣ) :
          CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) C3.place) ^
        (gaussExponent j.1).toNat :=
  rfl

/-- Exact unit-reference condition for the actual qUnit completion. -/
def ThetaCompletionActualUnitReferenceMembership : Prop :=
  ∀ j : SignedLabel l.value,
    C3.tensorLanding (thetaCompletionActual (I := I) C3 n j) ∈
      arithmeticTupleCanonicalUnitReference C3.tensorPlaces C3.tensorTuple

/-- The unit-reference donor for the actual interface is exactly the qUnit-power
condition. -/
theorem thetaCompletionUnitReferenceMembership_actual_iff :
    ThetaCompletionUnitReferenceMembership (C3 := C3) (T := actualThetaInterface (I := I) C3) n ↔
      ThetaCompletionActualUnitReferenceMembership (C3 := C3) n :=
  Iff.rfl

/-- Actual-interface membership from the exact qUnit-power donor. -/
theorem thetaCompletionUnitReferenceMembership_actual
    (h : ThetaCompletionActualUnitReferenceMembership (C3 := C3) n) :
    ThetaCompletionUnitReferenceMembership (C3 := C3)
      (T := actualThetaInterface (I := I) C3) n :=
  (thetaCompletionUnitReferenceMembership_actual_iff (C3 := C3) (n := n)).mpr h

end LeanFormal.IUT.N8Closure.C7ThetaCompletionSourceAttempt
