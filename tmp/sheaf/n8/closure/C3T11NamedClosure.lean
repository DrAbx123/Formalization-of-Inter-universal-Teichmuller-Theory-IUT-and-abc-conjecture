import tmp.sheaf.n8.closure.C3KummerActual
import tmp.sheaf.n8.closure.P6Tensor
import tmp.sheaf.n8.closure.T11Reductions
import tmp.sheaf.n8.closure.T11Native
import Mathlib

/-!
# C3 complete source object and T11 q-packet identification closure

This file assembles the C3 source object from the native actual q/roots/Kummer
slice, the P6 tensor output interface, and the T11 packet identification.

The T11 identification is not reproved: it is obtained from the existing
T11Reductions.thetaPacketIdentification_iff_q and the existing q obligation.

The full C3 complete source object still depends on the actual C3 source
donors; its nonemptiness is recorded as the single theorem-level named sorry.
-/

noncomputable section

namespace ABCBridge.N8.C3T11NamedClosure

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C3KummerActual
open LeanFormal.IUT.N8Closure.P6Tensor
open ABCBridge.N8.T11Reductions
open ABCBridge.N8.T11Native

universe ua uv upi umon ui u v w

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {X : N8NativeInput l}

/-- T11 q-packet identification from the actual theta-packet witness; the
iff lemma is reused, not reproved. -/
theorem c3T11_thetaPacketIdentification
    (W : ThetaPacketWitness (I := I)) :
    ThetaPacketIdentification (I := I) W.C3 :=
  (thetaPacketIdentification_iff_q (I := I) W.C3).mpr
    (qIdentification_obligation (I := I) W)

/-- Complete C3 source object: the actual C3 theta-packet witness, the native
actual q/roots/Kummer slice, and the P6 tensor output. -/
structure C3CompleteSourceObject
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (X : N8NativeInput l) where
  c3 : SourcePilotRegionData.{ua, uv, upi, umon, ui, 0, 0} (l := l) (V := V) I
  q : NativeQDonor X
  landing : P6TensorLandingData.{0, 0} X
  action : NativeKummerAction.{0} X q
  p6 : P6C3TensorOutput.{0, 0} X q landing
  thetaPacket : ThetaPacketIdentification.{ua, uv, upi, umon, ui, 0, 0} (I := I) c3
  thetaWitness : ThetaPacketWitness (I := I)

/-- Actual assembly from an actual theta-packet witness and native donors. -/
noncomputable def c3CompleteSourceObjectOfDonors
    (W : ThetaPacketWitness (I := I))
    (D : NativeQDonor X) (L : P6TensorLandingData X)
    (A : NativeKummerAction X D) :
    C3CompleteSourceObject I X where
  c3 := W.C3
  q := D
  landing := L
  action := A
  p6 := p6C3TensorOutputOfDonors X D L
  thetaPacket := c3T11_thetaPacketIdentification (I := I) W
  thetaWitness := W

end ABCBridge.N8.C3T11NamedClosure
