import tmp.sheaf.n8.closure.C3T11NamedClosure
import tmp.sheaf.n8.closure.NativeC3
import tmp.sheaf.n8.closure.P6Tensor
import tmp.sheaf.n8.closure.C3KummerActual
import Mathlib

/-!
# C3 complete-source reduction to exact sub-obligations

This file decomposes

  Nonempty (C3T11NamedClosure.C3CompleteSourceObject I X)

into a conjunction of exact sub-obligations:

- C3 actual source data;
- native q donor;
- native tensor landing donor;
- native Kummer action donor;
- T11 theta-packet identification.

The T11 q-packet identification is not reproved: it is discharged by
C3T11NamedClosure.c3T11_thetaPacketIdentification, which reuses
T11Reductions.thetaPacketIdentification_iff_q.

The native q donor is actual (NativeC3.nativeQDonorActual).  The C3 source,
tensor landing and Kummer action obligations keep their named gaps.
-/

noncomputable section

namespace ABCBridge.N8.C3CompleteSourceReduction

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.P6Tensor
open LeanFormal.IUT.N8Closure.C3KummerActual
open ABCBridge.N8.C3T11NamedClosure
open ABCBridge.N8.T11Native

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {X : N8NativeInput l}

/-- C3 actual source data obligation. -/
def C3SourceObligation : Prop :=
  Nonempty (SourcePilotRegionData.{ua, uv, upi, umon, ui, 0, 0} (l := l) (V := V) I)

/-- Native actual q donor obligation; discharged by nativeQDonorActual. -/
def NativeQDonorObligation : Prop :=
  Nonempty (NativeQDonor X)

/-- Native tensor landing donor obligation. -/
def NativeTensorLandingObligation : Prop :=
  Nonempty (P6TensorLandingData.{0, 0} X)

/-- Native Kummer action donor obligation (actual q plus Galois action). -/
def NativeKummerActionObligation : Prop :=
  Nonempty (Sigma (fun q : NativeQDonor X => NativeKummerAction.{0} X q))

/-- T11 theta-packet identification obligation. -/
def C3ThetaPacketObligation : Prop :=
  ∀ c3 : SourcePilotRegionData.{ua, uv, upi, umon, ui, 0, 0} (l := l) (V := V) I,
    ThetaPacketIdentification.{ua, uv, upi, umon, ui, 0, 0} (I := I) c3

/-- The exact conjunction of C3 sub-obligations. -/
structure C3SubObligations where
  source : C3SourceObligation (I := I)
  qDonor : NativeQDonorObligation (X := X)
  tensorLanding : NativeTensorLandingObligation (X := X)
  kummerAction : NativeKummerActionObligation (X := X)
  thetaPacket : C3ThetaPacketObligation (I := I)

/-- Actual q donor sub-obligation. -/
theorem nativeQDonorObligation_holds :
    NativeQDonorObligation (X := X) :=
  ⟨nativeQDonorActual X⟩

/-- T11 theta-packet sub-obligation is actual by the existing reduction; no
reproof of thetaPacketIdentification_iff_q is made here. -/
theorem c3ThetaPacketObligation_holds :
    C3ThetaPacketObligation (I := I) :=
  fun c3 => c3T11_thetaPacketIdentification (I := I) c3

/-- Named C3 source sub-obligation. -/
theorem c3SourceObligation_holds :
    C3SourceObligation (I := I) := by
  sorry

/-- Named tensor landing sub-obligation. -/
theorem nativeTensorLandingObligation_holds :
    NativeTensorLandingObligation (X := X) := by
  sorry

/-- Named Kummer action sub-obligation. -/
theorem nativeKummerActionObligation_holds :
    NativeKummerActionObligation (X := X) := by
  sorry

/-- Actual assembly of the C3 sub-obligation package from its named/actual
components. -/
noncomputable def c3SubObligations :
    C3SubObligations (I := I) (X := X) where
  source := c3SourceObligation_holds (I := I)
  qDonor := nativeQDonorObligation_holds (X := X)
  tensorLanding := nativeTensorLandingObligation_holds (X := X)
  kummerAction := nativeKummerActionObligation_holds (X := X)
  thetaPacket := c3ThetaPacketObligation_holds (I := I)

/-- Exact reduction: the complete C3 source object exists iff the four source
sub-obligations plus the T11 packet obligation hold. -/
theorem c3CompleteSourceObject_nonempty_iff_subobligations :
    Nonempty (C3CompleteSourceObject I X) ↔
      Nonempty (C3SubObligations (I := I) (X := X)) := by
  constructor
  · rintro ⟨obj⟩
    refine ⟨{
      source := ⟨obj.c3⟩
      qDonor := ⟨obj.q⟩
      tensorLanding := ⟨obj.landing⟩
      kummerAction := ⟨⟨obj.q, obj.action⟩⟩
      thetaPacket := fun c3 => c3T11_thetaPacketIdentification (I := I) c3 }⟩
  · rintro ⟨S⟩
    rcases S.source with ⟨c3⟩
    rcases S.kummerAction with ⟨⟨q, action⟩⟩
    exact ⟨{
      c3 := c3
      q := q
      landing := S.tensorLanding.some
      action := action
      p6 := p6C3TensorOutputOfDonors X q S.tensorLanding.some
      thetaPacket := S.thetaPacket c3 }⟩

/-- Closed reduction result: the named-sorry closure of C3T11 is exactly the
conjunction of the sub-obligations above. -/
theorem c3CompleteSourceObject_nonempty_of_subobligations :
    Nonempty (C3CompleteSourceObject I X) :=
  (c3CompleteSourceObject_nonempty_iff_subobligations (I := I) (X := X)).mpr
    ⟨c3SubObligations (I := I) (X := X)⟩

end ABCBridge.N8.C3CompleteSourceReduction
