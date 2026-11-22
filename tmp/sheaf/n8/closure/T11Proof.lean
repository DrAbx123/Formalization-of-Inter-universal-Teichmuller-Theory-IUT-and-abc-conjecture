import tmp.sheaf.n8.closure.T11Native

/-!
# T11 proof attempt: packet identification and C4 value-to-IQ donor

This file attempts the two named residuals:

1. ThetaPacketIdentification C3:
   forall n j, thetaScale C3 n j = C3.thetaPacket.scale j.
2. C4ValueMonoidToIQMissing C4 C3 D.

For (1), no production declaration links the source value I.thetaValueAt (n.1)
0 j to the C3 field C3.thetaPacket.scale j.  The source theta value is read from
I.theaterAt (n.1) 0; C3.thetaPacket is an independent field of the C3 structure.
This file proves the conditional consequences of the explicit proposition; it
does not fabricate a proof or a Real -> CommonPrimeCompletion inverse.

For (2), the missing donor is the full map ValueMonoidAt -> IQCarrier with its
compatibility law; no arbitrary function is introduced.

No free interface, no True, no arbitrary Type.
-/

noncomputable section

namespace ABCBridge.N8.T11Proof

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.SourceThetaToIQ
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C4Actual
open ABCBridge.N8.T11Actual
open ABCBridge.N8.T11Native

universe ua uv upi umon ui uL

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {Label : Type uL} [Group Label]

/-- The explicit packet identification is exactly the source-vs-C3 packet
equality. -/
theorem thetaPacketIdentification_iff_source
    (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    ThetaPacketIdentification (I := I) C3 ↔
      ∀ (n : ThetaPilotCarrier l) (j : SignedLabel l.value),
        I.thetaValueAt (n.1 : Int) 0 j = C3.thetaPacket.scale j := by
  constructor
  · intro h n j
    simpa [thetaScale] using h n j
  · intro h n j
    simpa [thetaScale] using h n j

/-- If the explicit identification holds, C3's packet scale is the actual source
theater packet scale.  This is the conditional source link; it is not proved
unconditionally. -/
theorem thetaPacketIdentification_forces_source_packet
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (h : ThetaPacketIdentification (I := I) C3)
    (n : ThetaPilotCarrier l) (j : SignedLabel l.value) :
    C3.thetaPacket.scale j =
      (I.theaterAt (n.1 : Int) 0).thetaPacket.scale j := by
  calc
    C3.thetaPacket.scale j = thetaScale (I := I) C3 n j := (h n j).symm
    _ = (I.theaterAt (n.1 : Int) 0).thetaPacket.scale j :=
      thetaScale_eq_theaterScale (I := I) C3 n j

/-- Conditional log form of the identification. -/
theorem thetaScale_log_eq_packet_of_identification
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (h : ThetaPacketIdentification (I := I) C3)
    (n : ThetaPilotCarrier l) (j : SignedLabel l.value) :
    Real.log (thetaScale (I := I) C3 n j) =
      (gaussExponent j.1).toNat * Real.log C3.thetaPacket.q :=
  T11Actual.thetaScale_log_eq_gauss_of_packet (I := I) C3 h n j

/-- Exact C4 value-monoid-to-IQ missing donor. -/
def C4ValueMonoidToIQMissing
    (C4 : SourceWitnessedOutputData (l := l) (V := V) I Label)
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (D : SourceThetaIQInterface (I := I) C3) : Prop :=
  T11Actual.ValueMonoidToIQObligation (I := I) C4 C3 D

/-- C4 missing donor is definitionally the explicit ValueMonoidToIQObligation. -/
theorem c4ValueMonoidToIQMissing_iff
    (C4 : SourceWitnessedOutputData (l := l) (V := V) I Label)
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (D : SourceThetaIQInterface (I := I) C3) :
    C4ValueMonoidToIQMissing (I := I) C4 C3 D ↔
      T11Actual.ValueMonoidToIQObligation (I := I) C4 C3 D :=
  Iff.rfl

/-- The native theta value's completion and real readout are both actual data;
there is no Real -> completion inverse in these declarations. -/
theorem nativeThetaValue_components
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (n : ThetaPilotCarrier l) (j : SignedLabel l.value) :
    (nativeThetaValue (I := I) C3 n j).completion =
        thetaCompletionActual (I := I) C3 n j ∧
      (nativeThetaValue (I := I) C3 n j).realReadout =
        C3.thetaPacket.scale j :=
  ⟨rfl, rfl⟩

end ABCBridge.N8.T11Proof