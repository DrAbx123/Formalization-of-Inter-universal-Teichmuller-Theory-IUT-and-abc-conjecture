import tmp.sheaf.n8.closure.T11Actual

/-!
# T11 native: construct the actual theta value first, then its real readout

The native theta value is a pair

  (completion, realReadout)

where the completion is built first from C3.qUnit and the label's Gaussian
exponent, and the real readout is C3.thetaPacket.scale j.  No inverse dictionary
Real -> CommonPrimeCompletion is introduced: the completion is constructed
directly, and the readout is a separate field.

The source theta scale equals the native real readout only under the explicit
proposition

  ThetaPacketIdentification C3 :=
    forall n j, thetaScale C3 n j = C3.thetaPacket.scale j.

That proposition is the exact missing source link.  C4 ValueMonoid -> IQ also
remains an explicit missing donor (C4ValueMonoidToIQMissing).
-/

noncomputable section

namespace ABCBridge.N8.T11Native

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.SourceThetaToIQ
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C4Actual
open ABCBridge.N8.T11Actual

universe ua uv upi umon ui uL

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {Label : Type uL} [Group Label]

/-- Native actual theta value: completion first, then real readout. -/
structure NativeThetaValue
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (n : ThetaPilotCarrier l) (j : SignedLabel l.value) where
  /-- The actual completion element, constructed from C3.qUnit. -/
  completion : CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) C3.place
  /-- It is the actual qUnit Gaussian power. -/
  completion_eq : completion =
    thetaCompletionActual (I := I) C3 n j
  /-- The real readout of the native theta value, from C3's theta packet. -/
  realReadout : Real
  /-- The readout is the C3 finite theta packet scale. -/
  realReadout_eq : realReadout = C3.thetaPacket.scale j

/-- Construct the native theta value; completion is built before readout. -/
def nativeThetaValue
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (n : ThetaPilotCarrier l) (j : SignedLabel l.value) :
    NativeThetaValue (I := I) C3 n j where
  completion := thetaCompletionActual (I := I) C3 n j
  completion_eq := rfl
  realReadout := C3.thetaPacket.scale j
  realReadout_eq := rfl

/-- The native completion is the actual qUnit Gaussian power. -/
theorem nativeThetaValue_completion
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (n : ThetaPilotCarrier l) (j : SignedLabel l.value) :
    (nativeThetaValue (I := I) C3 n j).completion =
      thetaCompletionActual (I := I) C3 n j :=
  rfl

/-- The native real readout is the C3 theta packet scale. -/
theorem nativeThetaValue_realReadout
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (n : ThetaPilotCarrier l) (j : SignedLabel l.value) :
    (nativeThetaValue (I := I) C3 n j).realReadout =
      C3.thetaPacket.scale j :=
  rfl

/-- The native real readout has the Gaussian q-log. -/
theorem nativeThetaValue_logReadout
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (n : ThetaPilotCarrier l) (j : SignedLabel l.value) :
    Real.log (nativeThetaValue (I := I) C3 n j).realReadout =
      (gaussExponent j.1).toNat * Real.log C3.thetaPacket.q := by
  rw [nativeThetaValue_realReadout]
  exact C3.thetaPacket.log_scale j

/-- Exact source/packet identification proposition. -/
def ThetaPacketIdentification
    (C3 : SourcePilotRegionData (l := l) (V := V) I) : Prop :=
  ThetaScalePacketIdentification (I := I) C3

/-- If the source/packet identification holds, the source theta scale equals the
native real readout.  No Real -> completion inverse is used. -/
theorem thetaScale_eq_nativeReadout_of_packet
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (h : ThetaPacketIdentification (I := I) C3)
    (n : ThetaPilotCarrier l) (j : SignedLabel l.value) :
    thetaScale (I := I) C3 n j =
      (nativeThetaValue (I := I) C3 n j).realReadout :=
  h n j

/-- Exact missing C4 ValueMonoid -> IQ donor, stated as an explicit Prop. -/
def C4ValueMonoidToIQMissing
    (C4 : SourceWitnessedOutputData (l := l) (V := V) I Label)
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (D : SourceThetaIQInterface (I := I) C3) : Prop :=
  ValueMonoidToIQObligation (I := I) C4 C3 D

/-- C4 alignment at log-degree, restated from T11Actual. -/
theorem c4_logDegree_eq_log_thetaScale
    (C4 : SourceWitnessedOutputData (l := l) (V := V) I Label)
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (hdeg : DegreeFaithful (I := I) C4)
    (n : ThetaPilotCarrier l) (j : SignedLabel l.value) :
    I.logDegreeAt 0 0 C4.place.v (I.thetaImageValue C4.place.R n j) =
      Real.log (thetaScale (I := I) C3 n j) :=
  T11Actual.c4_logDegree_eq_log_thetaScale (I := I) C4 C3 hdeg n j

end ABCBridge.N8.T11Native
