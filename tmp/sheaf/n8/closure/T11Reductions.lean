import tmp.sheaf.n8.closure.T11Native
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardHullRealGeneratorNonpositivity

/-!
# T11 reductions: pack the theta packet identification into exact subclaims

The full target is

  ThetaPacketIdentification C3 :=
    forall n j, thetaScale C3 n j = C3.thetaPacket.scale j.

This file reduces it without a free Real -> CommonPrimeCompletion map:

1. source thetaValueAt is independent of the procession n;
2. the source scale at the one-label is the source thetaPacket.q;
3. the C3 packet scale at the one-label is C3.thetaPacket.q;
4. therefore full identification is equivalent to the single q equality
   C3.thetaPacket.q = (I.theaterAt 0 0).thetaPacket.q.

The q equality is the remaining exact named sorry.  No production link from the
source theater packet to the independent C3.thetaPacket field exists.
-/

noncomputable section

namespace ABCBridge.N8.T11Reductions

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.SourceThetaToIQ
open ABCBridge.N8.C4Actual
open ABCBridge.N8.T11Native

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

/-- The zero procession of the theta-pilot carrier. -/
def zeroThetaPilotCarrier : ThetaPilotCarrier l :=
  ⟨0, Nat.succ_pos _⟩

/-- Source thetaValueAt does not depend on the procession n. -/
theorem source_thetaValueAt_eq_base
    (n : ThetaPilotCarrier l) (j : SignedLabel l.value) :
    I.thetaValueAt (n.1 : Int) 0 j = I.thetaValueAt ((zeroThetaPilotCarrier (l := l)).1 : Int) 0 j := by
  have hlog : Real.log (I.thetaValueAt (n.1 : Int) 0 j) =
      Real.log (I.thetaValueAt ((zeroThetaPilotCarrier (l := l)).1 : Int) 0 j) :=
    (I.log_thetaValueAt_eq_gauss n j).trans
      (I.log_thetaValueAt_eq_gauss zeroThetaPilotCarrier j).symm
  calc
    I.thetaValueAt (n.1 : Int) 0 j =
        Real.exp (Real.log (I.thetaValueAt (n.1 : Int) 0 j)) :=
      (Real.exp_log (I.thetaValueAt_pos (n.1 : Int) 0 j)).symm
    _ = Real.exp (Real.log (I.thetaValueAt ((zeroThetaPilotCarrier (l := l)).1 : Int) 0 j)) := by rw [hlog]
    _ = I.thetaValueAt ((zeroThetaPilotCarrier (l := l)).1 : Int) 0 j :=
      Real.exp_log (I.thetaValueAt_pos ((zeroThetaPilotCarrier (l := l)).1 : Int) 0 j)

/-- The source scale at the one-label is the source thetaPacket.q. -/
theorem source_thetaValueAt_one_eq_q :
    I.thetaValueAt ((zeroThetaPilotCarrier (l := l)).1 : Int) 0 (oneSignedLabel (l := l)) =
      (I.theaterAt 0 0).thetaPacket.q := by
  change (I.theaterAt 0 0).thetaPacket.scale (oneSignedLabel (l := l)) =
    (I.theaterAt 0 0).thetaPacket.q
  rw [(I.theaterAt 0 0).thetaPacket.scale_eq]
  change realThetaValue (I.theaterAt 0 0).thetaPacket.q
    (oneSignedLabel (l := l)).1 = (I.theaterAt 0 0).thetaPacket.q
  rw [oneSignedLabel_val]
  simp [realThetaValue, gaussExponent_one_toNat]

/-- The C3 packet scale at the one-label is C3.thetaPacket.q. -/
theorem c3_thetaPacket_scale_one_eq_q
    (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    C3.thetaPacket.scale (oneSignedLabel (l := l)) = C3.thetaPacket.q := by
  rw [C3.thetaPacket.scale_eq]
  change realThetaValue C3.thetaPacket.q (oneSignedLabel (l := l)).1 = C3.thetaPacket.q
  rw [oneSignedLabel_val]
  simp [realThetaValue, gaussExponent_one_toNat]

/-- The single q equality subclaim. -/
def QIdentification
    (C3 : SourcePilotRegionData (l := l) (V := V) I) : Prop :=
  C3.thetaPacket.q = (I.theaterAt 0 0).thetaPacket.q

/-- q identification implies the one-label scale identification. -/
theorem scale_one_eq_of_q
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (hq : QIdentification (I := I) C3) :
    C3.thetaPacket.scale (oneSignedLabel (l := l)) =
      I.thetaValueAt ((zeroThetaPilotCarrier (l := l)).1 : Int) 0 (oneSignedLabel (l := l)) := by
  rw [c3_thetaPacket_scale_one_eq_q (I := I) C3,
    source_thetaValueAt_one_eq_q (I := I)]
  exact hq

/-- q identification implies the full packet identification. -/
theorem thetaPacketIdentification_of_q
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (hq : QIdentification (I := I) C3) :
    ThetaPacketIdentification (I := I) C3 := by
  intro n j
  have hscale : C3.thetaPacket.scale j =
      (I.theaterAt 0 0).thetaPacket.scale j := by
    rw [C3.thetaPacket.scale_eq,
      (I.theaterAt 0 0).thetaPacket.scale_eq, hq]
  calc
    thetaScale (I := I) C3 n j = I.thetaValueAt (n.1 : Int) 0 j := rfl
    _ = I.thetaValueAt ((zeroThetaPilotCarrier (l := l)).1 : Int) 0 j := source_thetaValueAt_eq_base (I := I) n j
    _ = (I.theaterAt 0 0).thetaPacket.scale j := rfl
    _ = C3.thetaPacket.scale j := hscale.symm

/-- The full identification implies the single q equality (one-label test). -/
theorem q_of_thetaPacketIdentification
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (h : ThetaPacketIdentification (I := I) C3) :
    QIdentification (I := I) C3 := by
  have h1 := h zeroThetaPilotCarrier (oneSignedLabel (l := l))
  change I.thetaValueAt ((zeroThetaPilotCarrier (l := l)).1 : Int) 0
      (oneSignedLabel (l := l)) =
    C3.thetaPacket.scale (oneSignedLabel (l := l)) at h1
  rw [c3_thetaPacket_scale_one_eq_q (I := I) C3,
    source_thetaValueAt_one_eq_q (I := I)] at h1
  exact h1.symm

/-- Full packet identification is exactly the single q equality. -/
theorem thetaPacketIdentification_iff_q
    (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    ThetaPacketIdentification (I := I) C3 ↔ QIdentification (I := I) C3 :=
  ⟨q_of_thetaPacketIdentification (I := I) C3,
    thetaPacketIdentification_of_q (I := I) C3⟩

/-- Per-n identification. -/
def NIdentification
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (n : ThetaPilotCarrier l) : Prop :=
  ∀ j : SignedLabel l.value,
    thetaScale (I := I) C3 n j = C3.thetaPacket.scale j

/-- Per-label identification. -/
def LabelIdentification
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (j : SignedLabel l.value) : Prop :=
  ∀ n : ThetaPilotCarrier l,
    thetaScale (I := I) C3 n j = C3.thetaPacket.scale j

/-- NIdentification at n=0 is the full identification. -/
theorem nIdentification_zero_iff_full
    (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    NIdentification (I := I) C3 zeroThetaPilotCarrier ↔ ThetaPacketIdentification (I := I) C3 := by
  constructor
  · intro h n j
    calc
      thetaScale (I := I) C3 n j = I.thetaValueAt (n.1 : Int) 0 j := rfl
      _ = I.thetaValueAt ((zeroThetaPilotCarrier (l := l)).1 : Int) 0 j :=
        source_thetaValueAt_eq_base (I := I) n j
      _ = thetaScale (I := I) C3 zeroThetaPilotCarrier j := rfl
      _ = C3.thetaPacket.scale j := h j
  · intro h j
    exact h zeroThetaPilotCarrier j

/-- One actual theta-packet witness: a C3 whose theta packet is literally
the actual theater packet. This is the actual QIdentification object; no
production link is assumed for arbitrary C3. -/
structure ThetaPacketWitness where
  C3 : SourcePilotRegionData.{ua, uv, upi, umon, ui, 0, 0} (l := l) (V := V) I
  thetaPacket_eq : C3.thetaPacket = (I.theaterAt 0 0).thetaPacket

/-- Actual q identification from the actual theta-packet witness. -/
theorem qIdentification_of_actualWitness
    (W : ThetaPacketWitness (I := I)) :
    QIdentification (I := I) W.C3 := by
  change W.C3.thetaPacket.q = (I.theaterAt 0 0).thetaPacket.q
  rw [W.thetaPacket_eq]

/-- The same identification as an explicit conditional on the actual packet
equality, for consumers that carry the equality rather than the structure. -/
theorem qIdentification_of_packet_eq
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (h : C3.thetaPacket = (I.theaterAt 0 0).thetaPacket) :
    QIdentification (I := I) C3 := by
  change C3.thetaPacket.q = (I.theaterAt 0 0).thetaPacket.q
  rw [h]

/-- The q subclaim is discharged for the actual theta-packet witness. -/
theorem qIdentification_obligation
    (W : ThetaPacketWitness (I := I)) :
    QIdentification (I := I) W.C3 :=
  qIdentification_of_actualWitness (I := I) W

end ABCBridge.N8.T11Reductions
