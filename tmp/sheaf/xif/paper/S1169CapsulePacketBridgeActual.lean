import tmp.sheaf.xif.paper.S1156CapsuleTensorAuditActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000

namespace LeanFormal.IUT.XiFPaper.S1169CapsulePacketBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source.SourceHodgeTheaterBridge

universe u v w ua uv upi umon ui uI

variable {l : PrimeGeFive}
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (P : SourceLGPProcession l Label Choice)
variable {V : Type uv}
variable (I : LeanFormal.IUT.Theorem311Source.OriginalInput.{ua, uv, upi, umon, ui} l V)
variable {ι : Type uI}
variable (D : ι → LeanFormal.IUT.SourceLogShellDatum)

/-- Exact actual bridge from the H2/capsule production to a source packet.

The first missing fields are the choice-indexed H2 procession and the
choice-indexed actual tensor packet.  No degenerate PUnit packet is used.
-/
structure SourceCapsulePacketActualBridge where
  /-- First gap: choice-indexed H2 finite capsules. -/
  capsuleIndex : Choice → LeanFormal.IUT.Theorem311Source.OriginalInput.H2FProcession I
  /-- First gap: choice-indexed points of the actual tensor log-shell packet. -/
  tensorPoint : Choice → LeanFormal.IUT.SourceLogShellActualIQTensor D

  /-- Actual tensor log functional (paper log-volume source). -/
  tensorLog : LeanFormal.IUT.SourceLogShellActualIQTensor D → Real

  logVolume : Choice → Real
  logVolume_eq : ∀ c, logVolume c = tensorLog (tensorPoint c)

  determinant : Choice → Real
  determinant_eq : ∀ c, determinant c = Real.exp (logVolume c)

  possibleImage : Choice → Set Real
  possibleImage_nonempty : ∀ c, (possibleImage c).Nonempty

  ind1_volume : ∀ g c, logVolume (P.ind1 g c) = logVolume c
  ind2_volume : ∀ g c, logVolume (P.ind2 g c) = logVolume c
  ind3_volume : ∀ n c, logVolume c ≤ logVolume (P.ind3 n c)

  ind1_determinant : ∀ g c, determinant (P.ind1 g c) = determinant c
  ind2_determinant : ∀ g c, determinant (P.ind2 g c) = determinant c
  ind3_determinant : ∀ n c, determinant c ≤ determinant (P.ind3 n c)

  image_ind1 : ∀ g c, possibleImage (P.ind1 g c) = possibleImage c
  image_ind2 : ∀ g c, possibleImage (P.ind2 g c) = possibleImage c
  image_ind3 : ∀ n c z, z ∈ possibleImage c →
    ∃ y, y ∈ possibleImage (P.ind3 n c) ∧ z ≤ y

  /-- Exact remaining compatibility with H2 stage inclusions. -/
  h2_compatible : Prop
  /-- Exact remaining PrimeStrip log-shell bridge (PrimeStripLogShellActual absent). -/
  primeStripLogShell_bridge : Prop

/-- Any actual bridge yields a genuine SourcePacketRealization, with carrier
the actual tensor log-shell packet. -/
noncomputable def sourcePacketRealization_of_bridge
    (B : SourceCapsulePacketActualBridge (l := l) (Label := Label)
      (Choice := Choice) (P := P) (I := I) (D := D)) :
    SourcePacketRealization P where
  carrier := fun _ => LeanFormal.IUT.SourceLogShellActualIQTensor D
  distinguished := B.tensorPoint
  logVolume := B.logVolume
  determinant := B.determinant
  determinant_positive := fun c => by
    rw [B.determinant_eq c]
    exact Real.exp_pos _
  log_determinant := fun c => by
    rw [B.determinant_eq c, Real.log_exp]
  possibleImage := B.possibleImage
  possibleImage_nonempty := B.possibleImage_nonempty
  ind1_volume := B.ind1_volume
  ind2_volume := B.ind2_volume
  ind3_volume := B.ind3_volume
  ind1_determinant := B.ind1_determinant
  ind2_determinant := B.ind2_determinant
  ind3_determinant := B.ind3_determinant
  image_ind1 := B.image_ind1
  image_ind2 := B.image_ind2
  image_ind3 := B.image_ind3

/-- Exact first-gap proposition. -/
def SourceCapsulePacketActualBridgeRequired : Prop :=
  Nonempty (SourceCapsulePacketActualBridge (l := l) (Label := Label)
    (Choice := Choice) (P := P) (I := I) (D := D))

/-- First-gap projection: a bridge supplies the choice→H2 and choice→tensor
index maps; the current tree constructs neither. -/
theorem sourceCapsulePacket_firstGap
    (B : SourceCapsulePacketActualBridge (l := l) (Label := Label)
      (Choice := Choice) (P := P) (I := I) (D := D)) :
    (∀ c : Choice,
      Nonempty (LeanFormal.IUT.Theorem311Source.OriginalInput.H2FProcession I)) ∧
      (∀ c : Choice, Nonempty (LeanFormal.IUT.SourceLogShellActualIQTensor D)) :=
  ⟨fun c => ⟨B.capsuleIndex c⟩, fun c => ⟨B.tensorPoint c⟩⟩

end LeanFormal.IUT.XiFPaper.S1169CapsulePacketBridgeActual

end
