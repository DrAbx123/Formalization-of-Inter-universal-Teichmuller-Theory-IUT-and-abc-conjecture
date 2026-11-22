import LeanFormal.IUT.IUTIII.Theorem311.SourceFaithfulBoundary

/-! # A1/A2/A3 at the source-faithful Input boundary

This file proves the three source assumption packages from the actual
`Theorem311Source.Input` boundary already formalized in the project:

- A1: Theorem 3.11 output (`Theorem311Output I`).
- A2: Proposition 3.9 packet/log-volume laws.
- A3: Remark 3.9.5 vertical/hull/Ind laws (`PartII`, `PartIII`).

It does not construct `Input` from `OriginalInput`; that is the remaining
source-boundary obligation. No sorry, no custom axiom.
-/

namespace LeanFormal.IUT.N8Closure.C9A1A2A3Source

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source

noncomputable section

universe u v

variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
  (I : Theorem311Source.Input Label Choice)

/-- A1: the full Theorem 3.11 output over the actual Input boundary. -/
def A1 : Theorem311Source.Theorem311Output I :=
  Theorem311Source.theorem311Output I

theorem A1_part_i : (A1 I).part_i = Theorem311Source.partI I := by
  rfl

theorem A1_part_ii : (A1 I).part_ii = Theorem311Source.partII I := by
  rfl

theorem A1_part_iii : (A1 I).part_iii = Theorem311Source.partIII I := by
  rfl

/-- A2: Proposition 3.9 packet/log-volume laws. -/
structure A2 where
  log_determinant : ∀ c : Choice,
    Real.log (I.localPacket.determinant c) = I.localPacket.logVolume c
  ind1_log : ∀ (g : Label) (c : Choice),
    I.localPacket.logVolume (I.prime.ind1 g c) = I.localPacket.logVolume c
  ind2_log : ∀ (g : Label) (c : Choice),
    I.localPacket.logVolume (I.prime.ind2 g c) = I.localPacket.logVolume c
  ind3_log_upper : ∀ (n : Nat) (c : Choice),
    I.localPacket.logVolume c ≤ I.localPacket.logVolume (I.prime.ind3 n c)

def A2.ofInput : A2 I where
  log_determinant c := Theorem311Source.packet_log_determinant I c
  ind1_log g c := Theorem311Source.packet_ind1_log_volume I g c
  ind2_log g c := Theorem311Source.packet_ind2_log_volume I g c
  ind3_log_upper n c := Theorem311Source.packet_ind3_log_volume_upper I n c

/-- A3: Remark 3.9.5 vertical/hull/Ind laws. -/
structure A3 where
  vertical : Theorem311Source.PartII I
  horizontal : Theorem311Source.PartIII I
  hull_dominated : ∀ {c : Choice} {hull : Real},
    (Theorem311Source.verticalCorrespondence I).HullDominates c hull →
    I.profile.logVolume c ≤ hull

def A3.ofInput : A3 I where
  vertical := Theorem311Source.partII I
  horizontal := Theorem311Source.partIII I
  hull_dominated := by
    intro c hull h
    exact Theorem311Source.vertical_hull_dominates_base I h

theorem A1_A2_A3 :
    (A1 I).part_i = Theorem311Source.partI I ∧
    Nonempty (A2 I) ∧ Nonempty (A3 I) :=
  ⟨A1_part_i I, ⟨⟨A2.ofInput I⟩, ⟨A3.ofInput I⟩⟩⟩

#print axioms A1_A2_A3

end

end LeanFormal.IUT.N8Closure.C9A1A2A3Source