/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.IUTII.Kummer.SourceThetaPilotIQContainment

/-! # Theta-pilot orbit: consumers of the orbit-containment lemma -/

namespace LeanFormal.IUT

open Theorem311Source.SourceProcessionCapsule
open Theorem311Source.SourceLGPMonoidLayer

noncomputable section

universe uM

theorem possibleImage_subset_inf {l : PrimeGeFive} {G : LGPMonoid.{uM} l}
    {R : Type*} [CommSemiring R]
    {VQ : Type*} {Place : VQ → Type*} {j : Nat}
    {L : LogShellFamily R Place j}
    {P : LGPMonoidAction G R L} {vQ : VQ}
    (T : ThetaPilotObject P vQ) (Q1 Q2 : Submodule R (TensorPacket L vQ))
    (hgen1 : T.generator ∈ Q1)
    (hstable1 : ∀ (g : G.Carrier), g ∈ G.splittingMonoid →
      ∀ x : TensorPacket L vQ, x ∈ Q1 →
        (LGPMonoidAction.actionOnTensorPacket P vQ) g x ∈ Q1)
    (hgen2 : T.generator ∈ Q2)
    (hstable2 : ∀ (g : G.Carrier), g ∈ G.splittingMonoid →
      ∀ x : TensorPacket L vQ, x ∈ Q2 →
        (LGPMonoidAction.actionOnTensorPacket P vQ) g x ∈ Q2) :
    T.possibleImage ⊆ Q1 ⊓ Q2 := by
  intro x hx
  exact ⟨possibleImage_subset_of_generator_mem T Q1 hgen1 hstable1 hx,
    possibleImage_subset_of_generator_mem T Q2 hgen2 hstable2 hx⟩

theorem possibleImage_subset_of_le {l : PrimeGeFive} {G : LGPMonoid.{uM} l}
    {R : Type*} [CommSemiring R]
    {VQ : Type*} {Place : VQ → Type*} {j : Nat}
    {L : LogShellFamily R Place j}
    {P : LGPMonoidAction G R L} {vQ : VQ}
    (T : ThetaPilotObject P vQ) (Q Q' : Submodule R (TensorPacket L vQ))
    (hQ : Q ≤ Q')
    (hgen : T.generator ∈ Q)
    (hstable : ∀ (g : G.Carrier), g ∈ G.splittingMonoid →
      ∀ x : TensorPacket L vQ, x ∈ Q →
        (LGPMonoidAction.actionOnTensorPacket P vQ) g x ∈ Q) :
    T.possibleImage ⊆ Q' :=
  (possibleImage_subset_of_generator_mem T Q hgen hstable).trans hQ

end

end LeanFormal.IUT
