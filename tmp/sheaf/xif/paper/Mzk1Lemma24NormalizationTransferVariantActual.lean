import tmp.sheaf.xif.paper.Mzk1Lemma24AssemblyActual
import tmp.sheaf.xif.paper.Mzk1Lemma24NormalizationTransferActual
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-!
# STEP 0 prior-art: transfer variant|Mzk1Lemma24Goal|DecidableEq mismatch|Finset.image -> hits Mzk1Lemma24AssemblyActual:20 Mzk1Lemma24Goal (exists targetSet/unramifiedAt, Mzk1Lemma24StatementShape), Mzk1Lemma24NormalizationTransferActual (mzk1_normalization_transfer_shape/P1Morphism.comp + transport) -> ADAPT (instance-free variant stated with EXPLICIT membership iff instead of Finset.image, so abc's S3 goal transport does not depend on the DecidableEq instance used to form the images).

# Mzk1Lemma24NormalizationTransferVariantActual — instance-free goal transport for abc S3

This file provides the INSTANCE-FREE variant of the normalization transfer requested by
abc for the nested (m,d)-induction S3 step: the goal transport is stated via explicit
membership predicates `p ∈ U ↔ exists a in S, ofFinite a = p` and
`p ∈ V ↔ exists a in S, h (ofFinite a) = p`, so no equality of `Finset.image` values
(whose definitions depend on the DecidableEq instance) is ever needed.  The target
point of the next state is `h (ofFinite beta)`, which is not required to lie in V.
No fake; registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma24NormalizationTransferVariantActual

open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma24AssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma24NormalizationTransferActual

local instance : DecidableEq ℂ := Classical.decEq _

/-- **Instance-free goal transport (S3)**: given the Lemma 2.4 Goal at a next-state
finite set V (membership-characterized through a point map h applied to S) and base
point h(beta), produce the Goal at the current finite set U (membership-characterized
through ofFinite on S) and base point beta.  Both U and V are arbitrary Finsets with
the stated membership relation; no Finset.image instance is fixed in the statement. -/
theorem mzk1_normalization_transfer_goal_of_membership
    (S : Finset ℂ) (β : ℂ) (h : P1Point ℂ → P1Point ℂ)
    (U V : Finset (P1Point ℂ))
    (hU : ∀ p, p ∈ U ↔ ∃ a ∈ S, (P1Point.ofFinite (K := ℂ) a) = p)
    (hV : ∀ p, p ∈ V ↔ ∃ a ∈ S, h (P1Point.ofFinite (K := ℂ) a) = p)
    (goalNext : Mzk1Lemma24Goal V (h (P1Point.ofFinite (K := ℂ) β))) :
    Mzk1Lemma24Goal U (P1Point.ofFinite (K := ℂ) β) := by
  rcases goalNext with ⟨targetSet, unramifiedAt, hshape⟩
  rcases hshape with ⟨φ, hnc, hpres, hav, hunr⟩
  refine ⟨targetSet, (fun p => unramifiedAt (h p)), ?_⟩
  refine ⟨φ.comp h, hnc, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨a, haS, hap⟩ := (hU p).mp hp
    have hmemV : h p ∈ V := by
      rw [hV]
      exact ⟨a, haS, by rw [← hap]⟩
    exact hpres _ (by simpa using hmemV)
  · intro hmem
    exact hav hmem
  · intro z hz
    exact hunr (h z) hz

/-- Specialized form for the standard images (defined with the local Classical
DecidableEq of this file): transport from the h-image of S.backslash-points to the
ofFinite-image.  Provided for convenience; the membership version above is
preferred when the consumer's Finset.image instance is syntactically different. -/
theorem mzk1_normalization_transfer_goal_image
    (S : Finset ℂ) (β : ℂ) (h : P1Point ℂ → P1Point ℂ)
    (goalNext : Mzk1Lemma24Goal (S.image (fun a => h (P1Point.ofFinite (K := ℂ) a)))
      (h (P1Point.ofFinite (K := ℂ) β))) :
    Mzk1Lemma24Goal (S.image (fun a => P1Point.ofFinite (K := ℂ) a))
      (P1Point.ofFinite (K := ℂ) β) := by
  have hU : ∀ p, p ∈ S.image (fun a => P1Point.ofFinite (K := ℂ) a) ↔
      ∃ a ∈ S, P1Point.ofFinite (K := ℂ) a = p := by
    intro p; exact Finset.mem_image
  have hV : ∀ p, p ∈ S.image (fun a => h (P1Point.ofFinite (K := ℂ) a)) ↔
      ∃ a ∈ S, h (P1Point.ofFinite (K := ℂ) a) = p := by
    intro p; exact Finset.mem_image
  exact mzk1_normalization_transfer_goal_of_membership S β h _ _ hU hV goalNext

/-- Variant row record. -/
def normalizationTransferVariantRows : List (String × String × String) :=
  [ ("instance-free goal transport (explicit membership iff)", "A", "PROVED mzk1_normalization_transfer_goal_of_membership")
  , ("standard-image convenience form", "A", "PROVED mzk1_normalization_transfer_goal_image")
  , ("consumes Mzk1Lemma24Goal + Mzk1Lemma24StatementShape", "interface", "abc S3 nested assembly can import both")
  , ("DecidableEq mismatch avoided", "design", "statement uses membership iff; no Finset.image equality required") ]

/-- The variant row record has four rows. -/
theorem normalizationTransferVariantRows_length : normalizationTransferVariantRows.length = 4 := rfl

#check mzk1_normalization_transfer_goal_of_membership
#check mzk1_normalization_transfer_goal_image
#check normalizationTransferVariantRows_length

end LeanFormal.IUT.XiFPaper.Mzk1Lemma24NormalizationTransferVariantActual
end