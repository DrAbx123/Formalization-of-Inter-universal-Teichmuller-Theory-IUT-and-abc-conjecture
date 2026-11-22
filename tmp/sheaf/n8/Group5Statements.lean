/-
N8 group5 — stage-2 trial statements: the (IPL) admissible-family relation layer.

Source: tmp/sheaf/n8/group5-STAGE1.md §5.1.  Paper anchor: IUT III,
Remark 3.11.1, (iii).  The family `P` records *some possible* poly-isomorphism
images; `∃ φ ∈ P` does not say that `P` covers all possible images or that the
relation is universal/the full relation.

Consumer: the (IPL) slot through linkEvidenceOfQCMPWithIPL; there the relation
reads the second leg through E.polyIso.  This file restores the family
quantifier at the relation layer.

Standalone trial file: no production edit; all declarations proved outright
(no sorry).
-/
import LeanFormal.IUT.IUTIII.Theorem311.SourcePolyIsoTransportLaws

namespace LeanFormal.IUT.Tmp.N8Group5

open LeanFormal.IUT
open LeanFormal.IUT.MultiradialKernel
open LeanFormal.IUT.Theorem311Source.PolyIsoTransport

universe u v w

/-- (IPL) admissible-family relation at the reduced kernel shell: `a` and `b`
are connected through some state whose second leg is read through *some*
member `φ` of `P`.  The existential records one possible image; it does not
assert that every possible image is in the relation, nor that `P` is closed
under all operations. -/
def familyRel {Label : Type u} {Choice : Type v} [AddGroup Label]
    {core1 core2 : Core Label Choice} (L : LinkSpan core1 core2)
    (P : Set (L.mid ≃ L.mid)) (a b : Choice) : Prop :=
  ∃ m : L.mid, L.left m = a ∧ ∃ φ ∈ P, L.right (φ m) = b

/-- The (Ind1)-action as an equivalence; `act1 (-g)` is its inverse. -/
def act1Equiv {Label : Type u} {Choice : Type v} [AddGroup Label]
    {core1 core2 : Core Label Choice} (L : LinkSpan core1 core2) (g : Label) :
    L.mid ≃ L.mid where
  toFun := L.act1 g
  invFun := L.act1 (-g)
  left_inv m := by
    rw [← L.act1_add g (-g) m, add_neg_cancel, L.act1_zero]
  right_inv m := by
    rw [← L.act1_add (-g) g m, neg_add_cancel, L.act1_zero]

/-- The (Ind2)-action as an equivalence; `act2 (-g)` is its inverse. -/
def act2Equiv {Label : Type u} {Choice : Type v} [AddGroup Label]
    {core1 core2 : Core Label Choice} (L : LinkSpan core1 core2) (g : Label) :
    L.mid ≃ L.mid where
  toFun := L.act2 g
  invFun := L.act2 (-g)
  left_inv m := by
    rw [← L.act2_add g (-g) m, add_neg_cancel, L.act2_zero]
  right_inv m := by
    rw [← L.act2_add (-g) g m, neg_add_cancel, L.act2_zero]

@[simp] theorem act1Equiv_apply {Label : Type u} {Choice : Type v} [AddGroup Label]
    {core1 core2 : Core Label Choice} (L : LinkSpan core1 core2) (g : Label)
    (m : L.mid) : act1Equiv L g m = L.act1 g m := rfl

@[simp] theorem act1Equiv_symm_apply {Label : Type u} {Choice : Type v} [AddGroup Label]
    {core1 core2 : Core Label Choice} (L : LinkSpan core1 core2) (g : Label)
    (m : L.mid) : (act1Equiv L g).symm m = L.act1 (-g) m := rfl

@[simp] theorem act2Equiv_apply {Label : Type u} {Choice : Type v} [AddGroup Label]
    {core1 core2 : Core Label Choice} (L : LinkSpan core1 core2) (g : Label)
    (m : L.mid) : act2Equiv L g m = L.act2 g m := rfl

@[simp] theorem act2Equiv_symm_apply {Label : Type u} {Choice : Type v} [AddGroup Label]
    {core1 core2 : Core Label Choice} (L : LinkSpan core1 core2) (g : Label)
    (m : L.mid) : (act2Equiv L g).symm m = L.act2 (-g) m := rfl

/-- (Ind1) exchange with the family stable under conjugation by the (Ind1)-action.
`hP` says `a_{-g} ∘ φ ∘ a_g ∈ P`; the witness state is changed simultaneously
to `act1 (-g) m` in the forward direction and `act1 g m` in the reverse direction. -/
theorem familyRel_ind1_iff {Label : Type u} {Choice : Type v} [AddGroup Label]
    {core1 core2 : Core Label Choice} (L : LinkSpan core1 core2)
    (P : Set (L.mid ≃ L.mid))
    (hP : ∀ φ ∈ P, ∀ g : Label,
      ((act1Equiv L g).trans (φ.trans (act1Equiv L g).symm)) ∈ P)
    (a b : Choice) (g : Label) :
    familyRel L P (core1.ind1 g a) b ↔ familyRel L P a (core2.ind1 (-g) b) := by
  constructor
  · rintro ⟨m, h1, φ, hφ, h2⟩
    refine ⟨L.act1 (-g) m, ?_,
      (act1Equiv L g).trans (φ.trans (act1Equiv L g).symm), hP φ hφ g, ?_⟩
    · rw [L.left_act1, h1, core1.ind1_inverse]
    · simp only [Equiv.trans_apply, act1Equiv_apply, act1Equiv_symm_apply]
      rw [← L.act1_add (-g) g m, neg_add_cancel, L.act1_zero]
      rw [L.right_act1, h2]
  · rintro ⟨m, h1, φ, hφ, h2⟩
    refine ⟨L.act1 g m, ?_,
      (act1Equiv L (-g)).trans (φ.trans (act1Equiv L (-g)).symm), hP φ hφ (-g), ?_⟩
    · rw [L.left_act1, h1]
    · simp only [Equiv.trans_apply, act1Equiv_apply, act1Equiv_symm_apply]
      rw [← L.act1_add g (-g) m, add_neg_cancel, L.act1_zero]
      rw [neg_neg, L.right_act1, h2, ind1_inv_cancel core2 g b]

/-- (Ind2) exchange with the family stable under conjugation by the (Ind2)-action. -/
theorem familyRel_ind2_iff {Label : Type u} {Choice : Type v} [AddGroup Label]
    {core1 core2 : Core Label Choice} (L : LinkSpan core1 core2)
    (P : Set (L.mid ≃ L.mid))
    (hP : ∀ φ ∈ P, ∀ g : Label,
      ((act2Equiv L g).trans (φ.trans (act2Equiv L g).symm)) ∈ P)
    (a b : Choice) (g : Label) :
    familyRel L P (core1.ind2 g a) b ↔ familyRel L P a (core2.ind2 (-g) b) := by
  constructor
  · rintro ⟨m, h1, φ, hφ, h2⟩
    refine ⟨L.act2 (-g) m, ?_,
      (act2Equiv L g).trans (φ.trans (act2Equiv L g).symm), hP φ hφ g, ?_⟩
    · rw [L.left_act2, h1, core1.ind2_inverse]
    · simp only [Equiv.trans_apply, act2Equiv_apply, act2Equiv_symm_apply]
      rw [← L.act2_add (-g) g m, neg_add_cancel, L.act2_zero]
      rw [L.right_act2, h2]
  · rintro ⟨m, h1, φ, hφ, h2⟩
    refine ⟨L.act2 g m, ?_,
      (act2Equiv L (-g)).trans (φ.trans (act2Equiv L (-g)).symm), hP φ hφ (-g), ?_⟩
    · rw [L.left_act2, h1]
    · simp only [Equiv.trans_apply, act2Equiv_apply, act2Equiv_symm_apply]
      rw [← L.act2_add g (-g) m, add_neg_cancel, L.act2_zero]
      rw [neg_neg, L.right_act2, h2, ind2_inv_cancel core2 g b]

/-- Selected-member inclusion: if the supply's single `E.polyIso` belongs to
`P`, then every `polyIsoRel` witness is a `familyRel` witness.  This only
states inclusion for the selected member; it does not assert `QP ⊆ R`, does
not say the two relations are equal, and does not implement composition of
the two families. -/
theorem polyIsoRel_le_familyRel {Label : Type u} {Choice : Type v} [AddGroup Label]
    {core1 core2 : Core Label Choice} (L : LinkSpan core1 core2)
    (E : CardIPLTransportSupply L) (P : Set (L.mid ≃ L.mid))
    (h : E.polyIso ∈ P) (a b : Choice) :
    polyIsoRel L E a b → familyRel L P a b := by
  rintro ⟨m, h1, h2⟩
  exact ⟨m, h1, E.polyIso, h, h2⟩

end LeanFormal.IUT.Tmp.N8Group5