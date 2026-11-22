import LeanFormal.IUT.IUTIII.Theorem311.MultiradialOutputKernel
import LeanFormal.IUT.IUTIII.Theorem311.SourceFaithfulBoundary
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Ind2 reduction: the second-link compatibility without identifying alien copies

Frozen target: `LeanFormal/IUT/IUTIII/Theorem311/Indeterminacy/Ind2.lean`
(`IUT-III.Ind2`); its note at `Ind2.lean:9` reads "Prove the second link
compatibility without identifying alien copies."

Original-text counterpart (`D:/lean/papers/motizuki_corpus/text`):

* IUT III, Theorem 3.11, (i): the multiradial representation is "regarded up to
  indeterminacies of the following two types", where "(Ind2)" is induced by "the
  action of independent copies of Ism ... on each of the direct summands of the
  j+1 factors appearing in the tensor product used to define
  I_Q(S±_{j+1}; n,◦D⊢_{vQ})" (Proposition 1.2, (vi) of IUT II defines Ism).
* IUT III, Theorem 3.11, (iii), and Remark 3.11.3, (x): the construction is
  "stabilized/equivariant/functorial with respect to arbitrary automorphisms of
  the domain and codomain" of the horizontal arrows, i.e. of the Θ×μ_LGP-link;
  "(Ind2)" is precisely the compatibility with those automorphisms.

This module is a **reduction form** (缩减形式): the concrete F⊢×μ-prime-strips,
tensor packets, and Ism-actions of the paper are not constructed here.  The two
mutually alien copies enter as two `Core` values of the existing multiradial
skeleton, and the following structural content is proved.

* The link transports (Ind1)- and (Ind2)-indeterminacy steps between the copies
  through the given correspondence `labelCopyMap` of the two *independent*
  copies (`linkMap_ind1Step`, `linkMap_ind2Step`).
* The link respects the indeterminacy relation generated jointly by (Ind1) and
  (Ind2), so the construction is well defined "regarded up to (Ind1), (Ind2)":
  it descends to the indeterminacy quotients (`secondLinkDescent`).
* The descended map is forced: it is unique among maps with the prescribed
  values on representatives (`secondLinkDescent_unique`).
* If the link preserves the level invariant, the descent never collapses
  distinct levels (`secondLinkDescent_no_level_collapse`), which is the
  "distinguishing [i.e., not identifying]" property of IUT III, Remark 3.11.3,
  (vii).

No hypothesis and no conclusion below identifies the two copies: the datum
carries no equation `linkMap = id`, no equation `labelCopyMap = id`, no carrier
equality `Native = Alien`, and no isomorphism hypothesis.  The remaining precise
gap (that the actual source link satisfies the equivariance law) is kept as a
card in the accompanying report; no statement below claims it.
-/

namespace LeanFormal.IUT

open MultiradialKernel

noncomputable section

universe u v

/-- The (Ind2)-compatibility datum between two mutually alien copies of the
multiradial output.

`labelCopyMap` relates the two *independent* copies of the indeterminacy label
group; `linkMap` is the second link (the map induced by the horizontal arrow of
the log-theta-lattice) between the two carriers.  The fields `linkMap_ind1` and
`linkMap_ind2` are the compatibility laws: the link intertwines the two copies'
(Ind1)/(Ind2)-indeterminacy actions through `labelCopyMap`.  The copies are
related only through these maps; nothing identifies them. -/
structure Ind2AlienLink (LabelNative LabelAlien : Type u)
    (Native Alien : Type v) [AddGroup LabelNative] [AddGroup LabelAlien] where
  nativeCore : Core LabelNative Native
  alienCore : Core LabelAlien Alien
  labelCopyMap : LabelNative → LabelAlien
  linkMap : Native → Alien
  linkMap_ind1 : ∀ g a, linkMap (nativeCore.ind1 g a) =
    alienCore.ind1 (labelCopyMap g) (linkMap a)
  linkMap_ind2 : ∀ g a, linkMap (nativeCore.ind2 g a) =
    alienCore.ind2 (labelCopyMap g) (linkMap a)

namespace Ind2AlienLink

variable {LabelNative LabelAlien : Type u} {Native Alien : Type v}
  [AddGroup LabelNative] [AddGroup LabelAlien]
  (D : Ind2AlienLink LabelNative LabelAlien Native Alien)

/-! ## Step-level compatibility -/

/-- The link transports (Ind1)-indeterminacy steps to (Ind1)-indeterminacy
steps of the alien copy, through the copy correspondence `labelCopyMap`. -/
theorem linkMap_ind1Step {a b : Native}
    (h : Core.Ind1Step D.nativeCore a b) :
    Core.Ind1Step D.alienCore (D.linkMap a) (D.linkMap b) := by
  rcases h with ⟨g, rfl⟩
  exact ⟨D.labelCopyMap g, (D.linkMap_ind1 g a).symm⟩

/-- The link transports (Ind2)-indeterminacy steps to (Ind2)-indeterminacy
steps of the alien copy: the second-link compatibility at the step level. -/
theorem linkMap_ind2Step {a b : Native}
    (h : Core.Ind2Step D.nativeCore a b) :
    Core.Ind2Step D.alienCore (D.linkMap a) (D.linkMap b) := by
  rcases h with ⟨g, rfl⟩
  exact ⟨D.labelCopyMap g, (D.linkMap_ind2 g a).symm⟩

/-! ## Descent through the joint (Ind1)/(Ind2) indeterminacy relation -/

/-- The link respects the indeterminacy relation generated jointly by the
(Ind1) and (Ind2) steps. -/
theorem linkMap_respects_indeterminacy {a b : Native}
    (h : Core.GeneratedEqualityRelation D.nativeCore a b) :
    Core.GeneratedEqualityRelation D.alienCore (D.linkMap a) (D.linkMap b) := by
  induction h with
  | refl a => exact Core.GeneratedEqualityRelation.refl _
  | ind1 hstep => exact Core.GeneratedEqualityRelation.ind1 (D.linkMap_ind1Step hstep)
  | ind2 hstep => exact Core.GeneratedEqualityRelation.ind2 (D.linkMap_ind2Step hstep)
  | symm _ ih => exact Core.GeneratedEqualityRelation.symm ih
  | trans _ _ ih₁ ih₂ => exact Core.GeneratedEqualityRelation.trans ih₁ ih₂

/-- The datum packaged as the existing generic quotient-transport kernel
(`IUT-III.generic-quotient-transport`). -/
def asQuotientCompatibleMap :
    QuotientCompatibleMap (Core.generatedSetoid D.nativeCore)
      (Core.generatedSetoid D.alienCore) where
  map := D.linkMap
  respects := fun {_ _} h => D.linkMap_respects_indeterminacy h

/-- The map induced by the second link on the indeterminacy classes: the
construction "regarded up to (Ind1), (Ind2)". -/
def secondLinkDescent :
    Core.GeneratedQuotient D.nativeCore → Core.GeneratedQuotient D.alienCore :=
  Quotient.map' D.linkMap (fun _ _ h => D.linkMap_respects_indeterminacy h)

@[simp] theorem secondLinkDescent_mk (a : Native) :
    D.secondLinkDescent (Quotient.mk'' a) = Quotient.mk'' (D.linkMap a) :=
  Quotient.map'_mk'' D.linkMap
    (fun _ _ h => D.linkMap_respects_indeterminacy h) a

/-- Consistency with the existing `QuotientCompatibleMap.lift` kernel: the
descent is exactly the lift of the packaged datum. -/
theorem secondLinkDescent_eq_lift :
    D.secondLinkDescent = D.asQuotientCompatibleMap.lift := by
  funext q
  refine Quotient.inductionOn q ?_
  intro a
  rw [secondLinkDescent_mk]
  simp only [QuotientCompatibleMap.lift, Quotient.map_mk]
  rfl

/-- The (Ind1)-indeterminacy is invisible on the classes: the descended map
cannot distinguish an (Ind1)-step from the original value. -/
theorem secondLinkDescent_ind1Step (g : LabelNative) (a : Native) :
    D.secondLinkDescent (Quotient.mk'' (D.nativeCore.ind1 g a)) =
      D.secondLinkDescent (Quotient.mk'' a) := by
  rw [secondLinkDescent_mk, secondLinkDescent_mk, D.linkMap_ind1]
  exact (Core.generatedQuotientMap_eq_of_generated D.alienCore
    (.ind1 ⟨D.labelCopyMap g, rfl⟩)).symm

/-- The (Ind2)-indeterminacy is invisible on the classes: the descended map
cannot distinguish an (Ind2)-step from the original value. -/
theorem secondLinkDescent_ind2Step (g : LabelNative) (a : Native) :
    D.secondLinkDescent (Quotient.mk'' (D.nativeCore.ind2 g a)) =
      D.secondLinkDescent (Quotient.mk'' a) := by
  rw [secondLinkDescent_mk, secondLinkDescent_mk, D.linkMap_ind2]
  exact (Core.generatedQuotientMap_eq_of_generated D.alienCore
    (.ind2 ⟨D.labelCopyMap g, rfl⟩)).symm

/-! ## Uniqueness and non-collapse -/

/-- The descended map is the unique map out of the indeterminacy quotient whose
values on representatives are the link images.  This is the precise
"stabilized/equivariant/functorial" content of the reduction: the compatibility
map is forced, so no identification can be smuggled in through an alternative
choice of descent. -/
theorem secondLinkDescent_unique
    (h : Core.GeneratedQuotient D.nativeCore → Core.GeneratedQuotient D.alienCore)
    (hmk : ∀ a, h (Quotient.mk'' a) = Quotient.mk'' (D.linkMap a)) :
    h = D.secondLinkDescent := by
  funext q
  refine Quotient.inductionOn q ?_
  intro a
  rw [hmk a, secondLinkDescent_mk]

/-- Non-collapse: if the link preserves the level invariant, then the descended
map separates indeterminacy classes of distinct native level -- the
"distinguishing [i.e., not identifying] data" property of IUT III,
Remark 3.11.3, (vii), transported through the link. -/
theorem secondLinkDescent_no_level_collapse
    (hlinkLevel : ∀ a, D.alienCore.level (D.linkMap a) = D.nativeCore.level a)
    {a b : Native} (hlevel : D.nativeCore.level a ≠ D.nativeCore.level b) :
    D.secondLinkDescent (Quotient.mk'' a) ≠
      D.secondLinkDescent (Quotient.mk'' b) := by
  rw [secondLinkDescent_mk, secondLinkDescent_mk]
  refine Core.generatedQuotient_no_level_collapse D.alienCore ?_
  intro hlevelAlien
  exact hlevel ((hlinkLevel a).symm.trans (hlevelAlien.trans (hlinkLevel b)))

/-! ## The same-copy (diagonal) case -/

/-- The diagonal datum on a single copy: `linkMap = id` and `labelCopyMap = id`.
This is the special (same-copy) case; the general datum never assumes it. -/
def diagonal {Label : Type u} {Choice : Type v} [AddGroup Label]
    (core : Core Label Choice) : Ind2AlienLink Label Label Choice Choice where
  nativeCore := core
  alienCore := core
  labelCopyMap := id
  linkMap := id
  linkMap_ind1 := fun _ _ => rfl
  linkMap_ind2 := fun _ _ => rfl

/-- On the diagonal datum the descent is the identity: on a single copy the
second link changes no indeterminacy class. -/
theorem diagonal_secondLinkDescent_eq_id {Label : Type u} {Choice : Type v}
    [AddGroup Label] (core : Core Label Choice) :
    (diagonal core).secondLinkDescent = id := by
  funext q
  refine Quotient.inductionOn q ?_
  intro a
  rw [secondLinkDescent_mk]
  rfl

end Ind2AlienLink

/-! ## Consistency with the existing skeleton -/

/-- Extracted card: the within-copy (single-theater) (Ind2) descent that the
existing skeleton already provides (`SourceFaithfulBoundary.lean:640`,
`quotientMap_respects_ind2`).  This is the special case of the present
construction in which the two copies coincide; the cross-copy content above is
not derivable from the skeleton alone -- see the necessity refutation below. -/
theorem extractedWithinTheaterInd2Descent {Label : Type u} {Choice : Type v}
    [AddGroup Label] [Preorder Choice]
    (I : Theorem311Source.Input Label Choice) {a b : Choice}
    (h : Theorem311Source.Ind2Relation I a b) :
    Theorem311Source.quotientMap I a = Theorem311Source.quotientMap I b :=
  Theorem311Source.quotientMap_respects_ind2 I h

/-! ## Models: necessity of the law and non-vacuity of the datum -/

namespace Ind2AlienLinkModels

/-- A core whose second link acts by translation: `ind2 g c = c + g`.  Used to
show that the equivariance law is a genuine constraint on the datum. -/
def translationSecondLinkCore : Core Int Int where
  base := 0
  level := fun _ => 0
  ind1 := fun _ c => c
  ind2 := fun g c => c + g
  ind3 := fun _ c => c
  ind1_zero := fun _ => rfl
  ind1_add := fun _ _ _ => rfl
  ind1_inverse := fun _ _ => rfl
  ind2_zero := fun c => by simp
  ind2_add := fun g h c => by ring
  ind2_inverse := fun g c => by ring
  ind3_zero := fun _ => rfl
  ind3_add := fun _ _ _ => rfl
  ind1_ind2_commute := fun _ _ _ => rfl
  ind1_ind3_commute := fun _ _ _ => rfl
  ind2_ind3_commute := fun _ _ _ => rfl
  ind1_level := fun _ _ => rfl
  ind2_level := fun _ _ => rfl
  ind3_level := fun _ _ => le_rfl

/-- A core whose second link acts by the identity: the trivial companion of
`translationSecondLinkCore`. -/
def trivialSecondLinkCore : Core Int Int where
  base := 0
  level := fun _ => 0
  ind1 := fun _ c => c
  ind2 := fun _ c => c
  ind3 := fun _ c => c
  ind1_zero := fun _ => rfl
  ind1_add := fun _ _ _ => rfl
  ind1_inverse := fun _ _ => rfl
  ind2_zero := fun _ => rfl
  ind2_add := fun _ _ _ => rfl
  ind2_inverse := fun _ _ => rfl
  ind3_zero := fun _ => rfl
  ind3_add := fun _ _ _ => rfl
  ind1_ind2_commute := fun _ _ _ => rfl
  ind1_ind3_commute := fun _ _ _ => rfl
  ind2_ind3_commute := fun _ _ _ => rfl
  ind1_level := fun _ _ => rfl
  ind2_level := fun _ _ => rfl
  ind3_level := fun _ _ => le_rfl

/-- Necessity of the equivariance law: dropping `linkMap_ind2` from the datum
makes the step-transport claim false in general.  Concretely, the identity map
between the two cores above does not transport the (Ind2)-step `0 -> 1` of the
translation core to an (Ind2)-step of the trivial core.  Hence
`linkMap_ind2Step` is not derivable without the law, and the compatibility
content of the reduction lies genuinely in the law. -/
theorem secondLinkStepLaw_necessary :
    ¬ (∀ {a b : Int}, Core.Ind2Step translationSecondLinkCore a b →
      Core.Ind2Step trivialSecondLinkCore a b) := by
  intro h
  have hstep : Core.Ind2Step translationSecondLinkCore (0 : Int) 1 :=
    ⟨1, by
      change (0 : Int) + 1 = 1
      rfl⟩
  have halien : Core.Ind2Step trivialSecondLinkCore (0 : Int) 1 := h hstep
  rcases halien with ⟨m, hm⟩
  exact Int.zero_ne_one hm

/-- Non-diagonal inhabitant: the alien copy is the native copy translated by
`shift`, via `linkMap z = z + shift`.  For `shift ≠ 0` the alien copy is a
genuine translate of the native copy, so the compatibility proved for this
datum is not a disguised identification of the two copies. -/
def translatedAlienCopy (shift : Int) : Ind2AlienLink Int Int Int Int where
  nativeCore := translationSecondLinkCore
  alienCore := translationSecondLinkCore
  labelCopyMap := id
  linkMap := fun z => z + shift
  linkMap_ind1 := fun _ _ => rfl
  linkMap_ind2 := fun g a => by
    change a + g + shift = a + shift + g
    ring

/-- The translated copy is genuinely alien: its link map does not fix the
origin when `shift ≠ 0`. -/
theorem translatedAlienCopy_not_identity {shift : Int} (hshift : shift ≠ 0) :
    (translatedAlienCopy shift).linkMap 0 ≠ 0 := by
  change (0 : Int) + shift ≠ 0
  simpa using hshift

/-- A core on the product carrier `Bool x Int` whose second link acts on the
second coordinate; its first link acts by the identity. -/
def productSecondLinkCore : Core Int (Bool × Int) where
  base := (true, 0)
  level := fun _ => 0
  ind1 := fun _ p => p
  ind2 := fun g p => (p.1, p.2 + g)
  ind3 := fun _ p => p
  ind1_zero := fun _ => rfl
  ind1_add := fun _ _ _ => rfl
  ind1_inverse := fun _ _ => rfl
  ind2_zero := fun p => by simp
  ind2_add := fun g h p => by simp [add_assoc]
  ind2_inverse := fun g p => by simp [add_assoc]
  ind3_zero := fun _ => rfl
  ind3_add := fun _ _ _ => rfl
  ind1_ind2_commute := fun _ _ _ => rfl
  ind1_ind3_commute := fun _ _ _ => rfl
  ind2_ind3_commute := fun _ _ _ => rfl
  ind1_level := fun _ _ => rfl
  ind2_level := fun _ _ => rfl
  ind3_level := fun _ _ => le_rfl

/-- Cross-carrier inhabitant: the two copies live on different carrier types
(`Int` versus `Bool x Int`), so no equality between their elements is even
typeable; the compatibility laws nevertheless hold, with `linkMap z = (true, z)`. -/
def crossCarrierCopy : Ind2AlienLink Int Int Int (Bool × Int) where
  nativeCore := translationSecondLinkCore
  alienCore := productSecondLinkCore
  labelCopyMap := id
  linkMap := fun z => (true, z)
  linkMap_ind1 := fun _ _ => rfl
  linkMap_ind2 := fun _ _ => rfl

end Ind2AlienLinkModels

end

end LeanFormal.IUT
