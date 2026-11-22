/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import tmp.sheaf.xif.paper.S2622TorsorSectionUniqueActual

/-!
# S2665: the G-torsor section presheaf is a sheaf on the slice etale site

For a free action-groupoid datum `D : S2622TorsorData`, a base `S` and two
sections `M N : S ⟶ D.U`, the presheaf of group elements `g` with
`(T.hom ≫ M) ≫ rho g = T.hom ≫ N` is a sheaf for the slice etale topology.

The proof has two ingredients:

* sections over a fixed object are unique by freeness (`S2620_torsor_section_unique`),
  so the presheaf is a presheaf of subsingletons;
* to glue a compatible family we use the chosen member `f : Y ⟶ X` of the covering
  sieve.  Compatibility on the pullback `Z ×_X Y` shows that the group element at
  any other member `h : Z ⟶ X` equals the one at `f`.  Hence both
  `(X.hom ≫ M) ≫ rho g` and `X.hom ≫ N` become equal after restriction to every
  member of the sieve, so separatedness of the representable Hom sheaf
  (`S2620_representableHom_slice_isSheaf`) descends the equality to `X`.
  The vacuous (empty) cover case follows from separatedness as well.
-/

noncomputable section
open CategoryTheory
open LeanFormal.IUT
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S2665TorsorSheafActual

open LeanFormal.IUT.XiFPaper.S2619ActionGroupoidFiberSkeleton
open LeanFormal.IUT.XiFPaper.S2621TorsorPresheafActual
open LeanFormal.IUT.XiFPaper.S2622TorsorSectionUniqueActual
open LeanFormal.IUT.XiFPaper.S2620RepresentableSheafActual

universe u

variable {l : PrimeGeFive} {F : Type u} [Field F]
variable (D : S2622TorsorData (l := l) (F := F))
variable (S : Iut.SchemeOverField F)
variable (M N : S2621Hom (l := l) (F := F) D.toS2619ActionGroupoidData S)

/-- The defining equality of a torsor section at a slice object. -/
def S2665TorsorEq (T : (Over S)ᵒᵖ) (g : ZMod l.value) : Prop :=
  (T.unop.hom ≫ M) ≫ (D.toS2619ActionGroupoidData.rho g).hom = T.unop.hom ≫ N

/-- Naturality of the section predicate: restricting along a slice morphism
only precomposes the morphism part. -/
lemma S2665TorsorEq_naturality {T T' : (Over S)ᵒᵖ} (a : T ⟶ T') (g : ZMod l.value) :
    (T'.unop.hom ≫ M) ≫ (D.toS2619ActionGroupoidData.rho g).hom
      = a.unop.left ≫ ((T.unop.hom ≫ M) ≫ (D.toS2619ActionGroupoidData.rho g).hom) := by
  rw [← Over.w a.unop]
  simp only [Category.assoc]

/-- The representable Hom presheaf evaluates a slice morphism by precomposition. -/
lemma S2665Hom_map_apply {Z X : Over S} (h : Z ⟶ X)
    (t : X.left ⟶ D.toS2619ActionGroupoidData.U) :
    ((Over.forget S).op ⋙ yoneda.obj D.toS2619ActionGroupoidData.U).map h.op t
      = h.left ≫ t := rfl

/-- Sections of the torsor presheaf over any slice object have at most one element. -/
lemma S2665TorsorPresheaf_subsingleton (T : (Over S)ᵒᵖ) :
    Subsingleton
      ((S2620TorsorPresheaf (l := l) (F := F) D.toS2619ActionGroupoidData S M N).obj T) := by
  constructor
  intro a b
  rcases a with ⟨⟨g₁, h₁⟩⟩
  rcases b with ⟨⟨g₂, h₂⟩⟩
  have hg : g₁ = g₂ := S2620_torsor_section_unique D S M N T g₁ g₂ h₁ h₂
  cases hg
  rfl

/-- **The G-torsor section presheaf is a sheaf for the slice etale topology.** -/
theorem S2620_G_torsor_isSheaf
    (D : S2622TorsorData (l := l) (F := F))
    (S : Iut.SchemeOverField F)
    (M N : S2621Hom (l := l) (F := F) D.toS2619ActionGroupoidData S) :
    Presheaf.IsSheaf (S2620Slice (F := F) S)
      (S2620TorsorPresheaf (l := l) (F := F) D.toS2619ActionGroupoidData S M N) := by
  rw [isSheaf_iff_isSheaf_of_type]
  set P : (Over S)ᵒᵖ ⥤ Type (u+1) :=
    S2620TorsorPresheaf (l := l) (F := F) D.toS2619ActionGroupoidData S M N with hP
  have hHsheaf : Presieve.IsSheaf (S2620Slice (F := F) S)
      ((Over.forget S).op ⋙ yoneda.obj D.toS2619ActionGroupoidData.U) := by
    refine (isSheaf_iff_isSheaf_of_type (S2620Slice (F := F) S)
      ((Over.forget S).op ⋙ yoneda.obj D.toS2619ActionGroupoidData.U)).1 ?_
    exact S2620_representableHom_slice_isSheaf (F := F) D.toS2619ActionGroupoidData.U S
  have hsub : ∀ T : (Over S)ᵒᵖ, Subsingleton (P.obj T) := by
    intro T
    constructor
    intro a b
    rcases a with ⟨⟨g₁, h₁⟩⟩
    rcases b with ⟨⟨g₂, h₂⟩⟩
    have hg : g₁ = g₂ := S2620_torsor_section_unique D S M N T g₁ g₂ h₁ h₂
    cases hg
    rfl
  intro X R hR x hx
  by_cases hmem : ∃ (Y : Over S) (f : Y ⟶ X), R.arrows f
  · -- Nonempty cover: choose one member and show its group element works everywhere.
    obtain ⟨Y, f, hf⟩ := hmem
    set g : ZMod l.value := (x f hf).down.val with hgdef
    have hX : S2665TorsorEq D S M N (Opposite.op X) g := by
      have hsepR : Presieve.IsSeparatedFor
          ((Over.forget S).op ⋙ yoneda.obj D.toS2619ActionGroupoidData.U) (R : Presieve X) :=
        hHsheaf.isSeparated R hR
      let t₁ : X.left ⟶ D.toS2619ActionGroupoidData.U :=
        (X.hom ≫ M) ≫ (D.toS2619ActionGroupoidData.rho g).hom
      let t₂ : X.left ⟶ D.toS2619ActionGroupoidData.U := X.hom ≫ N
      refine Presieve.IsSeparatedFor.ext hsepR (t₁ := t₁) (t₂ := t₂) ?_
      intro Z h hh
      show ((Over.forget S).op ⋙ yoneda.obj D.toS2619ActionGroupoidData.U).map h.op t₁
        = ((Over.forget S).op ⋙ yoneda.obj D.toS2619ActionGroupoidData.U).map h.op t₂
      rw [S2665Hom_map_apply, S2665Hom_map_apply]
      have hnat1 : h.left ≫ t₁ = (Z.hom ≫ M) ≫ (D.toS2619ActionGroupoidData.rho g).hom := by
        dsimp only [t₁]
        exact (S2665TorsorEq_naturality (D := D) (S := S) (M := M) (a := h.op) (g := g)).symm
      have hnat2 : h.left ≫ t₂ = Z.hom ≫ N := by
        dsimp only [t₂]
        rw [← Category.assoc, Over.w h]
      have hZ : S2665TorsorEq D S M N (Opposite.op Z) g := by
        have hcompat := hx (Y₁ := Z) (Y₂ := Y) (Z := Limits.pullback h f)
          (g₁ := Limits.pullback.fst h f) (g₂ := Limits.pullback.snd h f)
          (f₁ := h) (f₂ := f) hh hf (Limits.pullback.condition)
        have hval : (x h hh).down.val = (x f hf).down.val := by
          exact congrArg (fun u => u.down.val) hcompat
        rw [show g = (x h hh).down.val by rw [hgdef]; exact hval.symm]
        exact (x h hh).down.property
      rw [hnat1, hnat2]
      exact hZ
    refine ⟨ULift.up ⟨g, hX⟩, ?_, ?_⟩
    · intro Z h _
      exact (hsub (Opposite.op Z)).allEq _ _
    · intro t' _
      exact (hsub (Opposite.op X)).allEq t' _
  · -- Empty cover: any element restricts vacuously; separatedness makes H(X) a singleton.
    push Not at hmem
    have hsepR : Presieve.IsSeparatedFor
        ((Over.forget S).op ⋙ yoneda.obj D.toS2619ActionGroupoidData.U) (R : Presieve X) :=
      hHsheaf.isSeparated R hR
    have hsubH : Subsingleton
        (((Over.forget S).op ⋙ yoneda.obj D.toS2619ActionGroupoidData.U).obj (Opposite.op X)) := by
      constructor
      intro t₁ t₂
      exact hsepR (fun Y f hf => (hmem Y f hf).elim) t₁ t₂
        (fun Y f hf => (hmem Y f hf).elim) (fun Y f hf => (hmem Y f hf).elim)
    have hE0 : S2665TorsorEq D S M N (Opposite.op X) (0 : ZMod l.value) := by
      have hEq : (X.hom ≫ M) ≫ (D.toS2619ActionGroupoidData.rho (0 : ZMod l.value)).hom
          = X.hom ≫ N := hsubH.allEq _ _
      exact hEq
    refine ⟨ULift.up ⟨(0 : ZMod l.value), hE0⟩, ?_, ?_⟩
    · intro Z h hh
      exact (hmem Z h hh).elim
    · intro t' _
      exact (hsub (Opposite.op X)).allEq t' _

/-- The statement as required by the D9 consumer, with all arguments explicit. -/
example
    (D : S2622TorsorData (l := l) (F := F))
    (S : Iut.SchemeOverField F)
    (M N : S2621Hom (l := l) (F := F) D.toS2619ActionGroupoidData S) :
    Presheaf.IsSheaf (S2620Slice (F := F) S)
      (S2620TorsorPresheaf (l := l) (F := F) D.toS2619ActionGroupoidData S M N) :=
  S2620_G_torsor_isSheaf D S M N

#print axioms S2620_G_torsor_isSheaf

end LeanFormal.IUT.XiFPaper.S2665TorsorSheafActual
end
