import tmp.sheaf.xif.paper.S3127FullForgetActual
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
noncomputable section
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127FullForgetActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G3FullActual
variable {l : PrimeGeFive}

noncomputable def S3127G3eX
    (X : S3127FiniteEtaleOverKFull l) :
    (S3127FullEquivalence (l := l)).inverse.obj
      ((S3127FullForget (l := l)).obj X) ≅ X :=
  (S3127FullForget (l := l)).preimageIso
    ((S3127FullEquivalence (l := l)).counitIso.app
      ((S3127FullForget (l := l)).obj X))

noncomputable def S3127G3eY
    (Y : S3127FiniteEtaleOverKFull l) :
    (S3127FullEquivalence (l := l)).inverse.obj
      ((S3127FullForget (l := l)).obj Y) ≅ Y :=
  (S3127FullForget (l := l)).preimageIso
    ((S3127FullEquivalence (l := l)).counitIso.app
      ((S3127FullForget (l := l)).obj Y))

noncomputable def S3127G3DiagramIso2
    (X : S3127FiniteEtaleOverKFull l)
    (Z : FiniteEtaleCover (S1419AffineScheme l)) :
    pair ((S3127FullEquivalence (l := l)).inverse.obj
        ((S3127FullForget (l := l)).obj X))
      ((S3127FullEquivalence (l := l)).inverse.obj Z)
    ≅ pair X ((S3127FullEquivalence (l := l)).inverse.obj Z) :=
  Discrete.natIso (fun j => by
    rcases j with ⟨(_ | _)⟩
    · exact S3127G3eX X
    · exact Iso.refl _)
noncomputable def S3127G3C0
    {X Y : S3127FiniteEtaleOverKFull l}
    (j : (S3127FullForget (l := l)).obj X ⟶
      (S3127FullForget (l := l)).obj Y)
    (Z : FiniteEtaleCover (S1419AffineScheme l))
    (u : Z ⟶ (S3127FullForget (l := l)).obj Y) :
    Cocone (pair ((S3127FullEquivalence (l := l)).inverse.obj
        ((S3127FullForget (l := l)).obj X))
      ((S3127FullEquivalence (l := l)).inverse.obj Z)) where
  pt := ((S3127FullEquivalence (l := l)).inverse.mapCocone
    (BinaryCofan.mk j u)).pt
  ι :=
    { app := fun k => by
        rcases k with ⟨(_ | _)⟩
        · exact (S3127FullEquivalence (l := l)).inverse.map j
        · exact (S3127FullEquivalence (l := l)).inverse.map u
      naturality := by
        intro a b f
        rcases a with ⟨(_ | _)⟩ <;>
          rcases b with ⟨(_ | _)⟩ <;>
          rcases f with ⟨down⟩ <;>
          cases down with
          | up h => cases h <;> simp }

noncomputable def S3127G3CX
    {X Y : S3127FiniteEtaleOverKFull l}
    (j : (S3127FullForget (l := l)).obj X ⟶
      (S3127FullForget (l := l)).obj Y)
    (Z : FiniteEtaleCover (S1419AffineScheme l))
    (u : Z ⟶ (S3127FullForget (l := l)).obj Y) :
    Cocone (pair X ((S3127FullEquivalence (l := l)).inverse.obj Z)) :=
  (Cocone.precomposeEquivalence
    (S3127G3DiagramIso2 (l := l) X Z)).functor.obj
    (S3127G3C0 j Z u)

noncomputable def S3127G3Beta
    (X : S3127FiniteEtaleOverKFull l)
    (Z : FiniteEtaleCover (S1419AffineScheme l)) :
    (pair ((S3127FullForget (l := l)).obj X) Z) ⋙
        (S3127FullEquivalence (l := l)).inverse
      ≅ pair ((S3127FullEquivalence (l := l)).inverse.obj
          ((S3127FullForget (l := l)).obj X))
        ((S3127FullEquivalence (l := l)).inverse.obj Z) :=
  Discrete.natIso (fun j => by
    rcases j with ⟨(_ | _)⟩ <;> exact Iso.refl _)

noncomputable def S3127G3Alpha
    (X : S3127FiniteEtaleOverKFull l)
    (Z : FiniteEtaleCover (S1419AffineScheme l)) :
    (pair ((S3127FullForget (l := l)).obj X) Z) ⋙
        (S3127FullEquivalence (l := l)).inverse
      ≅ pair X ((S3127FullEquivalence (l := l)).inverse.obj Z) :=
  S3127G3Beta X Z ≪≫ S3127G3DiagramIso2 X Z

noncomputable def S3127G3E
    (X : S3127FiniteEtaleOverKFull l)
    (Z : FiniteEtaleCover (S1419AffineScheme l)) :
    Cocone (pair ((S3127FullForget (l := l)).obj X) Z ⋙
        (S3127FullEquivalence (l := l)).inverse) ≌
      Cocone (pair X ((S3127FullEquivalence (l := l)).inverse.obj Z)) :=
  Cocone.precomposeEquivalence (S3127G3Alpha X Z)

noncomputable def S3127G3CX2
    {X Y : S3127FiniteEtaleOverKFull l}
    (j : (S3127FullForget (l := l)).obj X ⟶
      (S3127FullForget (l := l)).obj Y)
    (Z : FiniteEtaleCover (S1419AffineScheme l))
    (u : Z ⟶ (S3127FullForget (l := l)).obj Y) :
    Cocone (pair X ((S3127FullEquivalence (l := l)).inverse.obj Z)) :=
  (S3127G3E X Z).functor.obj
    ((S3127FullEquivalence (l := l)).inverse.mapCocone
      (BinaryCofan.mk j u))

noncomputable def S3127G3HX
    {X Y : S3127FiniteEtaleOverKFull l}
    (j : (S3127FullForget (l := l)).obj X ⟶
      (S3127FullForget (l := l)).obj Y)
    (Z : FiniteEtaleCover (S1419AffineScheme l))
    (u : Z ⟶ (S3127FullForget (l := l)).obj Y)
    (hG : IsColimit (BinaryCofan.mk j u)) :
    IsColimit (S3127G3CX2 j Z u) :=
  (IsColimit.ofCoconeEquiv (S3127G3E X Z)).symm
    (isColimitOfPreserves (S3127FullEquivalence (l := l)).inverse hG)

@[simp] lemma S3127G3CX2_left
    {X Y : S3127FiniteEtaleOverKFull l}
    (j : (S3127FullForget (l := l)).obj X ⟶
      (S3127FullForget (l := l)).obj Y)
    (Z : FiniteEtaleCover (S1419AffineScheme l))
    (u : Z ⟶ (S3127FullForget (l := l)).obj Y) :
    (S3127G3CX2 j Z u).ι.app ⟨WalkingPair.left⟩ =
      (S3127G3eX (l := l) X).inv ≫
        (S3127FullEquivalence (l := l)).inverse.map j := by
  dsimp [S3127G3CX2, S3127G3E, S3127G3Alpha, S3127G3Beta,
    S3127G3DiagramIso2]
  rfl

@[simp] lemma S3127G3CX2_right
    {X Y : S3127FiniteEtaleOverKFull l}
    (j : (S3127FullForget (l := l)).obj X ⟶
      (S3127FullForget (l := l)).obj Y)
    (Z : FiniteEtaleCover (S1419AffineScheme l))
    (u : Z ⟶ (S3127FullForget (l := l)).obj Y) :
    (S3127G3CX2 j Z u).ι.app ⟨WalkingPair.right⟩ =
      (S3127FullEquivalence (l := l)).inverse.map u := by
  dsimp [S3127G3CX2, S3127G3E, S3127G3Alpha, S3127G3Beta,
    S3127G3DiagramIso2]
  rfl

lemma S3127G3map_eX_inv
    (X : S3127FiniteEtaleOverKFull l) :
    (S3127FullForget (l := l)).map (S3127G3eX (l := l) X).inv =
      (S3127FullEquivalence (l := l)).counitIso.inv.app
        ((S3127FullForget (l := l)).obj X) := by
  simp [S3127G3eX, Functor.preimageIso_inv]

lemma S3127G3map_eY_hom
    (Y : S3127FiniteEtaleOverKFull l) :
    (S3127FullForget (l := l)).map (S3127G3eY (l := l) Y).hom =
      (S3127FullEquivalence (l := l)).counitIso.hom.app
        ((S3127FullForget (l := l)).obj Y) := by
  simp [S3127G3eY, Functor.preimageIso_hom]

@[simp] lemma S3127G3map_comp_apply
    {X Y Z : S3127FiniteEtaleOverKFull l}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (S3127FullForget (l := l)).map (f ≫ g) =
      (S3127FullForget (l := l)).map f ≫
        (S3127FullForget (l := l)).map g :=
  (S3127FullForget (l := l)).map_comp f g

lemma S3127G3CX2_left_leg
    {X Y : S3127FiniteEtaleOverKFull l}
    (i : X ⟶ Y)
    (j : (S3127FullForget (l := l)).obj X ⟶
      (S3127FullForget (l := l)).obj Y)
    (hji : j = (S3127FullForget (l := l)).map i)
    (Z : FiniteEtaleCover (S1419AffineScheme l))
    (u : Z ⟶ (S3127FullForget (l := l)).obj Y) :
    (S3127G3CX2 j Z u).ι.app ⟨WalkingPair.left⟩ ≫
        (S3127G3eY (l := l) Y).hom = i := by
  apply (S3127FullForget_faithful (l := l)).map_injective
  rw [S3127G3CX2_left]
  let e := (S3127G3eX (l := l) X).inv ≫
    (S3127FullEquivalence (l := l)).inverse.map j
  have hsplitOuter :
      (S3127FullForget (l := l)).map (e ≫ (S3127G3eY (l := l) Y).hom) =
      (S3127FullForget (l := l)).map e ≫
        (S3127FullForget (l := l)).map (S3127G3eY (l := l) Y).hom :=
    S3127G3map_comp_apply _ _
  have hsplit :
      (S3127FullForget (l := l)).map e =
      (S3127FullForget (l := l)).map (S3127G3eX (l := l) X).inv ≫
        (S3127FullForget (l := l)).map
          ((S3127FullEquivalence (l := l)).inverse.map j) :=
    S3127G3map_comp_apply _ _
  change (S3127FullForget (l := l)).map
      (e ≫ (S3127G3eY (l := l) Y).hom) =
    (S3127FullForget (l := l)).map i
  rw [hsplitOuter, hsplit]
  rw [S3127G3map_eX_inv, S3127G3map_eY_hom]
  change (S3127FullEquivalence (l := l)).counitIso.inv.app
      ((S3127FullForget (l := l)).obj X) ≫
    ((S3127FullEquivalence (l := l)).inverse ⋙
      (S3127FullEquivalence (l := l)).functor).map j ≫
    (S3127FullEquivalence (l := l)).counitIso.hom.app
      ((S3127FullForget (l := l)).obj Y) =
    (S3127FullForget (l := l)).map i
  rw [S3127FullEquivalence.counitIso.hom.naturality j]
  rw [hji]
  simp only [Functor.id_map]
  change (S3127FullEquivalence (l := l)).counitIso.inv.app
      ((S3127FullForget (l := l)).obj X) ≫
    (S3127FullEquivalence (l := l)).counitIso.hom.app
      ((S3127FullForget (l := l)).obj X) ≫
    (S3127FullForget (l := l)).map i =
    (S3127FullForget (l := l)).map i
  have hcoe : (S3127FullEquivalence (l := l)).counitIso.inv.app
        ((S3127FullForget (l := l)).obj X) =
      ((S3127FullEquivalence (l := l)).counitIso.app
        ((S3127FullForget (l := l)).obj X)).inv := rfl
  have hcoh : (S3127FullEquivalence (l := l)).counitIso.hom.app
        ((S3127FullForget (l := l)).obj X) =
      ((S3127FullEquivalence (l := l)).counitIso.app
        ((S3127FullForget (l := l)).obj X)).hom := rfl
  rw [hcoe, hcoh]
  rw [Iso.inv_hom_id_assoc]

lemma S3127G3CX2_right_leg
    {X Y : S3127FiniteEtaleOverKFull l}
    (i : X ⟶ Y)
    (j : (S3127FullForget (l := l)).obj X ⟶
      (S3127FullForget (l := l)).obj Y)
    (Z : FiniteEtaleCover (S1419AffineScheme l))
    (u : Z ⟶ (S3127FullForget (l := l)).obj Y)
    (uZ : (S3127FullEquivalence (l := l)).inverse.obj Z ⟶ Y)
    (huZ : (S3127FullForget (l := l)).map uZ =
      (S3127FullEquivalence (l := l)).counitIso.hom.app Z ≫ u) :
    (S3127G3CX2 j Z u).ι.app ⟨WalkingPair.right⟩ ≫
        (S3127G3eY (l := l) Y).hom = uZ := by
  apply (S3127FullForget_faithful (l := l)).map_injective
  rw [S3127G3CX2_right]
  change (S3127FullForget (l := l)).map
      ((S3127FullEquivalence (l := l)).inverse.map u) ≫
    (S3127FullForget (l := l)).map (S3127G3eY (l := l) Y).hom =
    (S3127FullForget (l := l)).map uZ
  erw [S3127G3map_eY_hom]
  change ((S3127FullEquivalence (l := l)).inverse ⋙
      (S3127FullEquivalence (l := l)).functor).map u ≫
    (S3127FullEquivalence (l := l)).counitIso.hom.app
      ((S3127FullForget (l := l)).obj Y) =
    (S3127FullForget (l := l)).map uZ
  rw [S3127FullEquivalence.counitIso.hom.naturality u]
  simp only [Functor.id_map]
  exact huZ.symm

theorem S3127G3_full
    {X Y : S3127FiniteEtaleOverKFull l} (i : X ⟶ Y) [Mono i] :
    ∃ (Z : S3127FiniteEtaleOverKFull l) (u : Z ⟶ Y),
      Nonempty (IsColimit (BinaryCofan.mk i u)) := by
  let j := (S3127FullForget (l := l)).map i
  haveI : Mono j := S3127FullForget_map_mono i
  obtain ⟨Z, u, ⟨hG⟩⟩ :=
    finiteEtaleCover_monoInducesIsoOnDirectSummand j
  let G := (S3127FullEquivalence (l := l)).inverse
  obtain ⟨uZ, huZ⟩ :=
    (S3127FullForget_full (l := l)).map_surjective
      ((S3127FullEquivalence (l := l)).counitIso.hom.app Z ≫ u)
  refine ⟨G.obj Z, uZ, ⟨?_⟩⟩
  have hX := S3127G3HX j Z u hG
  let hc : S3127G3CX2 j Z u ≅ BinaryCofan.mk i uZ :=
    Cocone.ext (S3127G3eY (l := l) Y) (by
      intro k
      rcases k with ⟨(_ | _)⟩
      · exact S3127G3CX2_left_leg i j rfl Z u
      · exact S3127G3CX2_right_leg i j Z u uZ
          huZ)
  exact IsColimit.ofIsoColimit hX hc

#check S3127G3_full
#check S3127G3CX2_right_leg
#check S3127G3CX2_left_leg
#check S3127G3map_comp_apply
#check S3127G3map_eX_inv
#check S3127G3map_eY_hom
end LeanFormal.IUT.XiFPaper.S3127G3FullActual
end
