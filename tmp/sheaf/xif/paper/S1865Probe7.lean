import tmp.sheaf.xif.paper.S1865CoprodApexActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1865CoprodApexActual

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S1854CoherentCategoryActual
open LeanFormal.IUT.XiFPaper.S1857CoherentLimits01Actual
open LeanFormal.IUT.XiFPaper.S1878CoherentAffineBridgeActual

theorem S1865HasInitial_of_hasFiniteCoproducts
    {C : Type*} [Category C] [HasFiniteCoproducts C] : HasInitial C := by
  let F : Discrete (Fin 0) ⥤ C := functorOfIsEmpty _ _
  haveI : HasColimit F := (HasFiniteCoproducts.out 0).has_colimit F
  have hinit : IsInitial (colimit F) :=
    (isColimitEquivIsInitialOfIsEmpty (C := C) (J := Discrete (Fin 0)) (F := F)
      (colimit.cocone F)).toFun (colimit.isColimit F)
  exact IsInitial.hasInitial hinit

theorem S1865CoherentHasInitial (h : S1878Full ∧ S1878EssSurj) :
    @HasInitial S1878CoherentCategory inferInstance := by
  letI := S1865CoherentHasFiniteCoproducts h
  exact S1865HasInitial_of_hasFiniteCoproducts

noncomputable def S1865CoherentInitialObj (h : S1878Full ∧ S1878EssSurj) :
    S1878CoherentCategory := by
  letI : HasInitial S1878CoherentCategory := S1865CoherentHasInitial h
  exact ⊥_ S1878CoherentCategory

noncomputable def S1865CoherentInitial_isInitial (h : S1878Full ∧ S1878EssSurj) :
    IsInitial (S1865CoherentInitialObj h) := by
  letI : HasInitial S1878CoherentCategory := S1865CoherentHasInitial h
  change IsInitial (⊥_ S1878CoherentCategory)
  exact initialIsInitial

noncomputable def S1865InitialObj_isInitial
    (h : S1878Full ∧ S1878EssSurj) (hE : S1865CoherentEssSurj) :
    IsInitial ((inducedFunctor (F := CoherentCover.cover)).obj
      (S1865CoherentInitialObj h)) := by
  let F := inducedFunctor (F := CoherentCover.cover)
  letI : F.EssSurj := ⟨fun A => hE A⟩
  letI : F.IsEquivalence :=
    { faithful := inferInstance, full := inferInstance, essSurj := inferInstance }
  have hI : IsInitial (S1865CoherentInitialObj h) := S1865CoherentInitial_isInitial h
  let toY : (Y : S1728Cover) → F.obj (S1865CoherentInitialObj h) ⟶ Y := fun Y =>
    let C : S1878CoherentCategory := Classical.choose (hE Y)
    let e : F.obj C ≅ Y := Classical.choice (Classical.choose_spec (hE Y))
    F.map (hI.to C) ≫ e.hom
  refine IsInitial.ofUniqueHom toY ?_
  intro Y m
  change m = toY Y
  let C : S1878CoherentCategory := Classical.choose (hE Y)
  let e : F.obj C ≅ Y := Classical.choice (Classical.choose_spec (hE Y))
  obtain ⟨m', hm'⟩ := F.map_surjective (m ≫ e.inv)
  have h1 : m' = hI.to C := hI.hom_ext _ _
  calc m = (m ≫ e.inv) ≫ e.hom := by simp
    _ = F.map m' ≫ e.hom := by rw [hm']
    _ = F.map (hI.to C) ≫ e.hom := by rw [h1]

noncomputable def S1865WeakInitial
    (h : S1878Full ∧ S1878EssSurj) (hE : S1865CoherentEssSurj) :
    HasInitial S1728Cover := by
  let F := inducedFunctor (F := CoherentCover.cover)
  let I : S1878CoherentCategory := S1865CoherentInitialObj h
  have hI : IsInitial (F.obj I) := S1865InitialObj_isInitial h hE
  haveI : ∀ Y : S1728Cover, Nonempty (F.obj I ⟶ Y) := fun Y => ⟨hI.to Y⟩
  haveI : ∀ Y : S1728Cover, Subsingleton (F.obj I ⟶ Y) :=
    fun Y => ⟨fun a b => hI.hom_ext a b⟩
  exact hasInitial_of_unique (F.obj I)

example
    (h : S1878Full ∧ S1878EssSurj) (hE : S1865CoherentEssSurj) :
    letI := S1865WeakInitial h hE
    (⊥_ S1728Cover) = (inducedFunctor (F := CoherentCover.cover)).obj
      (S1865CoherentInitialObj h) := rfl

noncomputable def S1865InitialApex
    (h : S1878Full ∧ S1878EssSurj) (hE : S1865CoherentEssSurj) :
    letI := S1865WeakInitial h hE
    Nonempty { P : CoherentCover // P.cover = (⊥_ S1728Cover) } := by
  letI := S1865WeakInitial h hE
  let I : CoherentCover := S1865CoherentInitialObj h
  refine ⟨I, ?_⟩
  change I.cover = (inducedFunctor (F := CoherentCover.cover)).obj
    (S1865CoherentInitialObj h)
  rfl

end LeanFormal.IUT.XiFPaper.S1865CoprodApexActual
