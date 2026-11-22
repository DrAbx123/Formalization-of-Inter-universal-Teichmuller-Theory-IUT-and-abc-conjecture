import tmp.sheaf.xif.paper.S1641CoverMapCompositionActual
import tmp.sheaf.xif.paper.S1726OrbicurveFPrimeActual
import Mathlib.Data.Quot
import Mathlib.Logic.Equiv.Defs

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace ProbeIntegration

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S1641CoverMapCompositionActual

universe u

variable {F : Type u} [Field F]
variable {X : HyperbolicOrbicurve F}

noncomputable def TestWhiskerLeft {A B C : OrbicurveFiniteEtaleCover X}
    (f : OrbicurveFiniteEtaleCoverMap A B)
    (g g' : OrbicurveFiniteEtaleCoverMap B C)
    (eg : g.map ≅ g'.map) :
    Iso
      (Pseudofunctor.StrongTrans.vcomp f.map g.map)
      (Pseudofunctor.StrongTrans.vcomp f.map g'.map) := by
  let Bicat := EtaleStackPseudofunctor F
  letI : Bicategory Bicat := inferInstance
  let source : Bicat := A.source.fiber
  let mid : Bicat := B.source.fiber
  let target : Bicat := C.source.fiber
  let fmap : source ⟶ mid := f.map
  let gmap : mid ⟶ target := g.map
  let gmap' : mid ⟶ target := g'.map
  exact @Bicategory.whiskerLeftIso Bicat _ source mid target fmap gmap gmap' eg

noncomputable def TestWhiskerRight {A B C : OrbicurveFiniteEtaleCover X}
    (f f' : OrbicurveFiniteEtaleCoverMap A B)
    (g : OrbicurveFiniteEtaleCoverMap B C)
    (ef : f.map ≅ f'.map) :
    Iso
      (Pseudofunctor.StrongTrans.vcomp f.map g.map)
      (Pseudofunctor.StrongTrans.vcomp f'.map g.map) := by
  let Bicat := EtaleStackPseudofunctor F
  letI : Bicategory Bicat := inferInstance
  let source : Bicat := A.source.fiber
  let mid : Bicat := B.source.fiber
  let target : Bicat := C.source.fiber
  let fmap : source ⟶ mid := f.map
  let fmap' : source ⟶ mid := f'.map
  let gmap : mid ⟶ target := g.map
  exact @Bicategory.whiskerRightIso Bicat _ source mid target fmap fmap' ef gmap

noncomputable def TestAssoc {A B C D : OrbicurveFiniteEtaleCover X}
    (f : OrbicurveFiniteEtaleCoverMap A B)
    (g : OrbicurveFiniteEtaleCoverMap B C)
    (h : OrbicurveFiniteEtaleCoverMap C D) :
    Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp f.map g.map) h.map)
      (Pseudofunctor.StrongTrans.vcomp
        f.map (Pseudofunctor.StrongTrans.vcomp g.map h.map)) := by
  let Bicat := EtaleStackPseudofunctor F
  letI : Bicategory Bicat := inferInstance
  let source : Bicat := A.source.fiber
  let mid1 : Bicat := B.source.fiber
  let mid2 : Bicat := C.source.fiber
  let target : Bicat := D.source.fiber
  let fmap : source ⟶ mid1 := f.map
  let gmap : mid1 ⟶ mid2 := g.map
  let hmap : mid2 ⟶ target := h.map
  exact @Bicategory.associator Bicat _ source mid1 mid2 target fmap gmap hmap

noncomputable def TestLeftUnitor {A B : OrbicurveFiniteEtaleCover X}
    (f : OrbicurveFiniteEtaleCoverMap A B) :
    Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.id A.source.fiber) f.map)
      f.map := by
  let Bicat := EtaleStackPseudofunctor F
  letI : Bicategory Bicat := inferInstance
  let source : Bicat := A.source.fiber
  let target : Bicat := B.source.fiber
  let fmap : source ⟶ target := f.map
  exact @Bicategory.leftUnitor Bicat _ source target fmap

noncomputable def TestRightUnitor {A B : OrbicurveFiniteEtaleCover X}
    (f : OrbicurveFiniteEtaleCoverMap A B) :
    Iso
      (Pseudofunctor.StrongTrans.vcomp
        f.map (Pseudofunctor.StrongTrans.id B.source.fiber))
      f.map := by
  let Bicat := EtaleStackPseudofunctor F
  letI : Bicategory Bicat := inferInstance
  let source : Bicat := A.source.fiber
  let target : Bicat := B.source.fiber
  let fmap : source ⟶ target := f.map
  exact @Bicategory.rightUnitor Bicat _ source target fmap

def CoverMapRel {A B : OrbicurveFiniteEtaleCover X}
    (f g : OrbicurveFiniteEtaleCoverMap A B) : Prop :=
  Nonempty (f.map ≅ g.map)

lemma coverMapRel_refl {A B : OrbicurveFiniteEtaleCover X}
    (f : OrbicurveFiniteEtaleCoverMap A B) : CoverMapRel f f :=
  ⟨Iso.refl f.map⟩

lemma coverMapRel_symm {A B : OrbicurveFiniteEtaleCover X}
    {f g : OrbicurveFiniteEtaleCoverMap A B}
    (h : CoverMapRel f g) : CoverMapRel g f := by
  rcases h with ⟨e⟩
  exact ⟨e.symm⟩

lemma coverMapRel_trans {A B : OrbicurveFiniteEtaleCover X}
    {f g h : OrbicurveFiniteEtaleCoverMap A B}
    (hfg : CoverMapRel f g) (hgh : CoverMapRel g h) : CoverMapRel f h := by
  rcases hfg with ⟨e₁⟩
  rcases hgh with ⟨e₂⟩
  exact ⟨e₁.trans e₂⟩

lemma coverMapRel_equivalence (A B : OrbicurveFiniteEtaleCover X) :
    Equivalence (CoverMapRel (A := A) (B := B)) :=
  ⟨coverMapRel_refl, coverMapRel_symm, coverMapRel_trans⟩

abbrev CoverMapClass (A B : OrbicurveFiniteEtaleCover X) : Type (u + 1) :=
  Quot (fun f g : OrbicurveFiniteEtaleCoverMap A B => CoverMapRel f g)

lemma coverMapRel_comp_right {A B C : OrbicurveFiniteEtaleCover X}
    (f : OrbicurveFiniteEtaleCoverMap A B)
    {g g' : OrbicurveFiniteEtaleCoverMap B C}
    (hg : CoverMapRel g g') :
    CoverMapRel (S1641CoverMapComp f g) (S1641CoverMapComp f g') := by
  rcases hg with ⟨eg⟩
  exact ⟨by simpa only [S1641CoverMapComp_map] using TestWhiskerLeft f g g' eg⟩

lemma coverMapRel_comp_left {A B C : OrbicurveFiniteEtaleCover X}
    {f f' : OrbicurveFiniteEtaleCoverMap A B}
    (g : OrbicurveFiniteEtaleCoverMap B C)
    (hf : CoverMapRel f f') :
    CoverMapRel (S1641CoverMapComp f g) (S1641CoverMapComp f' g) := by
  rcases hf with ⟨ef⟩
  exact ⟨by simpa only [S1641CoverMapComp_map] using TestWhiskerRight f f' g ef⟩

noncomputable def CoverMapClassComp {A B C : OrbicurveFiniteEtaleCover X}
    (f : CoverMapClass (A := A) (B := B)) (g : CoverMapClass (A := B) (B := C)) :
    CoverMapClass (A := A) (B := C) :=
  Quot.map₂ (fun f g => S1641CoverMapComp f g)
    (fun _ _ _ hg => coverMapRel_comp_right _ hg)
    (fun _ _ _ hf => coverMapRel_comp_left _ hf) f g

noncomputable def CoverMapClassId (A : OrbicurveFiniteEtaleCover X) :
    CoverMapClass (A := A) (B := A) :=
  Quot.mk _ (S1641CoverMapId A)

@[reducible] noncomputable def CoverCategoryStruct11 :
    CategoryStruct (OrbicurveFiniteEtaleCover X) where
  Hom := CoverMapClass
  id := CoverMapClassId
  comp := CoverMapClassComp

noncomputable instance CoverCategory11 :
    Category.{u + 1, u + 1} (OrbicurveFiniteEtaleCover X) where
  toCategoryStruct := CoverCategoryStruct11
  id_comp := by
    intro A B f
    induction f using Quot.inductionOn with
    | h f =>
        apply Quot.sound
        exact ⟨by
          simpa only [CoverCategoryStruct11, CoverMapClassComp, CoverMapClassId,
            S1641CoverMapComp_map, S1641CoverMapId_map, Quot.map₂_mk] using
            TestLeftUnitor f⟩
  comp_id := by
    intro A B f
    induction f using Quot.inductionOn with
    | h f =>
        apply Quot.sound
        exact ⟨by
          simpa only [CoverCategoryStruct11, CoverMapClassComp, CoverMapClassId,
            S1641CoverMapComp_map, S1641CoverMapId_map, Quot.map₂_mk] using
            TestRightUnitor f⟩
  assoc := by
    intro A B C D f g h
    induction f using Quot.inductionOn with
    | h f =>
      induction g using Quot.inductionOn with
      | h g =>
        induction h using Quot.inductionOn with
        | h h =>
          apply Quot.sound
          exact ⟨by
            simpa only [CoverCategoryStruct11, CoverMapClassComp,
              S1641CoverMapComp_map, Quot.map₂_mk] using TestAssoc f g h⟩

/-- General quotient equivalence: quotienting a small carrier by a relation
pulled back along an equivalence gives the same quotient. -/
def quotCongrEquiv {α : Type (u + 1)} {β : Type u}
    (r : α → α → Prop) (hr : Equivalence r) (e : β ≃ α) :
    Quot (fun (x y : β) => r (e x) (e y)) ≃ Quot r where
  toFun := Quot.lift (fun x => Quot.mk r (e x)) (fun x y h => Quot.sound h)
  invFun := Quot.lift (fun a => Quot.mk (fun (x y : β) => r (e x) (e y)) (e.symm a))
    (fun a b h => by
      apply Quot.sound
      simpa using h)
  left_inv q := by
    induction q using Quot.inductionOn with
    | h x =>
      apply Quot.sound
      simpa using hr.refl (e x)
  right_inv q := by
    induction q using Quot.inductionOn with
    | h a =>
      apply Quot.sound
      simpa using hr.refl a

/-- Transport a category structure along a family of equivalences of hom types. -/
noncomputable def CategoryOfHomEquiv
    (D : Type (u + 1)) [Category.{u + 1, u + 1} D]
    (H : D → D → Type u)
    (e : ∀ A B, H A B ≃ (A ⟶ B)) :
    Category.{u, u + 1} D where
  Hom := H
  id A := (e A A).symm (𝟙 A)
  comp {A B C} f g := (e A C).symm ((e A B f) ≫ (e B C g))
  id_comp {A B} f := by
    apply (e A B).injective
    simp only [Equiv.apply_symm_apply]
    exact Category.id_comp (f := e A B f)
  comp_id {A B} f := by
    apply (e A B).injective
    simp only [Equiv.apply_symm_apply]
    exact Category.comp_id (f := e A B f)
  assoc {A B C E} f g h := by
    apply (e A E).injective
    simp only [Equiv.apply_symm_apply]
    exact Category.assoc (f := e A B f) (g := e B C g) (h := e C E h)

/-- Small raw cover-map data: a Type 0 carrier for every actual cover-map
type, with an equivalence to the actual maps. -/
structure SmallRawCoverData (A B : OrbicurveFiniteEtaleCover X) where
  Carrier : Type u
  equiv : Carrier ≃ OrbicurveFiniteEtaleCoverMap A B

/-- From small raw cover-map data, the 2-isomorphism quotient is small and
carries the actual quotient category structure at the target universe. -/
noncomputable def CategoryOfSmallRawCoverData
    (H : (A B : OrbicurveFiniteEtaleCover X) → Type u)
    (e : ∀ A B, H A B ≃ OrbicurveFiniteEtaleCoverMap A B) :
    Category.{u, u + 1} (OrbicurveFiniteEtaleCover X) :=
  CategoryOfHomEquiv
    (D := OrbicurveFiniteEtaleCover X)
    (H := fun A B =>
      Quot (fun f g : H A B => CoverMapRel (e A B f) (e A B g)))
    (fun A B =>
      quotCongrEquiv (CoverMapRel (A := A) (B := B))
        (coverMapRel_equivalence A B) (e A B))

end ProbeIntegration
