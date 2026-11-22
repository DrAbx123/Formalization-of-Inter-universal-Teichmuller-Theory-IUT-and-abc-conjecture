import tmp.sheaf.xif.paper.S1641CoverMapCompositionActual
import tmp.sheaf.xif.paper.S1726OrbicurveFPrimeActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace Probe12

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

abbrev CoverMapClass (A B : OrbicurveFiniteEtaleCover X) : Type (u + 1) :=
  Quot (fun f g : OrbicurveFiniteEtaleCoverMap A B => CoverMapRel f g)

lemma coverMapRel_comp_right {A B C : OrbicurveFiniteEtaleCover X}
    (f : OrbicurveFiniteEtaleCoverMap A B)
    {g g' : OrbicurveFiniteEtaleCoverMap B C}
    (hg : CoverMapRel g g') :
    CoverMapRel (S1641CoverMapComp f g) (S1641CoverMapComp f g') := by
  rcases hg with ⟨eg⟩
  refine ⟨?iso⟩
  simpa only [S1641CoverMapComp_map] using TestWhiskerLeft f g g' eg

lemma coverMapRel_comp_left {A B C : OrbicurveFiniteEtaleCover X}
    {f f' : OrbicurveFiniteEtaleCoverMap A B}
    (g : OrbicurveFiniteEtaleCoverMap B C)
    (hf : CoverMapRel f f') :
    CoverMapRel (S1641CoverMapComp f g) (S1641CoverMapComp f' g) := by
  rcases hf with ⟨ef⟩
  refine ⟨?iso⟩
  simpa only [S1641CoverMapComp_map] using TestWhiskerRight f f' g ef

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

example {A B : OrbicurveFiniteEtaleCover X}
    (f : CoverMapClass (A := A) (B := B)) :
    CoverMapClassComp (CoverMapClassId A) f = f := by
  induction f using Quot.inductionOn with
  | h f =>
      apply Quot.sound
      refine ⟨?iso⟩
      simpa only [CoverMapClassComp, CoverMapClassId, S1641CoverMapComp_map,
        S1641CoverMapId_map, Quot.map₂_mk] using TestLeftUnitor f

example {A B : OrbicurveFiniteEtaleCover X}
    (f : CoverMapClass (A := A) (B := B)) :
    CoverMapClassComp f (CoverMapClassId B) = f := by
  induction f using Quot.inductionOn with
  | h f =>
      apply Quot.sound
      refine ⟨?iso⟩
      simpa only [CoverMapClassComp, CoverMapClassId, S1641CoverMapComp_map,
        S1641CoverMapId_map, Quot.map₂_mk] using TestRightUnitor f

example {A B C D : OrbicurveFiniteEtaleCover X}
    (f : CoverMapClass (A := A) (B := B))
    (g : CoverMapClass (A := B) (B := C))
    (h : CoverMapClass (A := C) (B := D)) :
    CoverMapClassComp (CoverMapClassComp f g) h =
      CoverMapClassComp f (CoverMapClassComp g h) := by
  induction f using Quot.inductionOn with
  | h f =>
    induction g using Quot.inductionOn with
    | h g =>
      induction h using Quot.inductionOn with
      | h h =>
        apply Quot.sound
        refine ⟨?iso⟩
        simpa only [CoverMapClassComp, S1641CoverMapComp_map, Quot.map₂_mk] using
          TestAssoc f g h

end Probe12
