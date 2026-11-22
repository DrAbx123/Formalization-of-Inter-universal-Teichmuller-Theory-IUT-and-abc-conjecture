import tmp.sheaf.xif.paper.S1641CoverMapCompositionActual
import tmp.sheaf.xif.paper.S1726OrbicurveFPrimeActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace Probe11

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

end Probe11
