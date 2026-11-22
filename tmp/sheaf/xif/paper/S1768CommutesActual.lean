import tmp.sheaf.xif.paper.S1767OverToQuotConditionalActual

noncomputable section
open CategoryTheory CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1755TwoYonedaSmallnessActual
open LeanFormal.IUT.XiFPaper.S1756QuotientActual
open LeanFormal.IUT.XiFPaper.S1767OverToQuotConditionalActual
open LeanFormal.IUT.XiFPaper.S1762OverModelHomActual
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S1768CommutesActual

variable {W X Y Z : EtaleStackPseudofunctor S1726K}

noncomputable def S1768assocV (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    Iso (Pseudofunctor.StrongTrans.vcomp
          (Pseudofunctor.StrongTrans.vcomp f g) h)
        (Pseudofunctor.StrongTrans.vcomp f
          (Pseudofunctor.StrongTrans.vcomp g h)) := by
  change Iso ((f ≫ g) ≫ h) (f ≫ (g ≫ h))
  exact Bicategory.associator f g h

noncomputable def S1768whiskerRightV {f g : W ⟶ X}
    (e : f ≅ g) (h : X ⟶ Y) :
    Iso (Pseudofunctor.StrongTrans.vcomp f h)
        (Pseudofunctor.StrongTrans.vcomp g h) := by
  change Iso (f ≫ h) (g ≫ h)
  exact Bicategory.whiskerRightIso e h

noncomputable def S1768whiskerLeftV (h : W ⟶ X) {f g : X ⟶ Y}
    (e : f ≅ g) :
    Iso (Pseudofunctor.StrongTrans.vcomp h f)
        (Pseudofunctor.StrongTrans.vcomp h g) := by
  change Iso (h ≫ f) (h ≫ g)
  exact Bicategory.whiskerLeftIso h e

noncomputable def S1768leftUnitorV (f : W ⟶ X) :
    Iso (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.id W) f) f := by
  change Iso (𝟙 W ≫ f) f
  exact Bicategory.leftUnitor f

variable {A B : S1728Cover}

noncomputable def S1768Commutes (g : S1762ModelHomOver A B) :
    S1767CommutesData g where
  commutes :=
    let s := S1755ModelSectionLift A
    let G := S1742StrongTransOfHom (F := S1726K) g.hom
    let t := (S1755BaseChange B).toSource
    let Bm := B.map
    let tA := (S1755BaseChange A).toSource
    let Am := A.map
    let base := S1733BasePoint
    let projB := (S1755BaseChange B).projectionMap.transformation
    let projA := (S1755BaseChange A).projectionMap.transformation
    let e1 := S1768assocV s (Pseudofunctor.StrongTrans.vcomp G t) Bm
    let e2 := S1768whiskerLeftV s (S1768assocV G t Bm)
    let e3 := S1768whiskerLeftV s
      (S1768whiskerLeftV G (S1755BaseChange B).commutes)
    let e4 := S1768whiskerLeftV s (S1768assocV G projB base).symm
    let e5 := S1768whiskerLeftV s
      (S1768whiskerRightV (Classical.choice g.overBase) base)
    let e6 := S1768whiskerLeftV s (S1755BaseChange A).commutes.symm
    let e7 := (S1768assocV s tA Am).symm
    let e8 := S1768whiskerRightV (S1755ModelSection A) Am
    let e9 := S1768leftUnitorV Am
    e1 ≪≫ e2 ≪≫ e3 ≪≫ e4 ≪≫ e5 ≪≫ e6 ≪≫ e7 ≪≫ e8 ≪≫ e9

#print axioms S1768Commutes

/-- Actual inverse direction. -/
noncomputable def S1768OverToQuot (g : S1762ModelHomOver A B) :
    S1756CoverMapQuot A B :=
  S1767OverToQuotOfCommutes g (S1768Commutes g)

#print axioms S1768Commutes
#print axioms S1768OverToQuot

end LeanFormal.IUT.XiFPaper.S1768CommutesActual
end
