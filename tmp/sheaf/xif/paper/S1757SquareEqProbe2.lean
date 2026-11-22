import tmp.sheaf.xif.paper.S1757LiftFunctorialityActual

noncomputable section
open CategoryTheory CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1755TwoYonedaSmallnessActual
open LeanFormal.IUT.XiFPaper.S1757LiftFunctorialityActual
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1757SquareEqProbe2

variable {A B : S1728Cover}

theorem S1757Square_eq :
    S1755Square B =
      EtalePseudofunctorSquare.mk (S1755BaseChange B).toSource
        (S1755BaseChange B).projectionMap.transformation B.map S1733BasePoint
        (S1755BaseChange B).commutes := rfl

noncomputable def S1757Witness :
    (S1755Square B).TwoPullbackWitness :=
  S1757Square_eq ▸ (S1755BaseChange B).isPullback

noncomputable def S1757LiftHomW {f g : S1728CoverMap A B}
    (e : f.map ≅ g.map) : S1755Lift A B f ⟶ S1755Lift A B g :=
  (S1757Witness (B := B)).liftTwoCell (S1755ModelStack A)
    (S1755Cone A B f) (S1755Cone A B g) (S1757ConeMorphism e)

example {f g : S1728CoverMap A B} (e : f.map ≅ g.map) :
    S1757LiftHomW e = S1757LiftHom e := rfl

theorem S1757Whisker {f g : S1728CoverMap A B} (e : f.map ≅ g.map) :
    CategoryTheory.Bicategory.whiskerRight (a := S1755ModelStack A) (b := S1755ModelStack B) (c := S1755Source B)
      (S1757LiftHomW e ≫ S1757LiftHomW e.symm :
        S1755Lift A B f ⟶ S1755Lift A B f)
      (S1755BaseChange B).toSource =
    CategoryTheory.Bicategory.whiskerRight (a := S1755ModelStack A) (b := S1755ModelStack B) (c := S1755Source B)
      (𝟙 (S1755Lift A B f) : S1755Lift A B f ⟶ S1755Lift A B f)
        (S1755BaseChange B).toSource := by
  rw [CategoryTheory.Bicategory.comp_whiskerRight]
  simp only [S1757LiftHomW]
  rw [(S1757Witness (B := B)).liftTwoCell_toX,
    (S1757Witness (B := B)).liftTwoCell_toX]
  rw [CategoryTheory.Bicategory.id_whiskerRight (S1755Lift A B f) (S1755BaseChange B).toSource]
  simp only [S1757Witness, S1757ConeMorphism, S1757Square_eq,
    CategoryTheory.Bicategory.whiskerLeft_comp,
    CategoryTheory.Bicategory.whiskerLeft_id, Iso.inv_hom_id, Iso.hom_inv_id,
    Category.assoc, Category.comp_id, Category.id_comp]

#print axioms S1757Whisker

end LeanFormal.IUT.XiFPaper.S1757SquareEqProbe2
end
