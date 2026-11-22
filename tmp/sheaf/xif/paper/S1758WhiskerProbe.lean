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

namespace LeanFormal.IUT.XiFPaper.S1758WhiskerProbe

variable {A B : S1728Cover}

theorem S1758LiftHom_whisker_toX {f g : S1728CoverMap A B}
    (e : f.map ≅ g.map) :
    CategoryTheory.Bicategory.whiskerRight (a := S1755ModelStack A) (b := S1755ModelStack B) (c := S1755Source B)
      (S1757LiftHom e ≫ S1757LiftHom e.symm :
        S1755Lift A B f ⟶ S1755Lift A B f)
      (S1755BaseChange B).toSource =
    CategoryTheory.Bicategory.whiskerRight (a := S1755ModelStack A) (b := S1755ModelStack B) (c := S1755Source B)
      (𝟙 (S1755Lift A B f) : S1755Lift A B f ⟶ S1755Lift A B f)
        (S1755BaseChange B).toSource := by
  rw [CategoryTheory.Bicategory.comp_whiskerRight]
  simp only [S1757LiftHom]
  rw [(S1755BaseChange B).isPullback.liftTwoCell_toX,
      (S1755BaseChange B).isPullback.liftTwoCell_toX]
  rw [CategoryTheory.Bicategory.id_whiskerRight (S1755Lift A B f) (S1755BaseChange B).toSource]
  simp only [S1757ConeMorphism, S1755Cone, CategoryTheory.Bicategory.whiskerLeft_comp,
    CategoryTheory.Bicategory.whiskerLeft_id, Iso.inv_hom_id, Iso.hom_inv_id,
    Category.assoc, Category.comp_id, Category.id_comp]

#print axioms S1758LiftHom_whisker_toX

end LeanFormal.IUT.XiFPaper.S1758WhiskerProbe
end
