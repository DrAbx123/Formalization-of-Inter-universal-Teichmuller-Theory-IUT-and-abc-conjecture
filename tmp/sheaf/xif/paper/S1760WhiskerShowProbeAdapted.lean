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

namespace LeanFormal.IUT.XiFPaper.S1760WhiskerShowProbeAdapted

variable {A B : S1728Cover}

theorem S1760Whisker {f g : S1728CoverMap A B} (e : f.map ≅ g.map) :
    (CategoryTheory.Bicategory.whiskerRight
      (S1757LiftHom e) (S1755Square B).toX :
      (S1755Lift A B f ≫ (S1755Square B).toX) ⟶
      (S1755Lift A B g ≫ (S1755Square B).toX)) ≫
    (CategoryTheory.Bicategory.whiskerRight
      (S1757LiftHom e.symm) (S1755Square B).toX) =
    (CategoryTheory.Bicategory.whiskerRight
      (𝟙 (S1755Lift A B f) : S1755Lift A B f ⟶ S1755Lift A B f)
        (S1755Square B).toX :
      (S1755Lift A B f ≫ (S1755Square B).toX) ⟶
      (S1755Lift A B f ≫ (S1755Square B).toX)) := by
  rw [CategoryTheory.Bicategory.comp_whiskerRight]
  show (CategoryTheory.Bicategory.whiskerRight
      (S1757LiftHom e) (S1755Square B).toX :
      (S1755Lift A B f ≫ (S1755Square B).toX) ⟶
      (S1755Lift A B g ≫ (S1755Square B).toX)) ≫
    (CategoryTheory.Bicategory.whiskerRight
      (S1757LiftHom e.symm) (S1755Square B).toX) =
    (CategoryTheory.Bicategory.whiskerRight
      (𝟙 (S1755Lift A B f)) (S1755Square B).toX)
  simp only [S1757LiftHom, (S1755BaseChange B).isPullback.liftTwoCell_toX]

#print axioms S1760Whisker

end LeanFormal.IUT.XiFPaper.S1760WhiskerShowProbeAdapted
end
