import tmp.sheaf.xif.paper.S1755TwoYonedaSmallnessActual
import tmp.sheaf.xif.paper.S1800IdentityAtlasSmallnessActual

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
open LeanFormal.IUT.XiFPaper.S1800IdentityAtlasSmallnessActual
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1757LiftFunctorialityProbe

variable {A B : S1728Cover}

noncomputable def S1757ConeMorphism {f g : S1728CoverMap A B}
    (e : f.map ≅ g.map) :
    (S1755Square B).ConeMorphism (S1755Cone A B f) (S1755Cone A B g) where
  toX := by
    change Pseudofunctor.StrongTrans.vcomp (S1755BaseChange A).toSource f.map ⟶
      Pseudofunctor.StrongTrans.vcomp (S1755BaseChange A).toSource g.map
    exact Pseudofunctor.StrongTrans.whiskerLeft (S1755BaseChange A).toSource e.hom
  toY := 𝟙 ((S1755BaseChange A).projectionMap.transformation)
  compatibility := by
    haveI : Subsingleton
        (Pseudofunctor.StrongTrans.vcomp (S1755Cone A B f).toX (S1755Square B).xToBase ⟶
          Pseudofunctor.StrongTrans.vcomp (S1755Cone A B g).toY (S1755Square B).yToBase) := by
      apply S1800Modification_subsingleton
    exact Subsingleton.elim _ _

#print axioms S1757ConeMorphism

end LeanFormal.IUT.XiFPaper.S1757LiftFunctorialityProbe
end
