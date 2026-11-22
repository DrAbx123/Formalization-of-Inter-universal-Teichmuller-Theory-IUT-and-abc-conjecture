import tmp.sheaf.xif.paper.S1757LiftFunctorialityActual
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
open LeanFormal.IUT.XiFPaper.S1757LiftFunctorialityActual
open LeanFormal.IUT.XiFPaper.S1800IdentityAtlasSmallnessActual
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1761SubsingletonIsoProbe

variable {A B : S1728Cover}

noncomputable def S1761LiftIso {f g : S1728CoverMap A B}
    (e : f.map ≅ g.map) : S1755Lift A B f ≅ S1755Lift A B g where
  hom := S1757LiftHom e
  inv := S1757LiftHom e.symm
  hom_inv_id := by
    haveI : Subsingleton (S1755Lift A B f ⟶ S1755Lift A B f) := by
      apply S1800Modification_subsingleton
    exact Subsingleton.elim _ _
  inv_hom_id := by
    haveI : Subsingleton (S1755Lift A B g ⟶ S1755Lift A B g) := by
      apply S1800Modification_subsingleton
    exact Subsingleton.elim _ _

#print axioms S1761LiftIso

end LeanFormal.IUT.XiFPaper.S1761SubsingletonIsoProbe
end
