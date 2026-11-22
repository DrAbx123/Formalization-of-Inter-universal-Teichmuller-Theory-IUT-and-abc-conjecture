import tmp.sheaf.xif.paper.S1755TwoYonedaSmallnessActual
import tmp.sheaf.xif.paper.S1800IdentityAtlasSmallnessActual
import tmp.sheaf.xif.paper.S1756QuotientActual

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
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1756QuotientActual
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1757LiftFunctorialityActual

variable {A B : S1728Cover}

/-- The cone morphism induced by a 2-isomorphism of cover maps. -/
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

/-- The induced 1-cell between the lifts. -/
noncomputable def S1757LiftHom {f g : S1728CoverMap A B}
    (e : f.map ≅ g.map) :
    S1755Lift A B f ⟶ S1755Lift A B g :=
  (S1755BaseChange B).isPullback.liftTwoCell (S1755ModelStack A)
    (S1755Cone A B f) (S1755Cone A B g) (S1757ConeMorphism e)

/-- Exact missing functoriality: a 2-isomorphism of cover maps induces an
isomorphism of the extracted lifts. -/
def S1757LiftFunctoriality : Prop :=
  forall (A B : S1728Cover) (f g : S1728CoverMap A B),
    Nonempty (f.map ≅ g.map) ->
      Nonempty (S1755Lift A B f ≅ S1755Lift A B g)

/-- Functoriality gives well-definedness of the quotient extraction. -/
theorem S1756LiftWellDefined_of_functoriality
    (h : S1757LiftFunctoriality) : S1756LiftWellDefined := by
  intro A B f g hr
  obtain ⟨e⟩ := h A B f g hr
  exact S1742HomOfStrongTrans_congr e

#print axioms S1756LiftWellDefined_of_functoriality

end LeanFormal.IUT.XiFPaper.S1757LiftFunctorialityActual
end
