import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalActionCocone
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.Algebra.Group.Units.Equiv

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleCoverActionFunctor

universe u

open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

variable {R : Type u} [CommRing R]
variable {G : Type u} [Group G]

abbrev CoverCat : Type (u + 1) := FiniteEtaleCover (Spec (CommRingCat.of R))

noncomputable def actionFunctorOfAction
    (X : CoverCat (R := R)) (act : G →* CategoryTheory.Aut X) :
    SingleObj G ⥤ CoverCat (R := R) :=
  SingleObj.functor ((CategoryTheory.Aut.toEnd X).comp act)

noncomputable def actionOfFunctor
    (F : SingleObj G ⥤ CoverCat (R := R)) :
    G →* CategoryTheory.Aut (F.obj (SingleObj.star G)) :=
  (F.mapAut (SingleObj.star G)).comp
    ((Units.toAut G).toMonoidHom.comp (toUnits (G := G)).toMonoidHom)


/-- Every functor from SingleObj G is the generic action functor of its extracted action. -/
theorem actionFunctorOfAction_actionOfFunctor
    (F : SingleObj G ⥤ CoverCat (R := R)) :
    actionFunctorOfAction (R := R) (F.obj (SingleObj.star G)) (actionOfFunctor F) = F := by
  rfl


end LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleCoverActionFunctor
