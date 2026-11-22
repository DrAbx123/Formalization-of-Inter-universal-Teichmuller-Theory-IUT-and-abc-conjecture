import Iut.Foundations.Orbicurve
import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S405OrbicurveCoverCategoryActual

open CategoryTheory
open Iut
universe u

variable {F : Type u} [Field F]
variable (X : HyperbolicOrbicurve F)

namespace OrbicurveFiniteEtaleCover

/-- Actual identity map on a cover, using the left unitor of StrongTrans. -/
noncomputable def idMap (A : OrbicurveFiniteEtaleCover X) :
    OrbicurveFiniteEtaleCoverMap A A where
  map := Pseudofunctor.StrongTrans.id A.source.fiber
  commutes := by
    letI := EtaleStackPseudofunctor.homCategory (F := F) A.source.fiber X.stack.fiber
    exact Pseudofunctor.StrongTrans.leftUnitor A.map

end OrbicurveFiniteEtaleCover

/-- Exact missing composition/coherence data for the cover category.

The Hom type is OrbicurveFiniteEtaleCoverMap, and id is actual (leftUnitor).
For a composite f : A -> B and g : B -> C, the map is StrongTrans.vcomp
f.map g.map, but its commutes field requires whiskering/composition of the
Iso fields and then strict id_comp/comp_id/assoc equalities.  The
pseudofunctor StrongTrans bicategory supplies associator/unitors only as
isomorphisms, not as the strict equalities needed for Category.  Hence the
Category instance is recorded as exact missing, not fabricated. -/
structure OrbicurveCoverCategoryGap where
  categoryStruct : CategoryStruct (OrbicurveFiniteEtaleCover X)
  id_comp : Prop
  comp_id : Prop
  assoc : Prop

def OrbicurveCoverCategoryRequired : Prop :=
  Nonempty (OrbicurveCoverCategoryGap (F := F) X)

end LeanFormal.IUT.XiFPaper.S405OrbicurveCoverCategoryActual

end
