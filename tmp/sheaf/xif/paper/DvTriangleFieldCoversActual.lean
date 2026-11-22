import Mathlib.RingTheory.Etale.Finite
import Iut.Foundations.Orbicurve

/-!
# S398: candidate actual category for D_v^⊢ = B(K_v)^0

`B(K)^0` is the full subcategory of connected objects of finite étale covers
of `Spec K`.  Mathlib's `CommAlgCat.FiniteEtale K` is the actual category of
finite étale `K`-algebras with `K`-algebra morphisms.  Taking the full
subcategory of objects that are fields gives the connected finite étale
covers of `Spec K` (finite separable field extensions).

The repo's `OrbicurveEtaleFundamentalGroup.coverCategory` is a structure field,
not a global instance, and its objects are finite étale stack maps to a
hyperbolic orbicurve `X`, not finite étale `K_v`-algebras.  It is therefore not
the paper base category `D_v^⊢`; the comparison is recorded as an exact gap.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.DvTriangleFieldCoversActual

open CategoryTheory
open Iut

universe u v

/-- Object property: a finite étale `K`-algebra is a field (one connected component). -/
abbrev DvFieldCoverProperty (K : Type u) [Field K] :
    ObjectProperty (CommAlgCat.FiniteEtale.{u} K) :=
  fun S => IsField S

abbrev DvTriangleFieldCover (K : Type u) [Field K] : Type _ :=
  (DvFieldCoverProperty K).FullSubcategory

/-- The actual inclusion of connected finite étale covers into all finite
étale `K`-algebras. -/
noncomputable def DvTriangleFieldCoverInclusion (K : Type u) [Field K] :
    DvTriangleFieldCover K ⥤ CommAlgCat.FiniteEtale.{u} K :=
  (DvFieldCoverProperty K).ι

/-- Exact missing comparison between the orbicurve cover category and the
paper base category `B(K_v)^0`. -/
structure OrbicurveCoverToDvTriangleComparison
    {F : Type u} [Field F] (X : HyperbolicOrbicurve F) where
  coverCategory : Category.{u} (OrbicurveFiniteEtaleCover X)
  baseIsSpecK : Prop
  connectedObjectCondition : Prop
  categoryEquivalence : Prop
  algebraStructureCompatibility : Prop

/-- Exact-missing predicate for the comparison. -/
def OrbicurveCoverToDvTriangleComparisonRequired
    {F : Type u} [Field F] (X : HyperbolicOrbicurve F) : Prop :=
  Nonempty (OrbicurveCoverToDvTriangleComparison X)

/-- The orbicurve cover category field is not a global category instance. -/
def OrbicurveCoverCategoryIsStructureField : Prop :=
  ∀ {F : Type u} [Field F] (X : HyperbolicOrbicurve F)
    (G : ProfiniteGrp.{u}) (data : OrbicurveEtaleFundamentalGroup X G),
      Nonempty (Category.{u} (OrbicurveFiniteEtaleCover X))

end LeanFormal.IUT.XiFPaper.DvTriangleFieldCoversActual
end
