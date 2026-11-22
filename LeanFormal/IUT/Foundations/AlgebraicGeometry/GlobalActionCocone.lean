import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalFiniteEtaleQuotient
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineLocalQuotientGluingConstruct
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Limits.Cones
import Mathlib.Tactic

/-!
# Global action cocone for the affine-chart quotient candidate

Conditional on global glued quotient data and a finite group action by cover
automorphisms, this file records the action diagram and the quotient cocone.
The cocone exists only from the explicit invariant projection supplied by the
data; no colimit claim is made here.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option maxRecDepth 10000

noncomputable section

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalActionCocone

universe u

open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalFiniteEtaleQuotient
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

variable {R : Type u} [CommRing R]

/-- Global action data: a glued quotient candidate, an identification of the
cover with the glued scheme, and a group action by cover automorphisms whose
projection to the candidate is invariant. -/
structure GlobalActionData
    (X : FiniteEtaleCover (Spec (CommRingCat.of R))) (G : Type u) [Group G] where
  D : GlobalGluedQuotientData (Spec (CommRingCat.of R))
  chartIso : X.carrier ≅ D.P.toSchemeGlueData.glued
  overTriangle : chartIso.hom ≫ FiniteEtaleCover.structureMap D.cover =
    FiniteEtaleCover.structureMap X
  action : G →* CategoryTheory.Aut X
  projection_invariant : ∀ g : G,
    (action g).hom ≫
      (AffineLocalQuotientGluingConstruct.finiteEtaleCoverHomMk
        (X := X) (Y := D.cover) chartIso.hom overTriangle) =
    AffineLocalQuotientGluingConstruct.finiteEtaleCoverHomMk
      (X := X) (Y := D.cover) chartIso.hom overTriangle

namespace GlobalActionData

open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineLocalQuotientGluingConstruct

variable {X : FiniteEtaleCover (Spec (CommRingCat.of R))} {G : Type u} [Group G]
  (A : GlobalActionData (R := R) X G)

/-- The projection from the cover to the glued quotient candidate. -/
def projection : X ⟶ A.D.cover :=
  AffineLocalQuotientGluingConstruct.finiteEtaleCoverHomMk (X := X) (Y := A.D.cover) A.chartIso.hom A.overTriangle

/-- The action functor on the one-object group category. -/
def actionFunctor : SingleObj G ⥤ FiniteEtaleCover (Spec (CommRingCat.of R)) where
  obj _ := X
  map g := (A.action g).hom
  map_id := by
    intro j
    change (A.action 1).hom = 𝟙 X
    rw [map_one]
    rfl
  map_comp := by
    intro U V W f g
    rw [SingleObj.comp_as_mul]
    change (A.action (g * f)).hom = (A.action f).hom ≫ (A.action g).hom
    rw [map_mul]
    simp [Aut.Aut_mul_def, Iso.trans_hom]

/-- The quotient cocone, conditional on the invariant projection. -/
def cocone : Cocone A.actionFunctor where
  pt := A.D.cover
  ι :=
    { app := fun _ => A.projection
      naturality := by
        intro j j' f
        change (A.action f).hom ≫ A.projection = A.projection ≫ 𝟙 A.D.cover
        rw [Category.comp_id]
        exact A.projection_invariant f }

end GlobalActionData

end LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalActionCocone

end