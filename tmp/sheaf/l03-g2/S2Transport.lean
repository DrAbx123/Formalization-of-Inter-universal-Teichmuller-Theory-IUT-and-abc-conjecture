import Iut.Foundations.Orbicurve
import LeanFormal.IUT.IUTII.Frobenioid.Example36EtaleCoverFoundations
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Stage 2/3: transport of finite-group colimits to orbicurve covers

This file states and proves the S2 transport target from
tmp/sheaf/l03-g2/STAGE1-source-scope.md.

If E : FiniteEtaleCover S.left ⥤ OrbicurveFiniteEtaleCover X is an equivalence
of categories, then every finite-group action colimit property on the scheme
side transports to the orbicurve cover category along E.inv.

No production file is modified.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option maxRecDepth 10000

noncomputable section

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.S2Transport

open Iut

universe u

open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

variable {F : Type u} [Field F]
variable {X : HyperbolicOrbicurve F}
variable {S : SchemeOverField F}

/-- The scheme-side finite-group action colimit property used by the source
transport.  This is the GlobalQuotientCoconeResidual specialized to S.left. -/
def SchemeSideHasFiniteGroupQuotients : Prop :=
  ∀ (G : Type u) [Group G] [Finite G],
    HasColimitsOfShape (SingleObj G) (FiniteEtaleCover S.left)

/-- S2 transport: an equivalence of cover categories transports the scheme-side
finite-group colimit property to the orbicurve cover category. -/
theorem hasColimitsOfShape_orbicurve_of_equivalence
    [Category.{u} (OrbicurveFiniteEtaleCover X)]
    (E : FiniteEtaleCover S.left ⥤ OrbicurveFiniteEtaleCover X)
    [E.IsEquivalence]
    (hS : SchemeSideHasFiniteGroupQuotients (S := S)) :
    ∀ (G : Type u) [Group G] [Finite G],
      HasColimitsOfShape (SingleObj G) (OrbicurveFiniteEtaleCover X) := by
  intro G _ _
  letI : HasColimitsOfShape (SingleObj G) (FiniteEtaleCover S.left) :=
    hS G
  exact Adjunction.hasColimitsOfShape_of_equivalence (E := E.inv)

/-- The same transport stated directly from the explicit scheme-side hypothesis. -/
theorem hasColimitsOfShape_orbicurve_of_scheme
    [Category.{u} (OrbicurveFiniteEtaleCover X)]
    (E : FiniteEtaleCover S.left ⥤ OrbicurveFiniteEtaleCover X)
    [E.IsEquivalence]
    (hS : ∀ (G : Type u) [Group G] [Finite G],
      HasColimitsOfShape (SingleObj G) (FiniteEtaleCover S.left)) :
    ∀ (G : Type u) [Group G] [Finite G],
      HasColimitsOfShape (SingleObj G) (OrbicurveFiniteEtaleCover X) :=
  hasColimitsOfShape_orbicurve_of_equivalence (X := X) (S := S) E hS

/-- A version taking the scheme-side residual Prop directly. -/
theorem hasColimitsOfShape_orbicurve_of_residual
    [Category.{u} (OrbicurveFiniteEtaleCover X)]
    (E : FiniteEtaleCover S.left ⥤ OrbicurveFiniteEtaleCover X)
    [E.IsEquivalence]
    (hres : ∀ (G : Type u) [Group G] [Finite G],
      HasColimitsOfShape (SingleObj G) (FiniteEtaleCover S.left)) :
    ∀ (G : Type u) [Group G] [Finite G],
      HasColimitsOfShape (SingleObj G) (OrbicurveFiniteEtaleCover X) :=
  hasColimitsOfShape_orbicurve_of_scheme (X := X) (S := S) E hres

end LeanFormal.IUT.Foundations.AlgebraicGeometry.S2Transport
