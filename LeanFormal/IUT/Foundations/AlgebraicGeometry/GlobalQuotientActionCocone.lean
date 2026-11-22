import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientUniq
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

/-!
# Global quotient: action cocone data

This file isolates the exact input needed to build the action-diagram cocone
for the global quotient cover: a finite etale cover with a finite-group action,
a quotient cover, an invariant projection, and the gluing universal property.

Only the cocone construction is actual here.  The colimit proof is a separate
explicit field/residual; no provider inhabitant is manufactured.
-/

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientActionCocone

universe u

open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientDesc
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientFac
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientUniq
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

variable {S : Scheme.{u}}

/-- Input data for the cocone of a finite-group action diagram on a finite etale
cover, with an explicitly chosen quotient cover and invariant projection. -/
structure GlobalActionCoconeData (S : Scheme.{u}) (G : Type u) [Group G]
    [Finite G] (F : SingleObj G ⥤ FiniteEtaleCover S) where
  /-- The quotient cover. -/
  quotient : FiniteEtaleCover S
  /-- The projection from the acted cover to the quotient. -/
  proj : F.obj (SingleObj.star G) ⟶ quotient
  /-- The projection is invariant under the action. -/
  proj_invariant : ∀ g : G, F.map g ≫ proj = proj

namespace GlobalActionCoconeData

variable {G : Type u} [Group G] [Finite G]
variable {F : SingleObj G ⥤ FiniteEtaleCover S}

/-- The actual cocone associated to the invariant projection. -/
noncomputable def cocone (D : GlobalActionCoconeData S G F) : Cocone F :=
  Cocone.mk D.quotient
    (NatTrans.mk (fun _ => D.proj) (by
      intro X Y f
      cases X; cases Y
      exact D.proj_invariant f))

/-- The cocone projection on the unique object is the chosen projection. -/
theorem cocone_ι (D : GlobalActionCoconeData S G F) :
    D.cocone.ι.app (SingleObj.star G) = D.proj :=
  rfl

/-- Naturality of the cocone, stated explicitly on the action maps. -/
theorem cocone_naturality (D : GlobalActionCoconeData S G F) (g : G) :
    F.map g ≫ D.cocone.ι.app (SingleObj.star G) =
      D.cocone.ι.app (SingleObj.star G) :=
  D.proj_invariant g

end GlobalActionCoconeData

/-- The exact per-diagram colimit obligation for the action cocone. -/
structure GlobalActionColimitData {G : Type u} [Group G] [Finite G]
    {F : SingleObj G ⥤ FiniteEtaleCover S}
    (D : GlobalActionCoconeData S G F) where
  /-- The actual colimit proof for the action diagram. -/
  isColimit : IsColimit D.cocone

/-- Exact global residual in action-cocone form: every finite-group action
diagram has a quotient cocone data and a colimit proof.  This is a Prop, not an
inhabited provider. -/
def GlobalActionCoconeResidual (S : Scheme.{u}) : Prop :=
  ∀ (G : Type u) [Group G] [Finite G],
    ∀ F : SingleObj G ⥤ FiniteEtaleCover S,
      ∃ D : GlobalActionCoconeData S G F, Nonempty (GlobalActionColimitData D)

end LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientActionCocone
end