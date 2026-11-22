import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientActionCocone
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

/-!
# Global quotient: cocone naturality

This file records naturality and postcomposition facts for the conditional
action cocone of the global quotient.  No colimit is asserted; only the
cocone transformations are constructed from explicit data.
-/

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientCoconeNaturality

universe u

open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientActionCocone
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

variable {S : Scheme.{u}} {G : Type u} [Group G] [Finite G]
  {F : SingleObj G ⥤ FiniteEtaleCover S}

/-- Postcompose the quotient and projection of action cocone data by a cover
morphism.  This is the naturality of the cocone construction in the target. -/
noncomputable def GlobalActionCoconeData.postcomp
    (D : GlobalActionCoconeData S G F) (Q' : FiniteEtaleCover S)
    (g : D.quotient ⟶ Q') : GlobalActionCoconeData S G F where
  quotient := Q'
  proj := D.proj ≫ g
  proj_invariant := by
    intro a
    rw [← Category.assoc, D.proj_invariant]

namespace GlobalActionCoconeData

variable (D : GlobalActionCoconeData S G F)

theorem postcomp_proj (Q' : FiniteEtaleCover S) (g : D.quotient ⟶ Q') :
    (D.postcomp Q' g).proj = D.proj ≫ g :=
  rfl

theorem postcomp_ι (Q' : FiniteEtaleCover S) (g : D.quotient ⟶ Q') :
    (D.postcomp Q' g).cocone.ι.app (SingleObj.star G) = D.proj ≫ g :=
  rfl

theorem cocone_ι_naturality (a : G) :
    F.map a ≫ D.cocone.ι.app (SingleObj.star G) =
      D.cocone.ι.app (SingleObj.star G) :=
  D.proj_invariant a

theorem cocone_ι_naturality_assoc (a : G) (Z : Scheme.{u})
    (h : D.quotient.carrier ⟶ Z) :
    F.map a ≫ D.cocone.ι.app (SingleObj.star G) ≫ h =
      D.cocone.ι.app (SingleObj.star G) ≫ h := by
  rw [D.cocone_ι_naturality]

end GlobalActionCoconeData

/-- A morphism between action cocone data over the same diagram, with the
same quotient and projection, has the same underlying cocone. -/
theorem cocone_congr_of_proj {D E : GlobalActionCoconeData S G F}
    (h : D.proj = E.proj) :
    D.cocone.ι.app (SingleObj.star G) = E.cocone.ι.app (SingleObj.star G) :=
  h

/-- Naturality of the cocone under a group element, in the explicit form used by
the IsColimit consumer. -/
theorem cocone_naturality_explicit (D : GlobalActionCoconeData S G F) (a : G) :
    F.map a ≫ D.cocone.ι.app (SingleObj.star G) =
      D.cocone.ι.app (SingleObj.star G) :=
  D.proj_invariant a


end LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientCoconeNaturality
end