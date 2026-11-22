import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientProviderResidual
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

/-!
# Global quotient: action cocone compatibility

Compatibility of action cocone data under quotient isomorphisms.  These are
post-compile-delta drafts, held for the next batch; no colimit is asserted.
-/

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientCoconeCompat

universe u

open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientActionCocone
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientCoconeNaturality
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

variable {S : Scheme.{u}} {G : Type u} [Group G] [Finite G]
  {F : SingleObj G ⥤ FiniteEtaleCover S}

/-- Reindex the quotient of action cocone data along an isomorphism. -/
noncomputable def GlobalActionCoconeData.reindex
    (D : GlobalActionCoconeData S G F) (Q' : FiniteEtaleCover S)
    (e : D.quotient ≅ Q') : GlobalActionCoconeData S G F :=
  D.postcomp Q' e.hom

namespace GlobalActionCoconeData

variable (D : GlobalActionCoconeData S G F)

theorem reindex_proj (Q' : FiniteEtaleCover S) (e : D.quotient ≅ Q') :
    (D.reindex Q' e).proj = D.proj ≫ e.hom :=
  rfl

theorem reindex_invariant (Q' : FiniteEtaleCover S) (e : D.quotient ≅ Q')
    (g : G) :
    F.map g ≫ (D.reindex Q' e).proj = (D.reindex Q' e).proj :=
  (D.reindex Q' e).proj_invariant g

theorem reindex_cocone_ι (Q' : FiniteEtaleCover S) (e : D.quotient ≅ Q') :
    (D.reindex Q' e).cocone.ι.app (SingleObj.star G) = D.proj ≫ e.hom :=
  rfl

theorem reindex_cocone_naturality (Q' : FiniteEtaleCover S) (e : D.quotient ≅ Q')
    (g : G) :
    F.map g ≫ (D.reindex Q' e).cocone.ι.app (SingleObj.star G) =
      (D.reindex Q' e).cocone.ι.app (SingleObj.star G) :=
  (D.reindex Q' e).proj_invariant g

theorem postcomp_comp (Q' Q'' : FiniteEtaleCover S)
    (g : D.quotient ⟶ Q') (h : Q' ⟶ Q'') :
    (D.postcomp Q' g).postcomp Q'' h = D.postcomp Q'' (g ≫ h) :=
  rfl

end GlobalActionCoconeData

/-- The action cocone data is stable under quotient isomorphisms: the reindexed
data has the same cocone after transporting the projection. -/
theorem reindex_cocone_proj_eq {D : GlobalActionCoconeData S G F}
    {Q' : FiniteEtaleCover S} (e : D.quotient ≅ Q') :
    (D.reindex Q' e).cocone.ι.app (SingleObj.star G) = D.proj ≫ e.hom :=
  rfl

end LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientCoconeCompat
end