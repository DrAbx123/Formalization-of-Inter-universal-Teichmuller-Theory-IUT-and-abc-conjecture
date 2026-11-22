import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineChartFamilyFromCover
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

/-!
# Affine chart family: induced action on restrictions

This file constructs the actual induced finite-group action on the restriction
of a global finite etale cover to an affine open.  The action is obtained by
applying the production restriction functor to cover automorphisms.

Post-compile-delta draft; held for watchdog compilation.  No provider/IsColimit.
-/

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineChartFamilyAction

universe u

open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineChartFamilyFromCover
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

variable {S : Scheme.{u}}

/-- The restriction functor on finite etale covers. -/
noncomputable abbrev restrictionFunctor (U : S.Opens)
    [Limits.HasPullbacksAlong (U.ι)] :
    FiniteEtaleCover S ⥤ FiniteEtaleCover U :=
  FiniteEtaleCover.pullback (U.ι)

/-- The actual induced action endomorphism of the restriction of a global
cover to an affine open. -/
noncomputable def restrictCoverActionEnd (X : FiniteEtaleCover S) (U : S.Opens)
    [Limits.HasPullbacksAlong (U.ι)] (g : CategoryTheory.Aut X) :
    CategoryTheory.Aut (restrictCover X U) :=
  (restrictionFunctor (S := S) U).mapIso g

/-- The induced action is a group homomorphism from the cover automorphism
group to the automorphism group of the restriction. -/
noncomputable def restrictCoverActionMonoidHom (X : FiniteEtaleCover S) (U : S.Opens)
    [Limits.HasPullbacksAlong (U.ι)] :
    CategoryTheory.Aut X →* CategoryTheory.Aut (restrictCover X U) where
  toFun := restrictCoverActionEnd (S := S) X U
  map_one' := by
    dsimp [restrictCoverActionEnd]
    rw [Functor.mapIso_refl]
  map_mul' g h := by
    dsimp [restrictCoverActionEnd]
    rw [Functor.mapIso_trans]

/-- The same induced action, with the group action passed as a monoid hom from
the finite group. -/
noncomputable def restrictCoverActionOfGroup {G : Type u} [Group G]
    (X : FiniteEtaleCover S) (U : S.Opens)
    [Limits.HasPullbacksAlong (U.ι)] (act : G →* CategoryTheory.Aut X) :
    G →* CategoryTheory.Aut (restrictCover X U) :=
  act.trans (restrictCoverActionMonoidHom (S := S) X U)

/-- Affine chart restriction data with the actual induced action. -/
structure AffineChartRestrictedAction (S : Scheme.{u}) where
  /-- The global finite etale cover. -/
  X : FiniteEtaleCover S
  /-- The affine open. -/
  U : S.Opens
  /-- Affineness of the open. -/
  hU : IsAffine U
  /-- Pullbacks along the open immersion exist. -/
  hasPullback : Limits.HasPullbacksAlong (U.ι)
  /-- The group. -/
  G : Type u
  /-- Group structure. -/
  groupG : Group G
  /-- Finiteness of the group. -/
  finiteG : Finite G
  /-- The action on the global cover. -/
  act : letI := groupG; G →* CategoryTheory.Aut X

namespace AffineChartRestrictedAction

variable (D : AffineChartRestrictedAction S)

/-- The restricted cover of the chart. -/
noncomputable def restrictedCover : FiniteEtaleCover D.U :=
  letI := D.hasPullback
  restrictCover D.X D.U

/-- The induced action on the restricted cover. -/
noncomputable def inducedAction :
    letI := D.groupG; D.G →* CategoryTheory.Aut D.restrictedCover :=
  letI := D.groupG
  letI := D.hasPullback
  restrictCoverActionOfGroup (S := S) D.X D.U D.act

theorem restrictedCover_isAffine : IsAffine D.restrictedCover.carrier :=
  letI := D.hasPullback
  restrictCover_isAffine D.X D.U

end AffineChartRestrictedAction

/-- Exact action-to-quotient instantiation target: from an actual global cover
with finite action and an affine chart, construct the local quotient chart
together with the induced action on the restriction and the compatibility of
the quotient chart map.  This is a Prop, not an inhabited structure. -/
def AffineChartActionToQuotientConstruction (S : Scheme.{u}) : Prop :=
  ∀ (_D : AffineChartRestrictedAction S),
    ∃ Q : AffineChartLocalQuotient S,
      Q.U = _D.U ∧ Q.XU = _D.restrictedCover

end LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineChartFamilyAction
end