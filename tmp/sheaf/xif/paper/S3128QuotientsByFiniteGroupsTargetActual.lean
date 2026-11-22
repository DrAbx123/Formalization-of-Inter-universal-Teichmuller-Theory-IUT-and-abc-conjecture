import tmp.sheaf.xif.paper.S3128RelPullbackConeActual
import Mathlib.CategoryTheory.Galois.Basic

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.RepresentableCoverChosenCategoryActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.S3128QuotientsByFiniteGroupsTargetActual

variable {l : PrimeGeFive}

/-- The exact remaining PreGalois condition: the chosen cover category has
colimits of shape SingleObj G for every finite group G. -/
def S3128HasQuotientsByFiniteGroupsTarget (l : PrimeGeFive) : Prop :=
  forall (G : Type) [Group G] [Finite G],
    HasColimitsOfShape (SingleObj G) (S3127Cover (l := l))

/-- Unfolding lemma for the quotient target. -/
theorem S3128HasQuotientsByFiniteGroupsTarget_iff (l : PrimeGeFive) :
    S3128HasQuotientsByFiniteGroupsTarget l ↔
      forall (G : Type) [Group G] [Finite G],
        HasColimitsOfShape (SingleObj G) (S3127Cover (l := l)) :=
  Iff.rfl

/-- The direct-summand target. -/
def S3128MonoInducesIsoOnDirectSummandTarget (l : PrimeGeFive) : Prop :=
  forall {X Y : S3127Cover (l := l)} (i : X ⟶ Y), Mono i ->
    ∃ (Z : S3127Cover (l := l)) (u : Z ⟶ Y),
      Nonempty (IsColimit (BinaryCofan.mk i u))

/-- Unfolding lemma for the direct-summand target. -/
theorem S3128MonoInducesIsoOnDirectSummandTarget_iff (l : PrimeGeFive) :
    S3128MonoInducesIsoOnDirectSummandTarget l ↔
      forall {X Y : S3127Cover (l := l)} (i : X ⟶ Y), Mono i ->
        ∃ (Z : S3127Cover (l := l)) (u : Z ⟶ Y),
          Nonempty (IsColimit (BinaryCofan.mk i u)) :=
  Iff.rfl

#check S3128HasQuotientsByFiniteGroupsTarget
#check S3128MonoInducesIsoOnDirectSummandTarget

end LeanFormal.IUT.XiFPaper.S3128QuotientsByFiniteGroupsTargetActual
end