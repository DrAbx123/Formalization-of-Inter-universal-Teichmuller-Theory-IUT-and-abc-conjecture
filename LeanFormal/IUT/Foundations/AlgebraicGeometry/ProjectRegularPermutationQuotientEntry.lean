import LeanFormal.IUT.Foundations.AlgebraicGeometry.RegularPermutationQuotientEquivalence
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineFiniteEtaleQuotientConsumer
import Mathlib.Tactic

/-!
# Project entry for the regular permutation quotient

This module exposes the actual regular permutation quotient cover, its cocone
IsColimit, desc/fac/uniq, the chart-map factorization, and the affine finite-etale
quotient facts.  It consumes the green RegularPermutationQuotientEquivalence and
AffineFiniteEtaleQuotientConsumer modules.  No residual is introduced.
-/

noncomputable section

namespace LeanFormal.IUT.ProjectRegularPermutationQuotientEntry

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
open ABCBridge.RegularPermutationQuotientEquivalence
open ABCBridge.AffineFiniteEtaleQuotientConsumer

universe u

variable (R : Type u) [CommRing R] (G : Type u) [Group G] [Fintype G]

/-- The actual regular permutation quotient cover. -/
noncomputable def projectRegularPermutationQuotientCover :
    FiniteEtaleCover (Spec (CommRingCat.of R)) :=
  (regularQuotientCocone (R := R) (G := G)).pt

/-- The regular permutation quotient cocone. -/
noncomputable def projectRegularPermutationQuotientCocone :
    Cocone (RegularPermutationCoconeUniqueness.actionFunctor R G) :=
  regularQuotientCocone (R := R) (G := G)

/-- The actual colimit property of the regular permutation quotient cocone. -/
noncomputable def projectRegularPermutationQuotientCocone_isColimit :
    IsColimit (projectRegularPermutationQuotientCocone R G) :=
  regularQuotientCocone_isColimit (R := R) (G := G)

/-- The desc map of an arbitrary cocone. -/
noncomputable def projectRegularPermutationQuotientDesc
    (c : Cocone (RegularPermutationCoconeUniqueness.actionFunctor R G)) :
    (projectRegularPermutationQuotientCocone R G).pt ⟶ c.pt :=
  regularQuotientCocone_desc (R := R) (G := G) c

/-- The desc map factors every cocone component. -/
theorem projectRegularPermutationQuotientDesc_fac
    (c : Cocone (RegularPermutationCoconeUniqueness.actionFunctor R G))
    (j : SingleObj G) :
    (projectRegularPermutationQuotientCocone R G).ι.app j ≫
        projectRegularPermutationQuotientDesc R G c =
      c.ι.app j :=
  regularQuotientCocone_desc_fac (R := R) (G := G) c j

/-- The desc map is unique. -/
theorem projectRegularPermutationQuotientDesc_uniq
    (c : Cocone (RegularPermutationCoconeUniqueness.actionFunctor R G))
    (m : (projectRegularPermutationQuotientCocone R G).pt ⟶ c.pt)
    (hm : ∀ j : SingleObj G,
      (projectRegularPermutationQuotientCocone R G).ι.app j ≫ m = c.ι.app j) :
    m = projectRegularPermutationQuotientDesc R G c :=
  regularQuotientCocone_desc_uniq (R := R) (G := G) c m hm

/-- The actual quotient chart map. -/
noncomputable def projectRegularPermutationChartMap :
    AffineLocalQuotientGluingConstruct.regularPermutationCover R G ⟶
      projectRegularPermutationQuotientCover R G :=
  AffineLocalQuotientGluingConstruct.regularPermutationChartMap R G

/-- The chart map is the star component of the quotient cocone. -/
theorem projectRegularPermutationChartMap_eq_cocone_ι :
    projectRegularPermutationChartMap R G =
      (projectRegularPermutationQuotientCocone R G).ι.app (SingleObj.star G) :=
  rfl

/-- The chart map factors through the desc map of every cocone. -/
theorem projectRegularPermutationChartMap_desc_fac
    (c : Cocone (RegularPermutationCoconeUniqueness.actionFunctor R G)) :
    projectRegularPermutationChartMap R G ≫
        projectRegularPermutationQuotientDesc R G c =
      c.ι.app (SingleObj.star G) :=
  regularQuotientChartMap_desc_fac (R := R) (G := G) c

/-- The finite-etale quotient facts in the regular free action case. -/
theorem projectRegularAffineFiniteEtaleQuotient_finiteEtale :
    Algebra.Etale R (FixedPoints.subalgebra R (G → R) G) ∧
      Module.Finite R (FixedPoints.subalgebra R (G → R) G) :=
  ABCBridge.FiniteEtaleQuotientFreeAction.regularPermutationFixedPoints_finiteEtale
    (R := R) (G := G)

/-- Complete Project-facing package: quotient cover, IsColimit, desc/fac/uniq,
chart factorization, and affine finite-etale quotient facts. -/
theorem projectRegularPermutationQuotient_complete
    (c : Cocone (RegularPermutationCoconeUniqueness.actionFunctor R G)) :
    (projectRegularPermutationChartMap R G ≫
        projectRegularPermutationQuotientDesc R G c =
      c.ι.app (SingleObj.star G)) ∧
      (∀ j : SingleObj G,
        (projectRegularPermutationQuotientCocone R G).ι.app j ≫
            projectRegularPermutationQuotientDesc R G c = c.ι.app j) ∧
      (Algebra.Etale R (FixedPoints.subalgebra R (G → R) G) ∧
        Module.Finite R (FixedPoints.subalgebra R (G → R) G)) :=
  ⟨projectRegularPermutationChartMap_desc_fac R G c,
    projectRegularPermutationQuotientDesc_fac R G c,
    projectRegularAffineFiniteEtaleQuotient_finiteEtale R G⟩

end LeanFormal.IUT.ProjectRegularPermutationQuotientEntry