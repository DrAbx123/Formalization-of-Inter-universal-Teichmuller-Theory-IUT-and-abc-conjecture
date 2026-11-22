import LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleQuotientFreeAction
import LeanFormal.IUT.Foundations.AlgebraicGeometry.RegularPermutationCoconeUniqueness
import Mathlib.Tactic

/-!
# Universal property of the regular permutation quotient cover

This module consumes the actual regular quotient cover and chart map from
FiniteEtaleQuotientFreeAction and the production colimit theorem
RegularPermutationCoconeUniqueness.regularPermutationCocone_isColimit.  It exposes
the desc/fac/uniq consumer for every cocone and the quotient chart factorization.
No residual and no new provider chain.
-/

noncomputable section

namespace ABCBridge.RegularPermutationQuotientEquivalence

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineLocalQuotientGluingConstruct

universe u

variable (R : Type u) [CommRing R] (G : Type u) [Group G] [Fintype G]

/-- The actual regular permutation quotient cocone. -/
noncomputable def regularQuotientCocone :
    Cocone (RegularPermutationCoconeUniqueness.actionFunctor R G) :=
  AffineLocalQuotientGluingConstruct.regularPermutationCocone R G

/-- The point of the regular quotient cocone is the actual quotient cover. -/
theorem regularQuotientCocone_pt :
    (regularQuotientCocone (R := R) (G := G)).pt =
      RegularPermutationCoconeUniqueness.quotientCover R G :=
  rfl

/-- The actual colimit property of the regular permutation quotient cocone. -/
noncomputable def regularQuotientCocone_isColimit :
    IsColimit (regularQuotientCocone (R := R) (G := G)) :=
  RegularPermutationCoconeUniqueness.regularPermutationCocone_isColimit R G

/-- The desc map of an arbitrary cocone. -/
noncomputable def regularQuotientCocone_desc
    (c : Cocone (RegularPermutationCoconeUniqueness.actionFunctor R G)) :
    (regularQuotientCocone (R := R) (G := G)).pt ⟶ c.pt :=
  (regularQuotientCocone_isColimit (R := R) (G := G)).desc c

/-- The desc map factors every cocone component. -/
theorem regularQuotientCocone_desc_fac
    (c : Cocone (RegularPermutationCoconeUniqueness.actionFunctor R G))
    (j : SingleObj G) :
    (regularQuotientCocone (R := R) (G := G)).ι.app j ≫ regularQuotientCocone_desc (R := R) (G := G) c =
      c.ι.app j :=
  (regularQuotientCocone_isColimit (R := R) (G := G)).fac c j

/-- The desc map is unique among maps factoring every cocone component. -/
theorem regularQuotientCocone_desc_uniq
    (c : Cocone (RegularPermutationCoconeUniqueness.actionFunctor R G))
    (m : (regularQuotientCocone (R := R) (G := G)).pt ⟶ c.pt)
    (hm : ∀ j : SingleObj G,
      (regularQuotientCocone (R := R) (G := G)).ι.app j ≫ m = c.ι.app j) :
    m = regularQuotientCocone_desc (R := R) (G := G) c :=
  (regularQuotientCocone_isColimit (R := R) (G := G)).uniq c m hm

/-- The actual chart map is the star component of the quotient cocone. -/
theorem regularQuotientChartMap_eq_cocone_ι :
    AffineLocalQuotientGluingConstruct.regularPermutationChartMap R G =
      (regularQuotientCocone (R := R) (G := G)).ι.app (SingleObj.star G) :=
  rfl

/-- The quotient chart map factors through the desc map of every cocone. -/
theorem regularQuotientChartMap_desc_fac
    (c : Cocone (RegularPermutationCoconeUniqueness.actionFunctor R G)) :
    AffineLocalQuotientGluingConstruct.regularPermutationChartMap R G ≫
        regularQuotientCocone_desc (R := R) (G := G) c =
      c.ι.app (SingleObj.star G) := by
  rw [regularQuotientChartMap_eq_cocone_ι]
  exact regularQuotientCocone_desc_fac (R := R) (G := G) c (SingleObj.star G)

/-- Every cocone is uniquely determined by the quotient chart map.  This is the
consumer form of the IsColimit property. -/
theorem regularQuotientCocone_desc_unique_of_chart
    (c : Cocone (RegularPermutationCoconeUniqueness.actionFunctor R G))
    (m : (regularQuotientCocone (R := R) (G := G)).pt ⟶ c.pt)
    (hm : AffineLocalQuotientGluingConstruct.regularPermutationChartMap R G ≫ m =
      c.ι.app (SingleObj.star G)) :
    m = regularQuotientCocone_desc (R := R) (G := G) c := by
  apply regularQuotientCocone_desc_uniq (R := R) (G := G) c m
  intro j
  have hj : j = SingleObj.star G := Subsingleton.elim j _
  rw [hj, ← regularQuotientChartMap_eq_cocone_ι]
  exact hm

/-- Complete universal-property package: desc, fac, uniq, chart factorization and
the actual quotient cover. -/
theorem regularQuotientCocone_complete
    (c : Cocone (RegularPermutationCoconeUniqueness.actionFunctor R G))
    (m : (regularQuotientCocone (R := R) (G := G)).pt ⟶ c.pt)
    (hm : AffineLocalQuotientGluingConstruct.regularPermutationChartMap R G ≫ m =
      c.ι.app (SingleObj.star G)) :
    (AffineLocalQuotientGluingConstruct.regularPermutationChartMap R G ≫
        regularQuotientCocone_desc (R := R) (G := G) c =
      c.ι.app (SingleObj.star G)) ∧
      (m = regularQuotientCocone_desc (R := R) (G := G) c) :=
  ⟨regularQuotientChartMap_desc_fac (R := R) (G := G) c,
    regularQuotientCocone_desc_unique_of_chart (R := R) (G := G) c m hm⟩

end ABCBridge.RegularPermutationQuotientEquivalence