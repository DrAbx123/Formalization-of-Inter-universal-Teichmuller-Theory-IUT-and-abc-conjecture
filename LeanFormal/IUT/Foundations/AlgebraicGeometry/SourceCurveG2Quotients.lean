import LeanFormal.IUT.IUTII.Frobenioid.Example36CurveScheme
import LeanFormal.IUT.IUTII.Frobenioid.Example36CurveGaloisCategory

/-!
# Scheme-level G2 candidate for the actual source curve

This file identifies the actual source curve scheme definitionally with the
spectrum of the Weierstrass coordinate ring and instantiates the scheme-level
G2 statement for it, conditional on the affine-base finite-etale quotient
theorem.  It is a scheme-level donor only; the source orbicurve G2 (nonabelian
punctured-curve pi1, cusp inertia, orbicurve structure) is a separate gap and is
not asserted here.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceCurveG2Quotients

open LeanFormal.IUT.IUTII.Frobenioid.Example36

universe u

/-- The actual source curve scheme is definitionally the spectrum of the
Weierstrass coordinate ring. -/
theorem curveScheme_eq_spec_coordinateRing (K : Type u) [Field K] :
    curveScheme K = Spec (CommRingCat.of (curveCoordinateRing K)) :=
  rfl

/-- The source curve scheme is affine. -/
theorem sourceCurveScheme_isAffine (K : Type u) [Field K] :
    IsAffine (curveScheme K) :=
  curveScheme_isAffine K

/-- Scheme-level G2 for the actual source curve, conditional on the affine-base
HasColimits theorem for the Weierstrass coordinate ring. -/
theorem sourceCurveG2_of_affineBaseG2 (K : Type u) [Field K]
    (h : ∀ (G : Type u) [Group G] [Finite G],
      HasColimitsOfShape (SingleObj G)
        (FiniteEtaleCover (Spec (CommRingCat.of (curveCoordinateRing K))))) :
    ∀ (G : Type u) [Group G] [Finite G],
      HasColimitsOfShape (SingleObj G) (FiniteEtaleCover (curveScheme K)) := by
  intro G _ _
  change HasColimitsOfShape (SingleObj G)
    (FiniteEtaleCover (Spec (CommRingCat.of (curveCoordinateRing K))))
  exact h G

/-- The once-punctured source is definitionally the same affine curve scheme. -/
theorem oncePuncturedScheme_eq_curveScheme (K : Type u) [Field K] :
    curveOncePuncturedScheme K = curveScheme K :=
  rfl

/-- Scheme-level G2 for the once-punctured source, conditional on the same
affine-base HasColimits theorem. -/
theorem oncePuncturedG2_of_affineBaseG2 (K : Type u) [Field K]
    (h : ∀ (G : Type u) [Group G] [Finite G],
      HasColimitsOfShape (SingleObj G)
        (FiniteEtaleCover (Spec (CommRingCat.of (curveCoordinateRing K))))) :
    ∀ (G : Type u) [Group G] [Finite G],
      HasColimitsOfShape (SingleObj G)
        (FiniteEtaleCover (curveOncePuncturedScheme K)) := by
  simpa [oncePuncturedScheme_eq_curveScheme K] using sourceCurveG2_of_affineBaseG2 K h

/-- The actual consumer: the scheme-level curve PreGaloisCategory remaining G2
field, conditional on the affine-base HasColimits theorem. -/
def sourceCurvePreGaloisRemainingFields_of_affineBaseG2 (K : Type u) [Field K]
    (h : ∀ (G : Type u) [Group G] [Finite G],
      HasColimitsOfShape (SingleObj G)
        (FiniteEtaleCover (Spec (CommRingCat.of (curveCoordinateRing K))))) :
    CurvePreGaloisCategoryRemainingFields (curveScheme K) where
  hasQuotientsByFiniteGroups := sourceCurveG2_of_affineBaseG2 K h

/-- The once-punctured version of the same consumer. -/
def oncePuncturedPreGaloisRemainingFields_of_affineBaseG2 (K : Type u) [Field K]
    (h : ∀ (G : Type u) [Group G] [Finite G],
      HasColimitsOfShape (SingleObj G)
        (FiniteEtaleCover (Spec (CommRingCat.of (curveCoordinateRing K))))) :
    CurvePreGaloisCategoryRemainingFields (curveOncePuncturedScheme K) where
  hasQuotientsByFiniteGroups := oncePuncturedG2_of_affineBaseG2 K h

end LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceCurveG2Quotients
end
