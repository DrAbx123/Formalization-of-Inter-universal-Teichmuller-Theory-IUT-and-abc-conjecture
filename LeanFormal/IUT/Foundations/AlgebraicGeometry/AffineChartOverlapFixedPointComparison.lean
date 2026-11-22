import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineChartOverlapRefinement
import LeanFormal.IUT.Foundations.AlgebraicGeometry.TensorEqualizerFixedPoints

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

/-!
# Affine chart overlap fixed-point comparison

This file attacks the fixed-point comparison residual for the two tensor
presentations of the overlap algebra.  The tensor base-change equivalences are
actual (`cancelBaseChange`); the exact remaining input is that they send fixed
points to fixed points.  No refinement is assumed.

Post-compile-delta draft; held for watchdog compilation. No provider/IsColimit.
-/

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineChartOverlapFixedPointComparison

universe u

open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineChartOverlapLocalizationCompatibility
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineChartOverlapRefinement
open LeanFormal.IUT.Foundations.AlgebraicGeometry.TensorEqualizerFixedPoints
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

variable {R A G : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [Group G] [Fintype G] [DecidableEq G]
  [MulSemiringAction G A] [SMulCommClass G R A]
  [Algebra.Etale R A] [Module.Finite R A]

/-- The f-chart tensor presentation of the overlap algebra. -/
abbrev overlapPresentationF (f g : R) : Type u :=
  TensorProduct (chartRing f) (overlapRing f g)
    (TensorProduct R (chartRing f) A)

/-- The g-chart tensor presentation of the overlap algebra. -/
abbrev overlapPresentationG (f g : R) : Type u :=
  TensorProduct (chartRing g) (overlapRing f g)
    (TensorProduct R (chartRing g) A)

/-- The common overlap presentation. -/
abbrev overlapPresentation (f g : R) : Type u :=
  TensorProduct R (overlapRing f g) A

/-- Actual tensor base-change equivalence from the f-presentation. -/
noncomputable def overlapPresentationEquivF (f g : R) :
    overlapPresentationF (R := R) (A := A) f g ≃ₐ[overlapRing f g]
      overlapPresentation (R := R) (A := A) f g :=
  Algebra.TensorProduct.cancelBaseChange (R := R) (S := chartRing f)
    (T := overlapRing f g) (A := overlapRing f g) (B := A)

/-- Actual tensor base-change equivalence from the g-presentation. -/
noncomputable def overlapPresentationEquivG (f g : R) :
    overlapPresentationG (R := R) (A := A) f g ≃ₐ[overlapRing f g]
      overlapPresentation (R := R) (A := A) f g :=
  Algebra.TensorProduct.cancelBaseChange (R := R) (S := chartRing g)
    (T := overlapRing f g) (A := overlapRing f g) (B := A)

/-- Exact missing lemma for the f-chart: the base-change equivalence carries
the fixed-point subalgebra of the f-presentation onto the fixed-point
subalgebra of the common overlap presentation. -/
def overlapBaseChangeFixedPointsF (f g : R) : Prop :=
  (FixedPoints.subalgebra (overlapRing f g)
    (overlapPresentationF (R := R) (A := A) f g) G).map
      (overlapPresentationEquivF (R := R) (A := A) f g : _ →ₐ[overlapRing f g] _) =
    FixedPoints.subalgebra (overlapRing f g)
      (overlapPresentation (R := R) (A := A) f g) G

/-- Exact missing lemma for the g-chart. -/
def overlapBaseChangeFixedPointsG (f g : R) : Prop :=
  (FixedPoints.subalgebra (overlapRing f g)
    (overlapPresentationG (R := R) (A := A) f g) G).map
      (overlapPresentationEquivG (R := R) (A := A) f g : _ →ₐ[overlapRing f g] _) =
    FixedPoints.subalgebra (overlapRing f g)
      (overlapPresentation (R := R) (A := A) f g) G

/-- Conditional fixed-point comparison: the two exact base-change fixed-point
statements give the algebra comparison of the two fixed-point subalgebras. -/
theorem overlapFixedPointComparison_of_baseChangeFixedPoints
    (f g : R)
    (hF : overlapBaseChangeFixedPointsF (R := R) (A := A) (G := G) f g)
    (hG : overlapBaseChangeFixedPointsG (R := R) (A := A) (G := G) f g) :
    Nonempty ((FixedPoints.subalgebra (overlapRing f g)
        (overlapPresentationF (R := R) (A := A) f g) G) ≃ₐ[overlapRing f g]
      (FixedPoints.subalgebra (overlapRing f g)
        (overlapPresentationG (R := R) (A := A) f g) G)) :=
  by
    let eF := (overlapPresentationEquivF (R := R) (A := A) f g).subalgebraMap
      (FixedPoints.subalgebra (overlapRing f g)
        (overlapPresentationF (R := R) (A := A) f g) G)
    let eG := (overlapPresentationEquivG (R := R) (A := A) f g).subalgebraMap
      (FixedPoints.subalgebra (overlapRing f g)
        (overlapPresentationG (R := R) (A := A) f g) G)
    exact ⟨(hF ▸ eF).trans (hG ▸ eG).symm⟩

/-- The fixed-point comparison residual reduces to the two exact base-change
fixed-point statements. -/
theorem overlapFixedPointComparisonResidual_of_baseChange
    (f g : R)
    (hF : overlapBaseChangeFixedPointsF (R := R) (A := A) (G := G) f g)
    (hG : overlapBaseChangeFixedPointsG (R := R) (A := A) (G := G) f g) :
    overlapFixedPointComparisonResidual (R := R) (A := A) (G := G) f g :=
  overlapFixedPointComparison_of_baseChangeFixedPoints (R := R) (A := A) (G := G) f g hF hG

end LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineChartOverlapFixedPointComparison
end