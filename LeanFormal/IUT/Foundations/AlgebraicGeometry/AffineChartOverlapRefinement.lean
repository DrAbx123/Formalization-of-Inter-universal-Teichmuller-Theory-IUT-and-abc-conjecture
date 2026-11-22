import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineChartOverlapLocalizationCompatibility
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

/-!
# Affine chart overlap refinement

This file constructs the actual overlap pullbacks of two affine quotient charts
from localization maps and M1 base change, and isolates the exact remaining
comparison needed for a common refinement.  It does not assume the unproved
M1 localization-naturality square.

Post-compile-delta draft; held for watchdog compilation. No provider/IsColimit.
-/

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineChartOverlapRefinement

universe u

open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineChartOverlapLocalizationCompatibility
open ABCBridge.GlobalQuotientChartCompat
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

variable {R A G : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [Group G] [Fintype G] [DecidableEq G]
  [MulSemiringAction G A] [SMulCommClass G R A]
  [Algebra.Etale R A] [Module.Finite R A]

/-- The actual quotient cover over the overlap ring `R[1/(f*g)]`. -/
noncomputable def overlapQuotientCover (f g : R) :
    FiniteEtaleCover (Spec (CommRingCat.of (overlapRing f g))) :=
  chartQuotientCover (R := R) (A := A) (G := G) (f := f * g)

/-- M1 base change identifies the overlap pullback of the f-chart quotient
with the actual overlap quotient cover, after the tensor base-change
identification. -/
noncomputable def overlapPullbackToOverlapQuotient (f g : R) :
    chartOverlapPullback (R := R) (A := A) (G := G) f g ⟶
      (overlapQuotientCover (R := R) (A := A) (G := G) f g).carrier :=
  (chartOverlapPullbackM1Iso (R := R) (A := A) (G := G) f g).hom

/-- The same construction for the g-chart. -/
noncomputable def overlapPullbackToOverlapQuotientG (f g : R) :
    chartOverlapPullback (R := R) (A := A) (G := G) g f ⟶
      (overlapQuotientCover (R := R) (A := A) (G := G) f g).carrier :=
  (chartOverlapPullbackM1Iso (R := R) (A := A) (G := G) g f).hom

/-- Exact obstruction: the two M1 overlap pullbacks are isomorphic over the
overlap, equivalently the fixed-point subalgebras of the two tensor
presentations of `R[1/(f*g)] ⊗[R] A` agree.  This is a Prop, not an inhabitant. -/
def overlapFixedPointComparisonResidual (f g : R) : Prop :=
  Nonempty (chartOverlapPullback (R := R) (A := A) (G := G) f g ≅
    chartOverlapPullback (R := R) (A := A) (G := G) g f)

/-- Actual projection from the f-overlap pullback to the f-chart quotient is
an open immersion. -/
theorem overlapPullbackFst_open (f g : R) :
    IsOpenImmersion (chartOverlapPullbackFst (R := R) (A := A) (G := G) f g) :=
  chartOverlapPullbackFst_isOpenImmersion (R := R) (A := A) (G := G) f g

/-- Conditional common refinement: given exactly the comparison residual, the
two local quotient charts have an actual common refinement with open
immersions into both. -/
theorem commonRefinement_of_fixedPointComparison
    (f g : R) (h : overlapFixedPointComparisonResidual (R := R) (A := A) (G := G) f g) :
    ∃ (W : Scheme.{u})
      (f₁ : W ⟶ (chartQuotientCover (R := R) (A := A) (G := G) f).carrier)
      (f₂ : W ⟶ (chartQuotientCover (R := R) (A := A) (G := G) g).carrier),
      IsOpenImmersion f₁ ∧ IsOpenImmersion f₂ :=
  by
    rcases h with ⟨e⟩
    exact ⟨chartOverlapPullback (R := R) (A := A) (G := G) f g,
      chartOverlapPullbackFst (R := R) (A := A) (G := G) f g,
      e.hom ≫ chartOverlapPullbackFst (R := R) (A := A) (G := G) g f,
      overlapPullbackFst_open (R := R) (A := A) (G := G) f g,
      IsOpenImmersion.comp _ _⟩


/-- The tensor base-change identification for the f-chart overlap algebra. -/
noncomputable def overlapBaseChangeEquivF (f g : R) :
    TensorProduct (chartRing f) (overlapRing f g)
        (TensorProduct R (chartRing f) A) ≃ₐ[overlapRing f g]
      TensorProduct R (overlapRing f g) A :=
  Algebra.TensorProduct.cancelBaseChange (R := R) (S := chartRing f)
    (T := overlapRing f g) (A := overlapRing f g) (B := A)

/-- The tensor base-change identification for the g-chart overlap algebra. -/
noncomputable def overlapBaseChangeEquivG (f g : R) :
    TensorProduct (chartRing g) (overlapRing f g)
        (TensorProduct R (chartRing g) A) ≃ₐ[overlapRing f g]
      TensorProduct R (overlapRing f g) A :=
  Algebra.TensorProduct.cancelBaseChange (R := R) (S := chartRing g)
    (T := overlapRing f g) (A := overlapRing f g) (B := A)

/-- The fixed-point comparison residual in explicit algebra form. -/
def overlapFixedPointAlgebraComparisonResidual (f g : R) : Prop :=
  Nonempty ((FixedPoints.subalgebra (overlapRing f g)
      (TensorProduct (chartRing f) (overlapRing f g)
        (TensorProduct R (chartRing f) A)) G) ≃ₐ[overlapRing f g]
    (FixedPoints.subalgebra (overlapRing f g)
      (TensorProduct (chartRing g) (overlapRing f g)
        (TensorProduct R (chartRing g) A)) G))

theorem overlapQuotientCover_structure (f g : R) :
    (overlapQuotientCover (R := R) (A := A) (G := G) f g).structureMap =
      Spec.map (CommRingCat.ofHom
        (algebraMap (overlapRing f g)
          (FixedPoints.subalgebra (overlapRing f g)
            (TensorProduct R (overlapRing f g) A) G))) :=
  rfl

end LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineChartOverlapRefinement
end
end LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineChartOverlapRefinement
end