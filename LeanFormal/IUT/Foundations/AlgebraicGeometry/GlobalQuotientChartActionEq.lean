import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientChartActionConsumer
import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientChartCompat
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

/-!
# Chart action equations

Actual equations for the action of `G` on the affine chart and on the
quotient fixed-point chart.  The chart action is built from
`MulSemiringAction.toAlgEquiv`; the quotient action is the induced trivial
action.  No transition map is introduced here.
-/
namespace ABCBridge.GlobalQuotientChartActionEq

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientG2
open LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
open ABCBridge.GlobalQuotientChartActionConsumer

universe u

variable {R : Type u} [CommRing R] {A G : Type u} [CommRing A] [Algebra R A]
  [Group G] [Fintype G] [DecidableEq G] [MulSemiringAction G A] [SMulCommClass G R A]
  [Algebra.Etale R A] [Module.Finite R A]

/-- The action of `g` followed by the action of `g⁻¹` is the identity chart
endomorphism. -/
theorem affineChartActionEnd_mul_inv (g : G) :
    affineChartActionEnd (R := R) (A := A) (G := G) g ≫
        affineChartActionEnd (R := R) (A := A) (G := G) g⁻¹ = 𝟙 _ := by
  rw [← affineChartActionEnd_mul]
  rw [mul_inv_cancel]
  exact affineChartActionEnd_one

/-- The action of `g⁻¹` followed by the action of `g` is the identity chart
endomorphism. -/
theorem affineChartActionEnd_inv_mul (g : G) :
    affineChartActionEnd (R := R) (A := A) (G := G) g⁻¹ ≫
        affineChartActionEnd (R := R) (A := A) (G := G) g = 𝟙 _ := by
  rw [← affineChartActionEnd_mul]
  rw [inv_mul_cancel]
  exact affineChartActionEnd_one

/-- The chart action is compatible with the canonical quotient map at the
level of `g` and `g⁻¹`. -/
theorem affineChartAction_quotient_eq_inv (g : G) :
    affineChartActionEnd (R := R) (A := A) (G := G) g⁻¹ ≫
        affineQuotientCoverMapGeneral (R := R) (A := A) (G := G) =
      affineQuotientCoverMapGeneral (R := R) (A := A) (G := G) :=
  affineChartAction_quotient_eq (R := R) (A := A) (G := G) g⁻¹

/-- The quotient chart action is compatible with the identity chart action. -/
theorem affineQuotientChartAction_eq_refl (g : G) :
    affineQuotientChartAction (R := R) (A := A) (G := G) g =
      Iso.refl (affineQuotientCoverGeneral (R := R) (A := A) (G := G)) :=
  rfl

/-- The quotient chart action is an involution in the sense that `g` and
`g⁻¹` induce the same identity isomorphism. -/
theorem affineQuotientChartAction_inv_eq (g : G) :
    affineQuotientChartAction (R := R) (A := A) (G := G) g⁻¹ =
      affineQuotientChartAction (R := R) (A := A) (G := G) g :=
  by simp [affineQuotientChartAction]

section ChartActionInverseEquations

theorem affineChartAction_quotient_eq_comp_inv (g h : G) :
    affineChartActionEnd (R := R) (A := A) (G := G) (g * h) ≫
        affineQuotientCoverMapGeneral (R := R) (A := A) (G := G) =
      affineQuotientCoverMapGeneral (R := R) (A := A) (G := G) :=
  affineChartAction_quotient_eq (R := R) (A := A) (G := G) (g * h)

theorem affineChartActionEnd_inv_quotient_eq (g : G) :
    affineChartActionEnd (R := R) (A := A) (G := G) g ≫
        affineChartActionEnd (R := R) (A := A) (G := G) g⁻¹ ≫
        affineQuotientCoverMapGeneral (R := R) (A := A) (G := G) =
      affineQuotientCoverMapGeneral (R := R) (A := A) (G := G) :=
  by
  rw [← Category.assoc, affineChartActionEnd_mul_inv, Category.id_comp]
  exact affineChartAction_quotient_eq (R := R) (A := A) (G := G) 1

theorem affineQuotientChartAction_one_eq_refl :
    affineQuotientChartAction (R := R) (A := A) (G := G) (1 : G) =
      Iso.refl (affineQuotientCoverGeneral (R := R) (A := A) (G := G)) :=
  rfl

theorem affineChartActionEnd_one_quotient_eq :
    affineChartActionEnd (R := R) (A := A) (G := G) (1 : G) ≫
        affineQuotientCoverMapGeneral (R := R) (A := A) (G := G) =
      affineQuotientCoverMapGeneral (R := R) (A := A) (G := G) :=
  affineChartAction_quotient_eq (R := R) (A := A) (G := G) 1

end ChartActionInverseEquations

end ABCBridge.GlobalQuotientChartActionEq