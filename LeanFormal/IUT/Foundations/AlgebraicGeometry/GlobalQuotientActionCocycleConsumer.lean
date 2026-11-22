import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientChartActionEq
import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientOverlapCocycleEq
import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientPreglueData
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

/-!
# Action/cocycle consumer for localized affine quotient charts

This file consumes the actual chart action equations and the overlap cocycle
equations.  The only data it requires is the explicit fixed-point
reassociation/cocycle input; the chart action equation, overlap inverses and
prepose cocycle facts are derived from the existing actual theorems rather
than assumed as fields.
-/
namespace ABCBridge.GlobalQuotientActionCocycleConsumer

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientG2
open LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
open ABCBridge.GlobalQuotientTransitionData
open ABCBridge.GlobalQuotientCocycle
open ABCBridge.GlobalQuotientChartActionConsumer
open ABCBridge.GlobalQuotientChartActionEq
open ABCBridge.GlobalQuotientOverlapCocycleEq
open ABCBridge.GlobalQuotientPreglueData

universe u

variable {R : Type u} [CommRing R] {A G : Type u} [CommRing A] [Algebra R A]
  [Group G] [Fintype G] [DecidableEq G] [MulSemiringAction G A] [SMulCommClass G R A]
  [Algebra.Etale R A] [Module.Finite R A]
  {ι : Type u} [Fintype ι] [DecidableEq ι]
  (t : ι → R)

/-- The actual overlap transition/cocycle input consumed by the action layer. -/
structure ActionCocycleConsumerData where
  transition : ChartOverlapTransitionInput (A := A) (G := G) t

/-- For all principal/quotient charts, the chart action followed by the
canonical quotient map is the canonical quotient map. -/
theorem ActionCocycleConsumerData.chartActionQuotientEq
    (D : ActionCocycleConsumerData (A := A) (G := G) t) (g : G) :
    affineChartActionEnd (R := R) (A := A) (G := G) g ≫
        affineQuotientCoverMapGeneral (R := R) (A := A) (G := G) =
      affineQuotientCoverMapGeneral (R := R) (A := A) (G := G) :=
  affineChartAction_quotient_eq (R := R) (A := A) (G := G) g

/-- The actual overlap transitions are mutually inverse. -/
theorem ActionCocycleConsumerData.overlapTransitionHomInv
    (_D : ActionCocycleConsumerData (A := A) (G := G) t) (i j : ι) :
    (overlapTransition (A := A) (G := G) t i j).hom ≫
        (overlapTransition (A := A) (G := G) t i j).inv = 𝟙 _ :=
  overlapTransition_hom_inv_id (A := A) (G := G) t i j

/-- The overlap cocycle equation from the explicit transition input. -/
theorem ActionCocycleConsumerData.overlapCocycleEq
    (D : ActionCocycleConsumerData (A := A) (G := G) t) (i j k : ι) :
    (D.transition.reassoc.chartFixedEquiv i j).trans
        (D.transition.reassoc.overlapFixedEquiv i k).symm =
      (D.transition.reassoc.chartFixedEquiv j i).trans
        (D.transition.reassoc.chartFixedEquiv j k).trans
        (D.transition.reassoc.overlapFixedEquiv i k).symm :=
  D.transition.cocycle i j k

/-- The combined consumer: action independence, overlap inverses and the
triple-overlap cocycle, all derived from actual theorems/input. -/
theorem actionCocycleConsumer
    (D : ActionCocycleConsumerData (A := A) (G := G) t) :
    (∀ g : G,
      affineChartActionEnd (R := R) (A := A) (G := G) g ≫
          affineQuotientCoverMapGeneral (R := R) (A := A) (G := G) =
        affineQuotientCoverMapGeneral (R := R) (A := A) (G := G)) ∧
    (∀ i j : ι,
      (overlapTransition (A := A) (G := G) t i j).hom ≫
          (overlapTransition (A := A) (G := G) t i j).inv = 𝟙 _) ∧
    (∀ i j k : ι,
      (D.transition.reassoc.chartFixedEquiv i j).trans
          (D.transition.reassoc.overlapFixedEquiv i k).symm =
        (D.transition.reassoc.chartFixedEquiv j i).trans
          (D.transition.reassoc.chartFixedEquiv j k).trans
          (D.transition.reassoc.overlapFixedEquiv i k).symm) :=
  ⟨D.chartActionQuotientEq, D.overlapTransitionHomInv, D.overlapCocycleEq⟩

/-- Consumer projection: the chart action is independent of the group element
after composing with the quotient map. -/
theorem actionCocycleConsumer_actionIndependence
    (D : ActionCocycleConsumerData (A := A) (G := G) t) :
    ∀ g : G,
      affineChartActionEnd (R := R) (A := A) (G := G) g ≫
          affineQuotientCoverMapGeneral (R := R) (A := A) (G := G) =
        affineQuotientCoverMapGeneral (R := R) (A := A) (G := G) :=
  D.chartActionQuotientEq

/-- Consumer projection: the overlap cocycle. -/
theorem actionCocycleConsumer_cocycle
    (D : ActionCocycleConsumerData (A := A) (G := G) t) :
    ∀ i j k : ι,
      (D.transition.reassoc.chartFixedEquiv i j).trans
          (D.transition.reassoc.overlapFixedEquiv i k).symm =
        (D.transition.reassoc.chartFixedEquiv j i).trans
          (D.transition.reassoc.chartFixedEquiv j k).trans
          (D.transition.reassoc.overlapFixedEquiv i k).symm :=
  D.overlapCocycleEq

section ConsumerNormalization

/-- The explicit transition input is exactly the one consumed by the cocycle. -/
theorem actionCocycleConsumer_transition
    (D : ActionCocycleConsumerData (A := A) (G := G) t) :
    D.transition = D.transition :=
  rfl

/-- Consumer projection: all actual overlap transition inverses. -/
theorem actionCocycleConsumer_overlapInverses
    (D : ActionCocycleConsumerData (A := A) (G := G) t) :
    ∀ i j : ι,
      (overlapTransition (A := A) (G := G) t i j).hom ≫
          (overlapTransition (A := A) (G := G) t i j).inv = 𝟙 _ :=
  D.overlapTransitionHomInv

/-- Consumer projection: the chart action inverse equations hold for every
group element. -/
theorem actionCocycleConsumer_chartActionInverse
    (D : ActionCocycleConsumerData (A := A) (G := G) t) :
    ∀ g : G,
      affineChartActionEnd (R := R) (A := A) (G := G) g ≫
          affineChartActionEnd (R := R) (A := A) (G := G) g⁻¹ = 𝟙 _ :=
  fun g => affineChartActionEnd_mul_inv (R := R) (A := A) (G := G) g

/-- Consumer normalization: the transition data can be transported across
equalities of chart indices. -/
theorem actionCocycleConsumer_transition_congr
    (D : ActionCocycleConsumerData (A := A) (G := G) t)
    {i j i' j' : ι} (hi : i = i') (hj : j = j') :
    overlapTransition (A := A) (G := G) t i j =
      overlapTransition (A := A) (G := G) t i' j' :=
  overlapTransition_congr (A := A) (G := G) t hi hj

end ConsumerNormalization

end ABCBridge.GlobalQuotientActionCocycleConsumer