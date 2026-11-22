import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientOverlapCocycleEq
import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientPreglueData
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

/-!
# Transition cocycle consumer for localized quotient charts

This file consumes the explicit fixed-point reassociation/cocycle input and
the actual overlap transition isomorphisms.  It exposes the cocycle equation
and the overlap transition inverses in the form required by the preglue data.
No new transition map is introduced.
-/
namespace ABCBridge.GlobalQuotientTransitionCocycleConsumer

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer
open LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
open ABCBridge.GlobalQuotientTransitionData
open ABCBridge.GlobalQuotientCocycle
open ABCBridge.GlobalQuotientOverlapCocycleEq
open ABCBridge.GlobalQuotientPreglueData

universe u

variable {R : Type u} [CommRing R] {A G : Type u} [CommRing A] [Algebra R A]
  [Group G] [Fintype G] [DecidableEq G] [MulSemiringAction G A] [SMulCommClass G R A]
  [Algebra.Etale R A] [Module.Finite R A]
  {ι : Type u} [Fintype ι] [DecidableEq ι]
  (t : ι → R)

/-- The consumer result: actual overlap transition inverses and the explicit
triple-overlap cocycle equation. -/
structure TransitionCocycleResult
    (D : ChartOverlapTransitionInput (A := A) (G := G) t) where
  hom_inv : ∀ i j : ι,
    (overlapTransition (A := A) (G := G) t i j).hom ≫
        (overlapTransition (A := A) (G := G) t i j).inv = 𝟙 _
  inv_hom : ∀ i j : ι,
    (overlapTransition (A := A) (G := G) t i j).inv ≫
        (overlapTransition (A := A) (G := G) t i j).hom = 𝟙 _
  cocycle : ∀ i j k : ι,
    (D.reassoc.chartFixedEquiv i j).trans
        (D.reassoc.overlapFixedEquiv i k).symm =
      (D.reassoc.chartFixedEquiv j i).trans
        (D.reassoc.chartFixedEquiv j k).trans
        (D.reassoc.overlapFixedEquiv i k).symm

/-- Actual consumer of the transition/cocycle data. -/
noncomputable def transitionCocycleResult
    (D : ChartOverlapTransitionInput (A := A) (G := G) t) :
    TransitionCocycleResult (A := A) (G := G) t D where
  hom_inv i j := overlapTransition_hom_inv_id (A := A) (G := G) t i j
  inv_hom i j := overlapTransition_inv_hom_id (A := A) (G := G) t i j
  cocycle i j k := D.cocycle i j k

theorem transitionCocycleResult_hom_inv
    (D : ChartOverlapTransitionInput (A := A) (G := G) t) (i j : ι) :
    (overlapTransition (A := A) (G := G) t i j).hom ≫
        (overlapTransition (A := A) (G := G) t i j).inv = 𝟙 _ :=
  (transitionCocycleResult (A := A) (G := G) t D).hom_inv i j

theorem transitionCocycleResult_inv_hom
    (D : ChartOverlapTransitionInput (A := A) (G := G) t) (i j : ι) :
    (overlapTransition (A := A) (G := G) t i j).inv ≫
        (overlapTransition (A := A) (G := G) t i j).hom = 𝟙 _ :=
  (transitionCocycleResult (A := A) (G := G) t D).inv_hom i j

theorem transitionCocycleResult_cocycle
    (D : ChartOverlapTransitionInput (A := A) (G := G) t) (i j k : ι) :
    (D.reassoc.chartFixedEquiv i j).trans
        (D.reassoc.overlapFixedEquiv i k).symm =
      (D.reassoc.chartFixedEquiv j i).trans
        (D.reassoc.chartFixedEquiv j k).trans
        (D.reassoc.overlapFixedEquiv i k).symm :=
  (transitionCocycleResult (A := A) (G := G) t D).cocycle i j k

theorem transitionCocycleResult_overlapTransition
    (D : ChartOverlapTransitionInput (A := A) (G := G) t) (i j : ι) :
    overlapTransition (A := A) (G := G) t i j =
      chartOverlapEquiv (A := A) (G := G) t i j :=
  rfl

end ABCBridge.GlobalQuotientTransitionCocycleConsumer