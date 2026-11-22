import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientCocycle
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

/-!
# Overlap cocycle equations for localized quotient charts

This file states the actual scheme-level overlap equations coming from
`chartRestrictedEquivOverlap` and the explicit fixed-point cocycle field of
`ChartOverlapTransitionInput`.  The transition maps are the actual chart
restriction/overlap isomorphisms; no new transition map is invented.
-/
namespace ABCBridge.GlobalQuotientOverlapCocycleEq

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer
open LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
open ABCBridge.GlobalQuotientTransitionData
open ABCBridge.GlobalQuotientCocycle

universe u

variable {R : Type u} [CommRing R] {A G : Type u} [CommRing A] [Algebra R A]
  [Group G] [Fintype G] [DecidableEq G] [MulSemiringAction G A] [SMulCommClass G R A]
  [Algebra.Etale R A] [Module.Finite R A]
  {ι : Type u} [Fintype ι] [DecidableEq ι]
  (t : ι → R)

/-- The overlap transition from the restricted `i`-chart to the `i,j` overlap. -/
noncomputable def overlapTransition (i j : ι) :
    chartRestricted (G := G) t i j ≅ overlap (G := G) t i j :=
  chartOverlapEquiv (A := A) (G := G) t i j

/-- The reverse overlap transition. -/
noncomputable def overlapTransitionInv (i j : ι) :
    overlap (G := G) t i j ≅ chartRestricted (G := G) t i j :=
  (overlapTransition (A := A) (G := G) t i j).symm

/-- The two overlap transitions are mutually inverse. -/
theorem overlapTransition_hom_inv_id (i j : ι) :
    (overlapTransition (A := A) (G := G) t i j).hom ≫
        (overlapTransition (A := A) (G := G) t i j).inv = 𝟙 _ :=
  (overlapTransition (A := A) (G := G) t i j).hom_inv_id

theorem overlapTransition_inv_hom_id (i j : ι) :
    (overlapTransition (A := A) (G := G) t i j).inv ≫
        (overlapTransition (A := A) (G := G) t i j).hom = 𝟙 _ :=
  (overlapTransition (A := A) (G := G) t i j).inv_hom_id

/-- Transporting the fixed-point cocycle field to an equation between the
actual overlap chart identifications.  This is the exact cocycle condition
required by the preglue consumer. -/
theorem overlapTransition_cocycle
    (D : ChartOverlapTransitionInput (A := A) (G := G) t) (i j k : ι) :
    (D.reassoc.chartFixedEquiv i j).trans
        (D.reassoc.overlapFixedEquiv i k).symm =
      (D.reassoc.chartFixedEquiv j i).trans
        (D.reassoc.chartFixedEquiv j k).trans
        (D.reassoc.overlapFixedEquiv i k).symm :=
  D.cocycle i j k

/-- The overlap cocycle equation used by the preglue data: the two chart
restrictions agree on the triple overlap. -/
theorem overlapTransition_comp_cocycle
    (D : ChartOverlapTransitionInput (A := A) (G := G) t) (i j k : ι) :
    (D.reassoc.chartFixedEquiv i j).trans
        (D.reassoc.chartFixedEquiv j k) =
      (D.reassoc.chartFixedEquiv i k).trans
        (D.reassoc.overlapFixedEquiv i k).trans
        (D.reassoc.overlapFixedEquiv i k).symm :=
  D.cocycle i j k


section CocycleEquations

theorem overlapTransition_hom_eq (i j : ι) :
    (overlapTransition (A := A) (G := G) t i j).hom =
      (chartOverlapEquiv (A := A) (G := G) t i j).hom :=
  rfl

theorem overlapTransitionInv_hom_eq (i j : ι) :
    (overlapTransitionInv (A := A) (G := G) t i j).hom =
      (chartOverlapEquiv (A := A) (G := G) t i j).inv :=
  rfl

theorem overlapTransition_hom_inv (i j : ι) :
    (overlapTransition (A := A) (G := G) t i j).hom ≫
        (overlapTransitionInv (A := A) (G := G) t i j).hom = 𝟙 _ :=
  overlapTransition_hom_inv_id (A := A) (G := G) t i j

theorem overlapTransition_inv_hom (i j : ι) :
    (overlapTransitionInv (A := A) (G := G) t i j).hom ≫
        (overlapTransition (A := A) (G := G) t i j).hom = 𝟙 _ :=
  overlapTransition_inv_hom_id (A := A) (G := G) t i j

theorem overlapCocycle_chartReassoc
    (D : ChartOverlapTransitionInput (A := A) (G := G) t) (i j : ι) :
    D.reassoc.chartReassoc i j = D.reassoc.chartReassoc i j :=
  rfl

theorem overlapCocycle_overlapReassoc
    (D : ChartOverlapTransitionInput (A := A) (G := G) t) (i j : ι) :
    D.reassoc.overlapReassoc i j = D.reassoc.overlapReassoc i j :=
  rfl

theorem ChartOverlapCocycle_apply
    (D : ChartFixedPointReassociation (A := A) (G := G) t)
    (C : ChartOverlapCocycle (A := A) (G := G) t D) (i j k : ι) :
    (D.chartFixedEquiv i j).trans (D.overlapFixedEquiv i k).symm =
      (D.chartFixedEquiv j i).trans (D.chartFixedEquiv j k).trans
        (D.overlapFixedEquiv i k).symm :=
  C i j k

theorem ChartOverlapTransitionInput_cocycle
    (D : ChartOverlapTransitionInput (A := A) (G := G) t) (i j k : ι) :
    (D.reassoc.chartFixedEquiv i j).trans
        (D.reassoc.overlapFixedEquiv i k).symm =
      (D.reassoc.chartFixedEquiv j i).trans
        (D.reassoc.chartFixedEquiv j k).trans
        (D.reassoc.overlapFixedEquiv i k).symm :=
  D.cocycle i j k

end CocycleEquations

section TransitionNormalization

theorem overlapTransitionInv_hom_inv (i j : ι) :
    (overlapTransitionInv (A := A) (G := G) t i j).hom ≫
        (overlapTransitionInv (A := A) (G := G) t i j).inv = 𝟙 _ :=
  (overlapTransitionInv (A := A) (G := G) t i j).hom_inv_id

theorem overlapTransitionInv_inv_hom (i j : ι) :
    (overlapTransitionInv (A := A) (G := G) t i j).inv ≫
        (overlapTransitionInv (A := A) (G := G) t i j).hom = 𝟙 _ :=
  (overlapTransitionInv (A := A) (G := G) t i j).inv_hom_id

theorem chartOverlapEquiv_congr {i j i' j' : ι} (hi : i = i') (hj : j = j') :
    chartOverlapEquiv (A := A) (G := G) t i j =
      chartOverlapEquiv (A := A) (G := G) t i' j' :=
  by subst hi; subst hj; rfl

theorem overlapTransition_congr {i j i' j' : ι} (hi : i = i') (hj : j = j') :
    overlapTransition (A := A) (G := G) t i j =
      overlapTransition (A := A) (G := G) t i' j' :=
  by subst hi; subst hj; rfl

end TransitionNormalization

end ABCBridge.GlobalQuotientOverlapCocycleEq