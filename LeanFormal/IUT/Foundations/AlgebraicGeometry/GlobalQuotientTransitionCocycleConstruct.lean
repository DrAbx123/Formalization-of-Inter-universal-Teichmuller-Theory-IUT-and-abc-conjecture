import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientTransitionConstruct
import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientCocycle
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

/-!
# Cocycle construction from the tensor reassociation

This file replaces the explicit `ChartOverlapTransitionInput` fields by the
actual tensor reassociation and fixed-point equivalences constructed in
`GlobalQuotientTransitionConstruct`.  The cocycle field is proved from
naturality of `Algebra.TensorProduct.cancelBaseChange`.
-/
namespace ABCBridge.GlobalQuotientTransitionCocycleConstruct

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientG2
open LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
open ABCBridge.SplitCaseFixedPointsTransport
open ABCBridge.GlobalQuotientTransitionData
open ABCBridge.GlobalQuotientCocycle
open ABCBridge.GlobalQuotientTransitionConstruct

universe u

variable {R : Type u} [CommRing R] {A G : Type u} [CommRing A] [Algebra R A]
  [Group G] [Fintype G] [DecidableEq G] [MulSemiringAction G A] [SMulCommClass G R A]
  [Algebra.Etale R A] [Module.Finite R A]
  {ι : Type u} [Fintype ι] [DecidableEq ι]
  (t : ι → R)

/-- The actual reassociation/cocycle input built from the two tensor
reassociations.  The cocycle is the naturality equation of the fixed-point
reassociations. -/
noncomputable def chartOverlapTransitionInputConstruct
    (hchart : ∀ i j (g : G)
      (x : TensorProduct (baseLocal t i) (baseOverlap t i j) (algLocal (A := A) t i)),
      chartOverlapTensorReassoc (A := A) (G := G) t i j (g • x) =
        g • chartOverlapTensorReassoc (A := A) (G := G) t i j x)
    (hoverlap : ∀ i j (g : G)
      (x : TensorProduct (baseLocal t j) (baseOverlap t i j) (algLocal (A := A) t j)),
      overlapTensorReassoc (A := A) (G := G) t i j (g • x) =
        g • overlapTensorReassoc (A := A) (G := G) t i j x) :
    ChartOverlapTransitionInput (A := A) (G := G) t where
  reassoc := chartFixedPointReassociation (A := A) (G := G) t hchart hoverlap
  cocycle := by
    intro i j k
    ext x
    simp only [chartFixedPointReassociation, chartOverlapFixedEquiv,
      overlapFixedEquivOfEquiv, fixedPointsAlgEquivOfEquiv, AlgEquiv.trans_apply,
      AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply]
    rfl

theorem chartOverlapTransitionInputConstruct_reassoc_chart
    (hchart : ∀ i j (g : G)
      (x : TensorProduct (baseLocal t i) (baseOverlap t i j) (algLocal (A := A) t i)),
      chartOverlapTensorReassoc (A := A) (G := G) t i j (g • x) =
        g • chartOverlapTensorReassoc (A := A) (G := G) t i j x)
    (hoverlap : ∀ i j (g : G)
      (x : TensorProduct (baseLocal t j) (baseOverlap t i j) (algLocal (A := A) t j)),
      overlapTensorReassoc (A := A) (G := G) t i j (g • x) =
        g • overlapTensorReassoc (A := A) (G := G) t i j x)
    (i j : ι) :
    (chartOverlapTransitionInputConstruct (A := A) (G := G) t hchart hoverlap).reassoc.chartReassoc i j =
      chartOverlapTensorReassoc (A := A) (G := G) t i j :=
  rfl

theorem chartOverlapTransitionInputConstruct_reassoc_overlap
    (hchart : ∀ i j (g : G)
      (x : TensorProduct (baseLocal t i) (baseOverlap t i j) (algLocal (A := A) t i)),
      chartOverlapTensorReassoc (A := A) (G := G) t i j (g • x) =
        g • chartOverlapTensorReassoc (A := A) (G := G) t i j x)
    (hoverlap : ∀ i j (g : G)
      (x : TensorProduct (baseLocal t j) (baseOverlap t i j) (algLocal (A := A) t j)),
      overlapTensorReassoc (A := A) (G := G) t i j (g • x) =
        g • overlapTensorReassoc (A := A) (G := G) t i j x)
    (i j : ι) :
    (chartOverlapTransitionInputConstruct (A := A) (G := G) t hchart hoverlap).reassoc.overlapReassoc i j =
      overlapTensorReassoc (A := A) (G := G) t i j :=
  rfl

theorem chartOverlapTransitionInputConstruct_cocycle
    (hchart : ∀ i j (g : G)
      (x : TensorProduct (baseLocal t i) (baseOverlap t i j) (algLocal (A := A) t i)),
      chartOverlapTensorReassoc (A := A) (G := G) t i j (g • x) =
        g • chartOverlapTensorReassoc (A := A) (G := G) t i j x)
    (hoverlap : ∀ i j (g : G)
      (x : TensorProduct (baseLocal t j) (baseOverlap t i j) (algLocal (A := A) t j)),
      overlapTensorReassoc (A := A) (G := G) t i j (g • x) =
        g • overlapTensorReassoc (A := A) (G := G) t i j x)
    (i j k : ι) :
    ((chartOverlapTransitionInputConstruct (A := A) (G := G) t hchart hoverlap).reassoc.chartFixedEquiv i j).trans
        ((chartOverlapTransitionInputConstruct (A := A) (G := G) t hchart hoverlap).reassoc.overlapFixedEquiv i k).symm =
      ((chartOverlapTransitionInputConstruct (A := A) (G := G) t hchart hoverlap).reassoc.chartFixedEquiv j i).trans
        ((chartOverlapTransitionInputConstruct (A := A) (G := G) t hchart hoverlap).reassoc.chartFixedEquiv j k).trans
        ((chartOverlapTransitionInputConstruct (A := A) (G := G) t hchart hoverlap).reassoc.overlapFixedEquiv i k).symm :=
  (chartOverlapTransitionInputConstruct (A := A) (G := G) t hchart hoverlap).cocycle i j k

end ABCBridge.GlobalQuotientTransitionCocycleConstruct
