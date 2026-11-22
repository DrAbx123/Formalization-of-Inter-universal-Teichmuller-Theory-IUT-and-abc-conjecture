import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientTransitionData
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

/-!
# Overlap transition data and cocycle for localized quotient charts

For a finite family `t : ι → R`, `chartRestrictedEquivOverlap` identifies the
restricted `i`-chart with the canonical overlap chart.  This file records the
transition data between chart restrictions and the exact fixed-point
reassociation fields still needed to turn that identification into actual
scheme-level transition maps between the localized quotient covers.

Nothing here is a fake cover: the missing tensor/reassociation data is an
explicit structure, and the cocycle is required as an explicit field.
-/
namespace ABCBridge.GlobalQuotientCocycle

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer
open LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
open ABCBridge.GlobalQuotientTransitionData

universe u

variable {R : Type u} [CommRing R] {A G : Type u} [CommRing A] [Algebra R A]
  [Group G] [Fintype G] [DecidableEq G] [MulSemiringAction G A] [SMulCommClass G R A]
  [Algebra.Etale R A] [Module.Finite R A]
  {ι : Type u} [Fintype ι] [DecidableEq ι]
  (t : ι → R)

/-- The restricted chart cover and the canonical overlap cover are isomorphic.
This is the actual scheme-level overlap identification. -/
noncomputable def chartOverlapEquiv (i j : ι) :
    chartRestricted (G := G) t i j ≅ overlap (G := G) t i j :=
  chartRestrictedEquivOverlap (G := G) t i j

/-- The reverse overlap identification. -/
noncomputable def overlapChartEquiv (i j : ι) :
    overlap (G := G) t i j ≅ chartRestricted (G := G) t i j :=
  (chartOverlapEquiv (G := G) t i j).symm

/-- The exact fixed-point reassociation comparison needed to identify the
restricted chart with the overlap chart after the two localized algebras are
identified.  These are the fields that are not constructed in the current
chart files; they are required, not assumed silently. -/
structure ChartFixedPointReassociation where
  chartReassoc : ∀ i j,
    TensorProduct (baseLocal t i) (baseOverlap t i j) (algLocal (A := A) t i) ≃ₐ[baseOverlap t i j]
      algOverlap (A := A) t i j
  overlapReassoc : ∀ i j,
    TensorProduct (baseLocal t j) (baseOverlap t i j) (algLocal (A := A) t j) ≃ₐ[baseOverlap t i j]
      algOverlap (A := A) t i j
  /-- The transported fixed-point algebras agree with the canonical overlap
  fixed-point algebra. -/
  chartFixedEquiv : ∀ i j,
    fixedPointSubalgebra (baseOverlap t i j)
        (TensorProduct (baseLocal t i) (baseOverlap t i j)
          (algLocal (A := A) t i)) G ≃ₐ[baseOverlap t i j]
      fixedPointSubalgebra (baseOverlap t i j) (algOverlap (A := A) t i j) G
  overlapFixedEquiv : ∀ i j,
    fixedPointSubalgebra (baseOverlap t i j)
        (TensorProduct (baseLocal t j) (baseOverlap t i j)
          (algLocal (A := A) t j)) G ≃ₐ[baseOverlap t i j]
      fixedPointSubalgebra (baseOverlap t i j) (algOverlap (A := A) t i j) G

/-- The exact cocycle condition required for the localized overlap charts. -/
def ChartOverlapCocycle (D : ChartFixedPointReassociation (A := A) (G := G) t) : Prop :=
  ∀ i j k : ι,
    (D.chartFixedEquiv i j).trans (D.overlapFixedEquiv i k).symm =
      (D.chartFixedEquiv j i).trans (D.chartFixedEquiv j k).trans
        (D.overlapFixedEquiv i k).symm

/-- Combined transition input: fixed-point reassociation plus the explicit
cocycle.  No inhabitant is fabricated. -/
structure ChartOverlapTransitionInput where
  reassoc : ChartFixedPointReassociation (A := A) (G := G) t
  cocycle : ChartOverlapCocycle (A := A) (G := G) t reassoc


section CocycleProjections

theorem chartOverlapEquiv_hom (i j : ι) :
    (chartOverlapEquiv (A := A) (G := G) t i j).hom =
      (chartRestrictedEquivOverlap (G := G) t i j).hom :=
  rfl

theorem overlapChartEquiv_hom (i j : ι) :
    (overlapChartEquiv (A := A) (G := G) t i j).hom =
      (chartRestrictedEquivOverlap (G := G) t i j).inv :=
  rfl

theorem chartFixedEquiv_bijective
    (D : ChartFixedPointReassociation (A := A) (G := G) t) (i j : ι) :
    Function.Bijective (D.chartFixedEquiv i j) :=
  (D.chartFixedEquiv i j).bijective

theorem overlapFixedEquiv_bijective
    (D : ChartFixedPointReassociation (A := A) (G := G) t) (i j : ι) :
    Function.Bijective (D.overlapFixedEquiv i j) :=
  (D.overlapFixedEquiv i j).bijective

end CocycleProjections

end ABCBridge.GlobalQuotientCocycle
