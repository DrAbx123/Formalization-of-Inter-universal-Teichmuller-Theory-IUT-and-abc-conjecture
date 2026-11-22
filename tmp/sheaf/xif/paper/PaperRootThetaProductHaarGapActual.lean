import tmp.sheaf.xif.paper.PaperRootThetaProductMeasureActual

/-! # Exact local/product Haar API gap for the root Theta carrier -/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section
open scoped BigOperators Pointwise

namespace LeanFormal.IUT.XiFPaper.PaperRootThetaProductHaarGapActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open LeanFormal.IUT.XiFPaper.PaperRootThetaProductCarrierActual
open LeanFormal.IUT.XiFPaper.PaperRootThetaProductMeasureActual
open MeasureTheory

universe u v

variable {l : PrimeGeFive}
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {V : Type v} [Fintype V]
variable (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)
variable [MeasurableSpace (RootThetaProductCarrier (G := G))]

/-- Exact per-place local Haar API on the algebraic-closure unit ball. -/
structure RootThetaLocalHaarData (v : V) where
  carrier : Type
  [measurableSpace : MeasurableSpace carrier]
  [topologicalSpace : TopologicalSpace carrier]
  [addGroup : AddGroup carrier]
  [isTopologicalAddGroup : IsTopologicalAddGroup carrier]
  [locallyCompact : LocallyCompactSpace carrier]
  measure : Measure carrier
  [isAddHaar : Measure.IsAddHaarMeasure measure]
  unitBall : Set carrier
  unitBall_pos : 0 < measure unitBall
  unitBall_lt_top : measure unitBall < ⊤

/-- Exact finite-product Haar API on the root Theta unit ball. -/
structure RootThetaProductHaarData where
  localHaar : ∀ v : V, RootThetaLocalHaarData v
  carrier : Type
  [measurableSpace : MeasurableSpace carrier]
  productMeasure : Measure carrier
  unitBall : Set carrier
  unitBall_pos : 0 < productMeasure unitBall
  unitBall_lt_top : productMeasure unitBall < ⊤

/-- Exact missing local Haar object. -/
def RootThetaLocalHaarGapRequired : Prop :=
  ∀ v : V, Nonempty (RootThetaLocalHaarData (V := V) v)

/-- Exact missing finite-product Haar object. -/
def RootThetaProductHaarGapRequired : Prop :=
  Nonempty (RootThetaProductHaarData (V := V))

/-- The Dirac image measure is explicitly the image-count measure, not a Haar
measure. -/
theorem rootThetaImageMeasure_eq_diracCount :
    rootThetaImageMeasure (G := G) =
      ∑ j : ThetaLabel (l := l),
        Measure.dirac (rootThetaProductImagePoint (G := G) j) := rfl

end LeanFormal.IUT.XiFPaper.PaperRootThetaProductHaarGapActual

end