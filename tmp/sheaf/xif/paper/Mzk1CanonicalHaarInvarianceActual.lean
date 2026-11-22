/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1HaarScalarOneActual
import tmp.sheaf.xif.paper.Mzk1CanonicalHaarRegularActual

/-! # Canonical Haar invariance, unconditional OuterRegular (task-109) -/
noncomputable section
open scoped BigOperators
open MeasureTheory
open MeasureTheory.Measure
namespace LeanFormal.IUT.XiFPaper.Mzk1CanonicalHaarInvarianceActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarScalarOneActual
open LeanFormal.IUT.XiFPaper.Mzk1CanonicalHaarRegularActual
open LeanFormal.IUT.XiFPaper.Mzk1MatrixHaarBaseActual
variable {p : Nat} [Fact p.Prime] {d : Type} [Fintype d] [DecidableEq d]
variable [TopologicalSpace (d → ℚ_[p])] [MeasurableSpace (d → ℚ_[p])]
variable [IsTopologicalAddGroup (d → ℚ_[p])] [BorelSpace (d → ℚ_[p])]
variable [LocallyCompactSpace (d → ℚ_[p])]

/-- For canonical additive Haar, the full measurable-set invariance needs no
`OuterRegular` hypothesis: `regular_haarMeasure` supplies it, and the image
measure is outer regular because `L` is a homeomorphism. -/
theorem canonical_map_eq_of_image_eq
    (K₀ : TopologicalSpace.PositiveCompacts (d → ℚ_[p]))
    (L : (d → ℚ_[p]) ≃L[ℚ_[p]] (d → ℚ_[p]))
    (h : L '' coordLattice (p := p) (d := d) = coordLattice (p := p) (d := d))
    (hO : IsOpen (coordLattice (p := p) (d := d)))
    (hOpos : addHaarMeasure K₀ (coordLattice (p := p) (d := d)) ≠ 0)
    (hOfin : addHaarMeasure K₀ (coordLattice (p := p) (d := d)) ≠ ⊤) :
    (addHaarMeasure K₀).map L = addHaarMeasure K₀ := by
  haveI : Measure.OuterRegular (addHaarMeasure K₀) :=
    canonical_addHaarMeasure_outerRegular K₀
  haveI : Measure.OuterRegular ((addHaarMeasure K₀).map L) :=
    Measure.OuterRegular.map L.toHomeomorph (addHaarMeasure K₀)
  exact map_eq_of_image_eq L h hO (addHaarMeasure K₀) hOpos hOfin
def canonicalInvRows : List (String × String) :=
  [ ("canonical_map_eq_of_image_eq", "unconditional canonical Haar"),
    ("glAct instance", "GAP") ]
theorem canonicalInvRows_length : canonicalInvRows.length = 2 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1CanonicalHaarInvarianceActual
