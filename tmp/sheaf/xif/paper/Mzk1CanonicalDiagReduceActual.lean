import tmp.sheaf.xif.paper.Mzk1CanonicalDiagScalingActual

/-! Canonical diagonal volume: remove positive/finite hypotheses using
`IsOpen.measure_pos` and `IsCompact.measure_lt_top` for `addHaarMeasure`. -/
noncomputable section
open scoped BigOperators
open MeasureTheory MeasureTheory.Measure
namespace LeanFormal.IUT.XiFPaper.Mzk1CanonicalDiagReduceActual
open LeanFormal.IUT.XiFPaper.Mzk1CanonicalHaarCoordLatticeActual
open LeanFormal.IUT.XiFPaper.Mzk1CanonicalDiagScalingActual
variable {p : Nat} [Fact p.Prime] {d : Type} [Fintype d] [DecidableEq d]
variable [MeasurableSpace (d → ℚ_[p])] [BorelSpace (d → ℚ_[p])]

theorem canonical_diag_volume_ratio_reduced
    (f : d → Nat)
    (hle : LeanFormal.IUT.XiFPaper.Mzk1DiagEmbeddingEquivActual.coordDual (p := p) (d := d) f ≤
      LeanFormal.IUT.XiFPaper.Mzk1DiagEmbeddingEquivActual.coordSmall (p := p) (d := d))
    (hLc : IsCompact (LeanFormal.IUT.XiFPaper.Mzk1DiagEmbeddingEquivActual.coordSmall (p := p) (d := d) : Set (d → ℚ_[p])))
    (hLo : IsOpen (LeanFormal.IUT.XiFPaper.Mzk1DiagEmbeddingEquivActual.coordSmall (p := p) (d := d) : Set (d → ℚ_[p])))
    (hXc : IsCompact (LeanFormal.IUT.XiFPaper.Mzk1DiagEmbeddingEquivActual.coordDual (p := p) (d := d) f : Set (d → ℚ_[p])))
    (hXo : IsOpen (LeanFormal.IUT.XiFPaper.Mzk1DiagEmbeddingEquivActual.coordDual (p := p) (d := d) f : Set (d → ℚ_[p]))) :
    (addHaarMeasure (coordinateCompacts (p := p) (d := d))
      (LeanFormal.IUT.XiFPaper.Mzk1DiagEmbeddingEquivActual.coordDual (p := p) (d := d) f : Set (d → ℚ_[p]))).toReal /
      (addHaarMeasure (coordinateCompacts (p := p) (d := d))
      (LeanFormal.IUT.XiFPaper.Mzk1DiagEmbeddingEquivActual.coordSmall (p := p) (d := d) : Set (d → ℚ_[p]))).toReal =
      (∏ i, (p : ℝ) ^ (f i))⁻¹ := by
  let μ := addHaarMeasure (coordinateCompacts (p := p) (d := d))
  haveI : Measure.IsAddHaarMeasure μ := inferInstance
  have hXpos : μ (LeanFormal.IUT.XiFPaper.Mzk1DiagEmbeddingEquivActual.coordDual (p := p) (d := d) f : Set (d → ℚ_[p])) ≠ 0 :=
    (hXo.measure_pos μ ⟨0, Submodule.zero_mem _⟩).ne'
  have hXtop : μ (LeanFormal.IUT.XiFPaper.Mzk1DiagEmbeddingEquivActual.coordDual (p := p) (d := d) f : Set (d → ℚ_[p])) ≠ ⊤ :=
    hXc.measure_lt_top.ne
  exact canonical_diag_volume_ratio (p := p) (d := d) f hle hLc hLo hXc hXo hXpos hXtop

end LeanFormal.IUT.XiFPaper.Mzk1CanonicalDiagReduceActual
end