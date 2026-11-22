import tmp.sheaf.xif.paper.Mzk1CanonicalDiagReduceActual

/-! B4 GAP marker + conditional compact/open wrapper.

The image bridge `diagHomeo f '' coordSmall = coordDual` and its
compact/open consequences are the remaining exact GAP (see
`Mzk1DiagEquivBridgeActual`); the conditional compact/open form is green
in `Mzk1CanonicalDiagReduceActual`. -/
noncomputable section
open scoped BigOperators
open MeasureTheory MeasureTheory.Measure
namespace LeanFormal.IUT.XiFPaper.Mzk1CanonicalDiagUncondActual
open LeanFormal.IUT.XiFPaper.Mzk1CanonicalHaarCoordLatticeActual
open LeanFormal.IUT.XiFPaper.Mzk1CanonicalDiagReduceActual
variable {p : Nat} [Fact p.Prime] {d : Type} [Fintype d] [DecidableEq d]
variable [MeasurableSpace (d → ℚ_[p])] [BorelSpace (d → ℚ_[p])]

theorem canonical_diag_volume_ratio_compact_open
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
      (∏ i, (p : ℝ) ^ (f i))⁻¹ :=
  canonical_diag_volume_ratio_reduced (p := p) (d := d) f hle hLc hLo hXc hXo

end LeanFormal.IUT.XiFPaper.Mzk1CanonicalDiagUncondActual
end