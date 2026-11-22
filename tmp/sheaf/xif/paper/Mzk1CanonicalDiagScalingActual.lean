/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1CanonicalHaarCoordLatticeActual
import tmp.sheaf.xif.paper.Mzk1DiagVolumeProvedActual

/-! # Canonical diagonal volume ratio: conditional wrapper (task-109) -/
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 2000000
open MeasureTheory
open MeasureTheory.Measure
namespace LeanFormal.IUT.XiFPaper.Mzk1CanonicalDiagScalingActual
open LeanFormal.IUT.XiFPaper.Mzk1CanonicalHaarCoordLatticeActual
open LeanFormal.IUT.XiFPaper.Mzk1DiagVolumeProvedActual
variable {p : Nat} [Fact p.Prime] {d : Type} [Fintype d] [DecidableEq d]
variable [MeasurableSpace (d → ℚ_[p])] [BorelSpace (d → ℚ_[p])]
theorem canonical_diag_volume_ratio
    (f : d → Nat)
    (hle : LeanFormal.IUT.XiFPaper.Mzk1DiagEmbeddingEquivActual.coordDual (p := p) (d := d) f ≤
      LeanFormal.IUT.XiFPaper.Mzk1DiagEmbeddingEquivActual.coordSmall (p := p) (d := d))
    (hLc : IsCompact (LeanFormal.IUT.XiFPaper.Mzk1DiagEmbeddingEquivActual.coordSmall (p := p) (d := d) : Set (d → ℚ_[p])))
    (hLo : IsOpen (LeanFormal.IUT.XiFPaper.Mzk1DiagEmbeddingEquivActual.coordSmall (p := p) (d := d) : Set (d → ℚ_[p])))
    (hXc : IsCompact (LeanFormal.IUT.XiFPaper.Mzk1DiagEmbeddingEquivActual.coordDual (p := p) (d := d) f : Set (d → ℚ_[p])))
    (hXo : IsOpen (LeanFormal.IUT.XiFPaper.Mzk1DiagEmbeddingEquivActual.coordDual (p := p) (d := d) f : Set (d → ℚ_[p])))
    (hXpos : addHaarMeasure (coordinateCompacts (p := p) (d := d))
      (LeanFormal.IUT.XiFPaper.Mzk1DiagEmbeddingEquivActual.coordDual (p := p) (d := d) f : Set (d → ℚ_[p])) ≠ 0)
    (hXtop : addHaarMeasure (coordinateCompacts (p := p) (d := d))
      (LeanFormal.IUT.XiFPaper.Mzk1DiagEmbeddingEquivActual.coordDual (p := p) (d := d) f : Set (d → ℚ_[p])) ≠ ⊤) :
    (addHaarMeasure (coordinateCompacts (p := p) (d := d))
      (LeanFormal.IUT.XiFPaper.Mzk1DiagEmbeddingEquivActual.coordDual (p := p) (d := d) f : Set (d → ℚ_[p]))).toReal /
      (addHaarMeasure (coordinateCompacts (p := p) (d := d))
      (LeanFormal.IUT.XiFPaper.Mzk1DiagEmbeddingEquivActual.coordSmall (p := p) (d := d) : Set (d → ℚ_[p]))).toReal =
      (∏ i, (p : ℝ) ^ (f i))⁻¹ := by
  exact diagonal_volume_ratio_actual
    (addHaarMeasure (coordinateCompacts (p := p) (d := d))) hle hLc hLo hXc hXo hXpos hXtop
def canonicalDiagRows : List (String × String) :=
  [ ("canonical_diag_volume_ratio", "conditional wrapper"),
    ("unconditional hLc/hXpos", "GAP") ]
theorem canonicalDiagRows_length : canonicalDiagRows.length = 2 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1CanonicalDiagScalingActual
