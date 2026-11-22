import tmp.sheaf.xif.paper.Mzk1DiagQuotCardActual
import tmp.sheaf.xif.paper.Mzk1DualIndexLinkActual

/-! CONDITIONAL: diagonal dual volume ratio via cardinal route (`hq` supplied
by the quotient/cardinal file), avoiding AddSubgroup/Submodule quotient typing. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1DiagVolumeProvedActual

open LeanFormal.IUT.XiFPaper.Mzk1DiagEmbeddingEquivActual
open LeanFormal.IUT.XiFPaper.Mzk1DiagQuotCardActual

open LeanFormal.IUT.XiFPaper.Mzk1DualIndexLinkActual

variable {p : Nat} [Fact p.Prime] {d : Type} [Fintype d] [DecidableEq d]

theorem natCard_addSubgroup_quot (f : d → Nat) :
    Nat.card ((Submodule.toAddSubgroup (coordSmall (p := p) (d := d)) : AddSubgroup (d → ℚ_[p])) ⧸
        (Submodule.toAddSubgroup (coordDual (p := p) (d := d) f)).comap
          (Submodule.toAddSubgroup (coordSmall (p := p) (d := d))).subtype) =
      ∏ i, p ^ (f i) := by
  change Nat.card (coordSmall (p := p) (d := d) ⧸
      (coordDual (p := p) (d := d) f).comap (coordSmall (p := p) (d := d)).subtype) =
    ∏ i, p ^ (f i)
  exact natCard_quotient_coordSmall (p := p) (d := d) f

theorem diagonal_volume_ratio_actual
    [MeasurableSpace (d → ℚ_[p])] [BorelSpace (d → ℚ_[p])]
    (μ : Measure (d → ℚ_[p])) [Measure.IsAddHaarMeasure μ]
    {f : d → Nat}
    (hle : coordDual (p := p) (d := d) f ≤ coordSmall (p := p) (d := d))
    (hLc : IsCompact (coordSmall (p := p) (d := d) : Set (d → ℚ_[p])))
    (hLo : IsOpen (coordSmall (p := p) (d := d) : Set (d → ℚ_[p])))
    (hXc : IsCompact (coordDual (p := p) (d := d) f : Set (d → ℚ_[p])))
    (hXo : IsOpen (coordDual (p := p) (d := d) f : Set (d → ℚ_[p])))
    (hXpos : μ (coordDual (p := p) (d := d) f : Set (d → ℚ_[p])) ≠ 0)
    (hXtop : μ (coordDual (p := p) (d := d) f : Set (d → ℚ_[p])) ≠ ⊤) :
    (μ (coordDual (p := p) (d := d) f : Set (d → ℚ_[p]))).toReal /
        (μ (coordSmall (p := p) (d := d) : Set (d → ℚ_[p]))).toReal =
      (∏ i, (p : ℝ) ^ (f i))⁻¹ := by
  have hle' : Submodule.toAddSubgroup (coordDual (p := p) (d := d) f) ≤
      Submodule.toAddSubgroup (coordSmall (p := p) (d := d)) :=
    hle
  exact dual_volume_ratio_of_quotient_cardinality μ hle' hLc hLo hXc hXo
    hXpos hXtop f (natCard_addSubgroup_quot (p := p) (d := d) f)

end LeanFormal.IUT.XiFPaper.Mzk1DiagVolumeProvedActual
end