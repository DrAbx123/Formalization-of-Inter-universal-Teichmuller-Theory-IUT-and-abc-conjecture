import tmp.sheaf.xif.paper.Mzk1DualIndexLinkActual

/-! CONDITIONAL: diagonal dual volume ratio for f-parameterisation (hq input). -/
noncomputable section
open MeasureTheory
namespace LeanFormal.IUT.XiFPaper.Mzk1DiagVolumeCondActual
open LeanFormal.IUT.XiFPaper.Mzk1DualIndexLinkActual
variable {p : Nat} [Fact p.Prime] {d : Type} [Fintype d] [DecidableEq d]
variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
variable [MeasurableSpace E] [BorelSpace E]
theorem diag_volume_ratio_f
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    {L X : AddSubgroup E} (hXL : X ≤ L)
    (hLc : IsCompact (L : Set E)) (hLo : IsOpen (L : Set E))
    (hXc : IsCompact (X : Set E)) (hXo : IsOpen (X : Set E))
    (hXpos : μ (X : Set E) ≠ 0) (hXtop : μ (X : Set E) ≠ ⊤)
    (f : d → Nat)
    (hq : Nat.card (L ⧸ X.comap L.subtype) = ∏ i, p ^ (f i)) :
    (μ (X : Set E)).toReal / (μ (L : Set E)).toReal =
      (∏ i, (p : ℝ) ^ (f i))⁻¹ :=
  dual_volume_ratio_of_quotient_cardinality (p := p) μ hXL hLc hLo hXc hXo
    hXpos hXtop f hq
end LeanFormal.IUT.XiFPaper.Mzk1DiagVolumeCondActual
end