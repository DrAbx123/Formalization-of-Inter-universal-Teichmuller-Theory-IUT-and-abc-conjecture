import tmp.sheaf.xif.paper.Mzk1LatticeOrbitIndexActual
import tmp.sheaf.xif.paper.Mzk1DualTransposeActual
import tmp.sheaf.xif.paper.Mzk1DiagonalIndexActual

/-!
# X_G dual index/volume link (conditional)

Conditional bridge between the X_G column-pairing form
(`Mzk1DualTransposeActual`) and the diagonal quotient cardinal
(`Mzk1DiagonalIndexActual`): if `X_G ⊆ L` are compact-open lattices and the
quotient `L / X_G` has the diagonal cardinal `∏ i, p^{e_i}`, then the actual
Haar volume ratio satisfies
`μ X_G / μ L = (∏ i, p^{e_i})^{-1}`
i.e. the dual-lattice volume is the inverse of the index cardinal.

No sorry/axiom; hypotheses `X` compact-open and the quotient cardinal are
explicit inputs (conditional version, as requested).
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.Mzk1DualIndexLinkActual

open LeanFormal.IUT.XiFPaper.Mzk1LatticeOrbitIndexActual

variable {p : ℕ} [Fact p.Prime]
variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
variable [MeasurableSpace E] [BorelSpace E]

/-- Conditional dual-volume ratio: for compact-open `X ≤ L` with finite quotient
cardinal `∏ i, p^{e_i}`, the Haar ratio is the inverse product. -/
theorem dual_volume_ratio_of_quotient_cardinality
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    {L X : AddSubgroup E} (hXL : X ≤ L)
    (hLc : IsCompact (L : Set E)) (hLo : IsOpen (L : Set E))
    (hXc : IsCompact (X : Set E)) (hXo : IsOpen (X : Set E))
    (hXpos : μ (X : Set E) ≠ 0) (hXtop : μ (X : Set E) ≠ ⊤)
    {d : Type*} [Fintype d] (e : d → ℕ)
    (hq : Nat.card (L ⧸ X.comap L.subtype) = ∏ i, p ^ (e i)) :
    (μ (X : Set E)).toReal / (μ (L : Set E)).toReal =
      (∏ i, (p : ℝ) ^ (e i))⁻¹ := by
  have hA := haar_measure_eq_index_mul_of_le μ hXL hXc hXo hLc hLo
  have hi : latticeIndex X L = ∏ i, p ^ (e i) := by
    change Nat.card (L ⧸ X.addSubgroupOf L) = ∏ i, p ^ (e i)
    exact hq
  have hLreal : (μ (L : Set E)).toReal =
      (latticeIndex X L : ℝ) * (μ (X : Set E)).toReal := by
    rw [hA, ENNReal.toReal_mul]
    simp only [ENNReal.toReal_natCast]
  have hX0 : (μ (X : Set E)).toReal ≠ 0 :=
    (ENNReal.toReal_pos hXpos hXtop).ne'
  rw [hLreal, hi, Nat.cast_prod]
  push_cast
  field_simp [hX0]

end LeanFormal.IUT.XiFPaper.Mzk1DualIndexLinkActual

end