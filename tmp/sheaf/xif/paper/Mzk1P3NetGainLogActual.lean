import tmp.sheaf.xif.paper.Mzk1LatticeOrbitIndexActual
import Mathlib.Analysis.SpecialFunctions.Log.Basic
/-! P3 (R3.7): log form of the Haar index formula and the net quantity
`G - log h + corrections`. -/
noncomputable section
open MeasureTheory
namespace LeanFormal.IUT.XiFPaper.Mzk1P3NetGainLogActual
open LeanFormal.IUT.XiFPaper.Mzk1LatticeOrbitIndexActual
variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
variable [MeasurableSpace E] [BorelSpace E]
/-- Root-side gain: log of the bigger lattice mass minus log of the root mass. -/
def rootGain (μ : Measure E) (K Q : AddSubgroup E) : ℝ :=
  Real.log (μ (K : Set E)).toReal - Real.log (μ (Q : Set E)).toReal
/-- Net quantity `G - log h + corrections`. -/
def netQuantity (G : ℝ) (h : ℝ) (corrections : ℝ) : ℝ :=
  G - Real.log h + corrections
/-- A2 in logarithmic form: `log μ K = log index + log μ L`. -/
theorem log_measure_eq_log_index_add_log_measure
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    {L K : AddSubgroup E} (hLK : L ≤ K)
    (hLc : IsCompact (L : Set E)) (hLo : IsOpen (L : Set E))
    (hKc : IsCompact (K : Set E)) (hKo : IsOpen (K : Set E))
    (hLpos : μ (L : Set E) ≠ 0) (hLtop : μ (L : Set E) ≠ ⊤) :
    Real.log (μ (K : Set E)).toReal =
      Real.log (latticeIndex L K : ℝ) + Real.log (μ (L : Set E)).toReal := by
  have hμ := haar_measure_eq_index_mul_of_le μ hLK hLc hLo hKc hKo
  have hi : (latticeIndex L K : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr
      (ne_of_gt (LeanFormal.IUT.CompactOpenAddSubgroup.intersectionIndex_pos K L hKc hLo))
  have hL0 : (μ (L : Set E)).toReal ≠ 0 :=
    (ENNReal.toReal_pos hLpos hLtop).ne'
  rw [hμ, ENNReal.toReal_mul]
  exact Real.log_mul hi hL0
/-- `log μ L = log μ K - log index`. -/
theorem log_measure_eq_sub_log_index
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    {L K : AddSubgroup E} (hLK : L ≤ K)
    (hLc : IsCompact (L : Set E)) (hLo : IsOpen (L : Set E))
    (hKc : IsCompact (K : Set E)) (hKo : IsOpen (K : Set E))
    (hLpos : μ (L : Set E) ≠ 0) (hLtop : μ (L : Set E) ≠ ⊤) :
    Real.log (μ (L : Set E)).toReal =
      Real.log (μ (K : Set E)).toReal - Real.log (latticeIndex L K : ℝ) := by
  have h := log_measure_eq_log_index_add_log_measure μ hLK hLc hLo hKc hKo hLpos hLtop
  linarith
/-- Net quantity after substituting `G = rootGain μ K Q`, `h = latticeIndex L K`:
it becomes `log μ L - log μ Q + corrections`. -/
theorem netQuantity_rootGain_eq_log_measure_sub_add
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    {L K Q : AddSubgroup E} (hLK : L ≤ K)
    (hLc : IsCompact (L : Set E)) (hLo : IsOpen (L : Set E))
    (hKc : IsCompact (K : Set E)) (hKo : IsOpen (K : Set E))
    (hLpos : μ (L : Set E) ≠ 0) (hLtop : μ (L : Set E) ≠ ⊤)
    (corrections : ℝ) :
    netQuantity (rootGain μ K Q) (latticeIndex L K : ℝ) corrections =
      Real.log (μ (L : Set E)).toReal - Real.log (μ (Q : Set E)).toReal + corrections := by
  unfold netQuantity rootGain
  rw [log_measure_eq_sub_log_index μ hLK hLc hLo hKc hKo hLpos hLtop]
  ring
/-- The net quantity is nonnegative iff the source log-ratio comparison holds. -/
theorem netQuantity_nonneg_iff_sourceComparison
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    {L K Q : AddSubgroup E} (hLK : L ≤ K)
    (hLc : IsCompact (L : Set E)) (hLo : IsOpen (L : Set E))
    (hKc : IsCompact (K : Set E)) (hKo : IsOpen (K : Set E))
    (hLpos : μ (L : Set E) ≠ 0) (hLtop : μ (L : Set E) ≠ ⊤)
    (corrections : ℝ) :
    0 ≤ netQuantity (rootGain μ K Q) (latticeIndex L K : ℝ) corrections ↔
      0 ≤ Real.log (μ (L : Set E)).toReal - Real.log (μ (Q : Set E)).toReal + corrections := by
  rw [netQuantity_rootGain_eq_log_measure_sub_add μ hLK hLc hLo hKc hKo hLpos hLtop]
end LeanFormal.IUT.XiFPaper.Mzk1P3NetGainLogActual
end