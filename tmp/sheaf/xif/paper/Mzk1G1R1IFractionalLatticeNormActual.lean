/- R1 brick: norm bounds of the fractional lattice `{x | ‖x‖ ≤ p^{-a}}`, inputs for putting
`badPlaceQRegion` (fractional times holomorphic tensor lattice) into a per-place log region.
REUSE: `LeanFormal.IUT.LocalFieldLogarithm.mem_padicFractionalLattice_iff`,
`padicFractionalLattice_zero`, `padicFractionalLattice_antitone`
(`LeanFormal/IUT/Foundations/LocalFields/PadicFractionalLattice.lean:78,92,100`). -/
import LeanFormal.IUT.Foundations.LocalFields.PadicFractionalLattice
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1R1IFractionalLatticeNormActual
open LeanFormal.IUT.LocalFieldLogarithm

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {p : ℕ} [Fact p.Prime]
  [NormedAlgebra ℚ_[p] K]

/-- **Fractional-lattice norm bound**: a nonzero element of `padicFractionalLattice a` has
`log‖x‖ ≤ -a * log p`. -/
theorem padicFractionalLattice_log_norm_le (a : ℝ) (x : K) (hx0 : x ≠ 0)
    (hx : x ∈ padicFractionalLattice (p := p) (K := K) a) :
    Real.log ‖x‖ ≤ -a * Real.log (p : ℝ) := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : Nat.Prime p).one_lt
  have hp0 : (0 : ℝ) < (p : ℝ) := lt_trans one_pos hp1
  rw [mem_padicFractionalLattice_iff] at hx
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  calc Real.log ‖x‖ ≤ Real.log ((p : ℝ) ^ (-a)) := Real.log_le_log hxpos hx
    _ = -a * Real.log (p : ℝ) := by rw [Real.log_rpow hp0]

/-- A nonnegative-exponent fractional lattice sits inside the valuation-integer lattice. -/
theorem padicFractionalLattice_le_valuationInteger (a : ℝ) (ha : 0 ≤ a) :
    padicFractionalLattice (p := p) (K := K) a ≤
      valuationIntegerLattice (p := p) (K := K) := by
  rw [show valuationIntegerLattice (p := p) (K := K) =
      padicFractionalLattice (p := p) (K := K) 0 from
    (padicFractionalLattice_zero (p := p) (K := K)).symm]
  exact padicFractionalLattice_antitone (p := p) (K := K) ha

#print axioms padicFractionalLattice_log_norm_le
#print axioms padicFractionalLattice_le_valuationInteger
end LeanFormal.IUT.XiFPaper.Mzk1G1R1IFractionalLatticeNormActual
