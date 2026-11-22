import tmp.sheaf.n8.closure.EtaGaussianActionVolumeNontrivial
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicHaarScaling
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellHaarIndex
import Mathlib

/-!
# Rank-one Gaussian action-volume actual witness

Rank-one actual block: K = Q_p.  The group element is the actual nontrivial
p-adic unit g = p, the set is the actual integral unit ball S = Z_p, and the
action is scalar multiplication by g.  The production p-scaling theorem
FinitePadicHaarScaling.log_measure_prime_smul_finiteDimensional proves

  nu(g S) - nu(S) = log ||g||_p / 1 = - log p.

This is a non-PUnit actual witness of the volume identity at a nontrivial g.
The full Q_p^-action for every unit still needs the general unit-scaling
theorem; that is the exact remaining gap.
-/

noncomputable section

namespace ABCBridge.N8.EtaGaussianActionVolumeRankOneActual

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldLogarithm

universe u

/-- The actual p-adic norm-log on units. -/
noncomputable def pAdicUnitLogNorm {p : ℕ} [Fact p.Prime] (g : ℚ_[p]ˣ) : ℝ :=
  Real.log ‖(g : ℚ_[p])‖

/-- Actual rank-one Gaussian volume witness at g = p and S = Z_p. -/
structure RankOneGaussianVolumeActual (p : ℕ) [Fact p.Prime] where
  g : ℚ_[p]ˣ
  g_field : (g : ℚ_[p]) = (p : ℚ_[p])
  g_ne_one : g ≠ 1
  S : Set ℚ_[p]
  S_eq : S = (Integers ℚ_[p] : Set ℚ_[p])
  measurable_S : MeasurableSet S
  pos_S : 0 < Measure.addHaar S
  finite_S : Measure.addHaar S < ⊤
  d_j : ℝ
  d_j_eq_one : d_j = 1
  volume_formula :
    Real.log (Measure.addHaar ((g : ℚ_[p]) • S)).toReal -
        Real.log (Measure.addHaar S).toReal = pAdicUnitLogNorm g / d_j

/-- Actual witness construction, zero sorry. -/
noncomputable def rankOneGaussianVolumeActual (p : ℕ) [Fact p.Prime] :
    RankOneGaussianVolumeActual p where
  g := Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime p).ne_zero)
  g_field := rfl
  g_ne_one := by
    intro hg
    have hnorm : ‖((Units.mk0 (p : ℚ_[p])
        (Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime p).ne_zero) : ℚ_[p]))‖ = 1 := by
      rw [show ((Units.mk0 (p : ℚ_[p])
          (Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime p).ne_zero) : ℚ_[p])) = 1 by
        simpa using congrArg (fun u : ℚ_[p]ˣ => (u : ℚ_[p])) hg]
      simp
    have hlt := Padic.norm_p_lt_one (p := p) (Fact.out : Nat.Prime p)
    rw [Padic.norm_p (p := p) (Fact.out : Nat.Prime p).one_lt] at hnorm
    rw [hnorm] at hlt
    norm_num at hlt
  S := (Integers ℚ_[p] : Set ℚ_[p])
  S_eq := rfl
  measurable_S := by
    rw [show (Integers ℚ_[p] : Set ℚ_[p]) = Metric.closedBall (0 : ℚ_[p]) 1 from by
      ext x
      change (‖x‖ ≤ 1) ↔ dist x 0 ≤ 1
      simp only [dist_eq_norm, sub_zero]]
    exact Metric.isClosed_closedBall.measurableSet
  pos_S := (measure_localIntegers_pos_lt_top (Measure.addHaar : Measure ℚ_[p])).1
  finite_S := (measure_localIntegers_pos_lt_top (Measure.addHaar : Measure ℚ_[p])).2
  d_j := 1
  d_j_eq_one := rfl
  volume_formula := by
    have hpos := (measure_localIntegers_pos_lt_top (Measure.addHaar : Measure ℚ_[p])).1
    have hfin := (measure_localIntegers_pos_lt_top (Measure.addHaar : Measure ℚ_[p])).2
    have h := FinitePadicHaarScaling.log_measure_prime_smul_finiteDimensional
      (p := p) (M := ℚ_[p]) (μ := (Measure.addHaar : Measure ℚ_[p]))
      (S := (Integers ℚ_[p] : Set ℚ_[p])) hpos hfin
    simpa [pAdicUnitLogNorm, Padic.norm_p, Real.log_inv, Module.finrank_self] using h

/-- The rank-one witness has nontrivial g and the volume identity at that g. -/
theorem rankOneGaussianVolumeActual_nonvacuous (p : ℕ) [Fact p.Prime] :
    ∃ W : RankOneGaussianVolumeActual p,
      W.g_ne_one ∧
        Real.log (Measure.addHaar ((W.g : ℚ_[p]) • W.S)).toReal -
          Real.log (Measure.addHaar W.S).toReal = pAdicUnitLogNorm W.g / W.d_j :=
  ⟨rankOneGaussianVolumeActual p, (rankOneGaussianVolumeActual p).g_ne_one,
    (rankOneGaussianVolumeActual p).volume_formula⟩

end ABCBridge.N8.EtaGaussianActionVolumeRankOneActual
