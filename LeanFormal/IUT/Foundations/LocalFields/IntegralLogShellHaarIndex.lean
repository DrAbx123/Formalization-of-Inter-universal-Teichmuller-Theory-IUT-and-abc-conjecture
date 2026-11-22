import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellIntegerQuotient
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The actual log-shell's Haar discrepancy from valuation integers

The shell quotient by O is finite by the preceding construction. The
existing subgroup-index measure formula, applied to the Haar measure
pulled back to this open shell, gives its exact mass. Its relative
logarithm is the logarithm of the actual finite index, equivalently the
log congruence-quotient order minus the log torsion-unit order.
-/

namespace LeanFormal.IUT.LocalFieldLogarithm

open LeanFormal.IUT.LocalFieldIntegralUnits MeasureTheory

noncomputable section

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [ProperSpace K]
variable [MeasurableSpace K]

theorem measure_localIntegers_pos_lt_top (μ : Measure K) [Measure.IsAddHaarMeasure μ] :
    0 < μ (Integers K : Set K) ∧ μ (Integers K : Set K) < ⊤ := by
  have hcompact : IsCompact (Integers K : Set K) := by
    have heq : (Integers K : Set K) = Metric.closedBall (0 : K) 1 := by
      ext x
      change (‖x‖ ≤ 1) ↔ dist x 0 ≤ 1
      simp only [dist_eq_norm, sub_zero]
    rw [heq]
    exact isCompact_closedBall (0 : K) 1
  have hzero : (0 : K) ∈ interior (Integers K : Set K) := by
    apply mem_interior_iff_mem_nhds.mpr
    apply Filter.mem_of_superset (Metric.ball_mem_nhds (0 : K) zero_lt_one)
    intro x hx
    exact (mem_integers_iff x).mpr ((show ‖x‖ < 1 by simpa using hx).le)
  exact ⟨Measure.measure_pos_of_nonempty_interior μ ⟨0, hzero⟩, hcompact.measure_lt_top⟩

variable [CharZero K] [CompleteSpace K] [BorelSpace K]
variable {p : ℕ} [Fact p.Prime] [localNormedAlgebra : NormedAlgebra ℚ_[p] K]

omit [BorelSpace K] in
theorem measure_integralLogShell_pos_lt_top (μ : Measure K) [Measure.IsAddHaarMeasure μ] :
    0 < μ (integralLogShell (K := K) (p := p) : Set K) ∧
      μ (integralLogShell (K := K) (p := p) : Set K) < ⊤ :=
  ⟨(measure_localIntegers_pos_lt_top μ).1.trans_le
    (measure_mono (integers_subset_integralLogShell (K := K) (p := p))),
    (isCompact_integralLogShell (K := K) (p := p)).measure_lt_top⟩

theorem measure_integralLogShell_eq_index_mul (μ : Measure K) [Measure.IsAddHaarMeasure μ] :
    μ (integralLogShell (K := K) (p := p) : Set K) =
      (logShellIntegerIndex (K := K) (p := p) : ENNReal) * μ (Integers K : Set K) := by
  let shell := integralLogShell (K := K) (p := p)
  let shellMeasure := μ.comap (shell.subtype : shell → K)
  have hopen : Topology.IsOpenEmbedding (shell.subtype : shell → K) :=
    (isOpen_integralLogShell (K := K) (p := p)).isOpenEmbedding_subtypeVal
  letI : Measure.IsAddHaarMeasure shellMeasure :=
    Measure.IsAddHaarMeasure.comap (mH := inferInstance) μ hopen
  letI : (logShellIntegerSubgroup (K := K) (p := p)).FiniteIndex := ⟨by
    rw [AddSubgroup.index_eq_card]
    exact (logShellIntegerIndex_pos (K := K) (p := p)).ne'⟩
  have hmeasure (S : Set shell) : shellMeasure S = μ (shell.subtype '' S) :=
    hopen.measurableEmbedding.comap_apply μ S
  have hintegers : shell.subtype ''
      (logShellIntegerSubgroup (K := K) (p := p) : Set shell) = (Integers K : Set K) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, integers_subset_integralLogShell (K := K) (p := p) hx⟩, hx, rfl⟩
  have hwhole : shell.subtype '' (Set.univ : Set shell) = (shell : Set K) := by
    ext x
    constructor
    · rintro ⟨y, _, rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x, hx⟩, Set.mem_univ _, rfl⟩
  have hindex := MeasureTheory.AddSubgroup.index_mul_measure
    (logShellIntegerSubgroup (K := K) (p := p))
    (isOpen_logShellIntegerSubgroup (K := K) (p := p)).measurableSet shellMeasure
  simp only [hmeasure, hintegers, hwhole, AddSubgroup.index_eq_card] at hindex
  exact hindex.symm

def integralLogShellDiscrepancy : ℝ := Real.log (logShellIntegerIndex (K := K) (p := p) : ℝ)

theorem integralLogShellDiscrepancy_eq_relativeHaarLog
    (μ : Measure K) [Measure.IsAddHaarMeasure μ] :
    integralLogShellDiscrepancy (K := K) (p := p) =
      Real.log (μ (integralLogShell (K := K) (p := p) : Set K)).toReal -
        Real.log (μ (Integers K : Set K)).toReal := by
  rw [measure_integralLogShell_eq_index_mul (p := p)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast]
  have hindex : (logShellIntegerIndex (K := K) (p := p) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (logShellIntegerIndex_pos (K := K) (p := p)).ne'
  have hmass := measure_localIntegers_pos_lt_top μ
  rw [Real.log_mul hindex (ENNReal.toReal_pos hmass.1.ne' hmass.2.ne).ne']
  unfold integralLogShellDiscrepancy
  ring

omit [MeasurableSpace K] [BorelSpace K] in
theorem integralLogShellDiscrepancy_nonneg : 0 ≤ integralLogShellDiscrepancy (K := K) (p := p) := by
  apply Real.log_nonneg
  exact_mod_cast Nat.succ_le_of_lt (logShellIntegerIndex_pos (K := K) (p := p))

omit [MeasurableSpace K] [BorelSpace K] in
theorem integralLogShellDiscrepancy_eq_log_congruence_sub_log_torsion :
    integralLogShellDiscrepancy (K := K) (p := p) =
      Real.log (Nat.card ((Integers K)ˣ ⧸ logShellCongruenceUnits (K := K) (p := p)) : ℝ) -
        Real.log (Nat.card (CommGroup.torsion (Integers K)ˣ) : ℝ) := by
  letI := finite_integralUnitTorsion (K := K) (p := p)
  have htorsion : (Nat.card (CommGroup.torsion (Integers K)ˣ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hindex : (logShellIntegerIndex (K := K) (p := p) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (logShellIntegerIndex_pos (K := K) (p := p)).ne'
  have hcard :
      (Nat.card ((Integers K)ˣ ⧸ logShellCongruenceUnits (K := K) (p := p)) : ℝ) =
        (Nat.card (CommGroup.torsion (Integers K)ˣ) : ℝ) *
          (logShellIntegerIndex (K := K) (p := p) : ℝ) := by
    exact_mod_cast card_logShellCongruenceQuotient (K := K) (p := p)
  rw [hcard, Real.log_mul htorsion hindex]
  unfold integralLogShellDiscrepancy
  ring

end

end LeanFormal.IUT.LocalFieldLogarithm
