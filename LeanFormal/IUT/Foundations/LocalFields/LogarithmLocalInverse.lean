import LeanFormal.IUT.Foundations.LocalFields.LogarithmRemainder
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithm
import Mathlib.Topology.MetricSpace.Contracting

/-!
# A local inverse and the actual integer-ring inclusion in the log-shell

Banach contraction on the closed ball constructs an inverse of the actual
logarithm series. Applying it to `(p*) x` for integral x proves the source
inclusion in IUT III Remark 1.2.2(i). No inverse or inclusion is supplied
as an uninhabited interface obligation.
-/

namespace LeanFormal.IUT.LocalFieldLogarithm

open LeanFormal.IUT.LocalFieldIntegralUnits
open scoped NNReal

noncomputable section

variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
variable [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [localNormedAlgebra : NormedAlgebra ℚ_[p] K]

include localNormedAlgebra

/-- Construct an actual preimage of each point of a sufficiently small
closed ball under the analytic logarithm. -/
theorem exists_log1p_preimage {r : ℝ} (hr : 0 ≤ r) (hrhalf : r < 1 / 2)
    (y : K) (hy : ‖y‖ ≤ r) : ∃ x : K, ‖x‖ ≤ r ∧ log1p x = y := by
  let B := {x : K // ‖x‖ ≤ r}
  have hclosed : IsClosed {x : K | ‖x‖ ≤ r} :=
    isClosed_le continuous_norm continuous_const
  letI : CompleteSpace B := hclosed.isComplete.completeSpace_coe
  letI : Nonempty B := ⟨⟨0, by simpa using hr⟩⟩
  have hzero : logRemainder (0 : K) = 0 := by simp [logRemainder, log1p_zero]
  have hrem : ∀ x : B, ‖logRemainder (x : K)‖ ≤ r := by
    intro x
    have h := norm_logRemainder_sub_le (p := p) (x : K) 0 hr hrhalf.le x.property
      (by simpa using hr)
    rw [hzero, sub_zero, sub_zero] at h
    exact h.trans ((mul_le_of_le_one_left (norm_nonneg _) (by linarith)).trans x.property)
  let F : B → B := fun x => ⟨y - logRemainder (x : K), by
    apply le_trans _ (max_le hy (hrem x))
    simpa only [sub_eq_add_neg, norm_neg] using
      IsUltrametricDist.norm_add_le_max y (-logRemainder (x : K))⟩
  let c : ℝ≥0 := ⟨2 * r, by positivity⟩
  have hlip : LipschitzWith c F := by
    apply LipschitzWith.of_dist_le_mul
    intro x z
    change dist (y - logRemainder (x : K)) (y - logRemainder (z : K)) ≤
      (2 * r) * dist (x : K) (z : K)
    rw [dist_eq_norm, dist_eq_norm]
    have heq : (y - logRemainder (x : K)) - (y - logRemainder (z : K)) =
        -(logRemainder (x : K) - logRemainder (z : K)) := by ring
    rw [heq, norm_neg]
    exact norm_logRemainder_sub_le (p := p) _ _ hr hrhalf.le x.property z.property
  have hcontract : ContractingWith c F := ⟨by change 2 * r < 1; linarith, hlip⟩
  let x := hcontract.fixedPoint F
  have hfixed : F x = x := hcontract.fixedPoint_isFixedPt
  have heq : y - logRemainder (x : K) = (x : K) := congrArg Subtype.val hfixed
  refine ⟨x, x.property, ?_⟩
  dsimp [logRemainder] at heq
  linear_combination -heq

omit localNormedAlgebra [CharZero K] [CompleteSpace K] in
/-- Small offsets of one are actual integral units. -/
theorem norm_one_add_of_norm_lt_one (x : K) (hx : ‖x‖ < 1) : ‖1 + x‖ = 1 := by
  have hne : ‖(1 : K)‖ ≠ ‖x‖ := by simpa only [norm_one] using ne_of_gt hx
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_one, max_eq_left hx.le]

omit [CharZero K] [CompleteSpace K] [IsUltrametricDist K] in
/-- The precise source factor p* is small enough for the proved inverse,
including the exceptional choice p*=4 at p=2. -/
theorem norm_logShellScale_lt_half : ‖(logShellScale p : K)‖ < 1 / 2 := by
  have hpnorm : ‖(p : K)‖ = (p : ℝ)⁻¹ := by
    calc
      _ = ‖(p : ℚ_[p])‖ := by
        simpa only [map_natCast] using norm_algebraMap' K (p : ℚ_[p])
      _ = _ := Padic.norm_p
  by_cases htwo : p = 2
  · rw [logShellScale, if_pos htwo, Nat.cast_pow, norm_pow, hpnorm, htwo]
    norm_num
  · rw [logShellScale, if_neg htwo, hpnorm, inv_eq_one_div]
    have hp : 2 < p := by
      have hpmin : 2 ≤ p := (Fact.out : p.Prime).two_le
      omega
    apply (div_lt_div_iff₀ (Nat.cast_pos.mpr (Fact.out : p.Prime).pos) (by norm_num)).mpr
    simpa only [one_mul] using (show (2 : ℝ) < (p : ℝ) by exact_mod_cast hp)

omit localNormedAlgebra [CharZero K] [CompleteSpace K] [IsUltrametricDist K] in
theorem logShellScale_pos : 0 < logShellScale p := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  unfold logShellScale
  split_ifs <;> positivity

variable [ProperSpace K]

/-- The actual logarithm of full units surjects onto p* times the integer
ring, with an actual principal-unit preimage. -/
theorem exists_unitLog_eq_scale_mul (x : Integers K) :
    ∃ u : (Integers K)ˣ, u ∈ principalUnits ∧
      unitLog u = (logShellScale p : K) * (x : K) := by
  have hrhalf := norm_logShellScale_lt_half (K := K) (p := p)
  have hy : ‖(logShellScale p : K) * (x : K)‖ ≤ ‖(logShellScale p : K)‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) ((mem_integers_iff _).mp x.property)
  obtain ⟨t, ht, hlog⟩ := exists_log1p_preimage (p := p) (norm_nonneg _) hrhalf _ hy
  have htone : ‖t‖ < 1 := ht.trans_lt (hrhalf.trans (by norm_num))
  let u := unitOfNormOne (K := K) ⟨1 + t, norm_one_add_of_norm_lt_one t htone⟩
  have hoffset : (u.val : K) - 1 = t := by change (1 + t) - 1 = t; ring
  have hu : u ∈ principalUnits := by
    apply (mem_principalUnits_iff _).mpr
    rw [hoffset]
    exact htone
  exact ⟨u, hu, by rw [unitLog_eq_log1p (p := p) u hu, hoffset, hlog]⟩

/-- The source integer ring is contained in the constructed log-shell;
this is a theorem about the analytic image, not an interface hypothesis. -/
theorem integers_subset_integralLogShell :
    (Integers K : Set K) ⊆ (integralLogShell (K := K) (p := p) : Set K) := by
  intro x hx
  obtain ⟨u, _, hu⟩ := exists_unitLog_eq_scale_mul (p := p) (⟨x, hx⟩ : Integers K)
  change ∃ u : (Integers K)ˣ, (logShellScale p : K)⁻¹ * unitLog u = x
  refine ⟨u, ?_⟩
  rw [hu]
  have hscale : (logShellScale p : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt (logShellScale_pos (p := p)))
  exact inv_mul_cancel_left₀ hscale x

end

end LeanFormal.IUT.LocalFieldLogarithm
