import LeanFormal.IUT.Foundations.PAdicAnalytic.TateQSeriesCoefficients
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Analysis.Normed.Ring.InfiniteSum

open LeanFormal.IUT.PAdicAnalytic

set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.PAdicAnalytic

noncomputable section

local instance fivePrimeFactBridge : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

noncomputable def padicCoeffTerm (f : PowerSeries (PadicInt 5)) (q : ℚ_[5]) (n : ℕ) :
    ℚ_[5] :=
  (f.coeff n : ℚ_[5]) * q ^ n

noncomputable def padicEval (f : PowerSeries (PadicInt 5)) (q : ℚ_[5]) : ℚ_[5] :=
  ∑' n : ℕ, padicCoeffTerm f q n

lemma summable_norm_padicCoeffTerm (f : PowerSeries (PadicInt 5)) {q : ℚ_[5]}
    (hq : ‖q‖ < 1) : Summable fun n : ℕ => ‖padicCoeffTerm f q n‖ := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    (summable_geometric_of_lt_one (norm_nonneg q) hq)
  rw [padicCoeffTerm, norm_mul, norm_pow]
  have hc : ‖((f.coeff n : ℚ_[5]))‖ ≤ 1 := by
    simpa using PadicInt.norm_le_one (f.coeff n)
  calc
    ‖(f.coeff n : ℚ_[5])‖ * ‖q‖ ^ n ≤ 1 * ‖q‖ ^ n :=
      mul_le_mul_of_nonneg_right hc (pow_nonneg (norm_nonneg q) n)
    _ = ‖q‖ ^ n := one_mul _

lemma summable_padicCoeffTerm (f : PowerSeries (PadicInt 5)) {q : ℚ_[5]}
    (hq : ‖q‖ < 1) : Summable (padicCoeffTerm f q) :=
  (summable_norm_padicCoeffTerm f hq).of_norm

lemma padicEval_add (f g : PowerSeries (PadicInt 5)) {q : ℚ_[5]} (hq : ‖q‖ < 1) :
    padicEval (f + g) q = padicEval f q + padicEval g q := by
  rw [padicEval, padicEval, padicEval]
  rw [← (summable_padicCoeffTerm f hq).tsum_add (summable_padicCoeffTerm g hq)]
  apply tsum_congr
  intro n
  simp [padicCoeffTerm, add_mul]

lemma padicEval_neg (f : PowerSeries (PadicInt 5)) {q : ℚ_[5]} (hq : ‖q‖ < 1) :
    padicEval (-f) q = -padicEval f q := by
  rw [padicEval, padicEval]
  rw [show (∑' n : ℕ, padicCoeffTerm (-f) q n) =
      ∑' n : ℕ, -padicCoeffTerm f q n by
    apply tsum_congr
    intro n
    simp [padicCoeffTerm, neg_mul]]
  rw [tsum_neg]

lemma padicEval_one {q : ℚ_[5]} (hq : ‖q‖ < 1) :
    padicEval (1 : PowerSeries (PadicInt 5)) q = 1 := by
  rw [padicEval]
  have h : ∀ b : ℕ, b ≠ 0 → padicCoeffTerm (1 : PowerSeries (PadicInt 5)) q b = 0 := by
    intro b hb
    simp [padicCoeffTerm, hb]
  rw [tsum_eq_single 0 h]
  simp [padicCoeffTerm]

lemma padicEval_C (c : PadicInt 5) {q : ℚ_[5]} (hq : ‖q‖ < 1) :
    padicEval (PowerSeries.C c) q = (c : ℚ_[5]) := by
  rw [padicEval]
  have h : ∀ b : ℕ, b ≠ 0 → padicCoeffTerm (PowerSeries.C c) q b = 0 := by
    intro b hb
    rw [padicCoeffTerm, PowerSeries.coeff_C, if_neg hb]
    simp
  rw [tsum_eq_single 0 h]
  simp [padicCoeffTerm]

lemma padicEval_mul (f g : PowerSeries (PadicInt 5)) {q : ℚ_[5]} (hq : ‖q‖ < 1) :
    padicEval (f * g) q = padicEval f q * padicEval g q := by
  rw [padicEval, padicEval, padicEval]
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
    (f := padicCoeffTerm f q) (g := padicCoeffTerm g q)
    (summable_norm_padicCoeffTerm f hq) (summable_norm_padicCoeffTerm g hq)]
  apply tsum_congr
  intro n
  rw [padicCoeffTerm, PowerSeries.coeff_mul]
  change PadicInt.Coe.ringHom
      (∑ p ∈ Finset.antidiagonal n, (f.coeff p.1) * (g.coeff p.2)) * q ^ n =
    ∑ kl ∈ Finset.antidiagonal n, padicCoeffTerm f q kl.1 * padicCoeffTerm g q kl.2
  rw [map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  rintro ⟨i, j⟩ hij
  rw [padicCoeffTerm, padicCoeffTerm]
  have hmem : i + j = n := Finset.mem_antidiagonal.mp hij
  change ((f.coeff i : ℚ_[5]) * (g.coeff j : ℚ_[5])) * q ^ n =
    ((f.coeff i : ℚ_[5]) * q ^ i) * ((g.coeff j : ℚ_[5]) * q ^ j)
  rw [← hmem, pow_add]
  ring

end
end LeanFormal.IUT.PAdicAnalytic
