import tmp.sheaf.xif.paper.S2568TateCoefficientNormActual
import Mathlib.Data.ZMod.Basic

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2568TateCoefficientNormActual

namespace LeanFormal.IUT.XiFPaper.S2569TateA6UnconditionalActual

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K]

/-- Integer coefficient of the unconditional a6 expansion. -/
def S2569a6Coeff (n : Nat) : Nat := (5 * n ^ 3 + 7 * n ^ 5) / 12

lemma S2569_twelve_dvd (n : Nat) : 12 ∣ 5 * n ^ 3 + 7 * n ^ 5 := by
  have h : ∀ x : ZMod 12, 5 * x ^ 3 + 7 * x ^ 5 = 0 := by decide
  refine (ZMod.natCast_eq_zero_iff _ 12).mp ?_
  push_cast
  exact h (n : ZMod 12)

lemma S2569_twelve_mul_coeff (n : Nat) :
    12 * S2569a6Coeff n = 5 * n ^ 3 + 7 * n ^ 5 :=
  Nat.mul_div_cancel' (S2569_twelve_dvd n)

lemma S2569_term_identity (q : K) (n : Nat) :
    5 * ((n : K) ^ 3 * q ^ n / (1 - q ^ n)) +
      7 * ((n : K) ^ 5 * q ^ n / (1 - q ^ n)) =
    12 * ((S2569a6Coeff n : K) * q ^ n / (1 - q ^ n)) := by
  have hcast : 5 * (n : K) ^ 3 + 7 * (n : K) ^ 5 =
      12 * (S2569a6Coeff n : K) := by
    have h : ((5 * n ^ 3 + 7 * n ^ 5 : Nat) : K) =
        ((12 * S2569a6Coeff n : Nat) : K) := by
      rw [S2569_twelve_mul_coeff]
    push_cast at h ⊢
    linear_combination h
  linear_combination (q ^ n / (1 - q ^ n)) * hcast

lemma S2569_summable_coeff (q : K) (hq : ‖q‖ < 1) :
    Summable fun n : Nat => (S2569a6Coeff n : K) * q ^ n / (1 - q ^ n) := by
  have hgeom : Summable fun n : Nat => ‖q‖ ^ n := by
    simpa using (summable_geometric_of_lt_one (norm_nonneg q) hq)
  refine Summable.of_norm_bounded hgeom ?_
  intro n
  by_cases hn : n = 0
  · subst n; simp [S2569a6Coeff]
  · rw [norm_div, norm_mul, norm_pow, S2568_norm_one_sub_qpow hq n (Nat.pos_of_ne_zero hn), div_one]
    have hqpow : ‖q‖ ^ n ≤ ‖q‖ :=
      pow_le_of_le_one (norm_nonneg q) hq.le hn
    calc ‖(S2569a6Coeff n : K)‖ * ‖q‖ ^ n
        ≤ 1 * ‖q‖ ^ n := by
          exact mul_le_mul (IsUltrametricDist.norm_natCast_le_one K _) le_rfl (by positivity) zero_le_one
      _ = ‖q‖ ^ n := one_mul _

theorem S2569_a6_eq_integer_tsum (q : K) (hq : ‖q‖ < 1) :
    TateCurve.a6 K q =
      -∑' n : Nat, (S2569a6Coeff n : K) * q ^ n / (1 - q ^ n) := by
  have h3 := TateCurve.lambertSeries_summable K 3 hq
  have h5 := TateCurve.lambertSeries_summable K 5 hq
  have hc := S2569_summable_coeff q hq
  have hcombo : 5 * TateCurve.lambertSeries K 3 q + 7 * TateCurve.lambertSeries K 5 q =
      12 * ∑' n : Nat, (S2569a6Coeff n : K) * q ^ n / (1 - q ^ n) := by
    rw [TateCurve.lambertSeries, TateCurve.lambertSeries]
    rw [← tsum_mul_left, ← tsum_mul_left, ← (h3.mul_left 5).tsum_add (h5.mul_left 7)]
    rw [← tsum_mul_left]
    exact tsum_congr fun n => S2569_term_identity q n
  unfold TateCurve.a6
  rw [hcombo]
  have h12 : (12 : K) ≠ 0 := by norm_num
  field_simp

theorem S2569_norm_a6_le_unconditional (q : K) (hq : ‖q‖ < 1) :
    ‖TateCurve.a6 K q‖ ≤ ‖q‖ := by
  rw [S2569_a6_eq_integer_tsum q hq, norm_neg]
  let F : Nat → K := fun n => (S2569a6Coeff n : K) * q ^ n / (1 - q ^ n)
  have hsum : HasSum F (∑' n : Nat, F n) := (S2569_summable_coeff q hq).hasSum
  refine S2568_norm_tsum_le_of_bound F (∑' n : Nat, F n) ‖q‖ (norm_nonneg q) hsum ?_
  intro n
  by_cases hn : n = 0
  · subst n
    have hc0 : S2569a6Coeff 0 = 0 := by decide
    dsimp [F]
    rw [hc0]
    simp
  · rw [norm_div, norm_mul, norm_pow, S2568_norm_one_sub_qpow hq n (Nat.pos_of_ne_zero hn), div_one]
    have hc : ‖(S2569a6Coeff n : K)‖ ≤ 1 :=
      IsUltrametricDist.norm_natCast_le_one K _
    have hqpow : ‖q‖ ^ n ≤ ‖q‖ :=
    pow_le_of_le_one (norm_nonneg q) hq.le hn
    calc ‖(S2569a6Coeff n : K)‖ * ‖q‖ ^ n
        ≤ 1 * ‖q‖ := mul_le_mul hc hqpow (by positivity) zero_le_one
      _ = ‖q‖ := one_mul _

#check S2569_norm_a6_le_unconditional
#print axioms S2569_norm_a6_le_unconditional
end LeanFormal.IUT.XiFPaper.S2569TateA6UnconditionalActual
end