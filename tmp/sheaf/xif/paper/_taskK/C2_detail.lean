import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
set_option maxHeartbeats 800000

-- @ G1|nlinarith
example (N l : ℝ) (hN : 0 ≤ N) (hl : 5 ≤ l) : N / (2*l) ≤ N := by nlinarith

-- @ G1|gcongr
example (N l : ℝ) (hN : 0 ≤ N) (hl : 5 ≤ l) : N / (2*l) ≤ N := by gcongr

-- @ G1|rw_div;nlinarith
example (N l : ℝ) (hN : 0 ≤ N) (hl : 5 ≤ l) : N / (2*l) ≤ N := by
  rw [div_le_iff₀ (by linarith : (0:ℝ) < 2*l)]
  nlinarith

-- @ G1|field_simp;nlinarith
example (N l : ℝ) (hN : 0 ≤ N) (hl : 5 ≤ l) : N / (2*l) ≤ N := by
  field_simp
  nlinarith

-- @ G2|rw_div;nlinarith
example (N l : ℝ) (hN : 0 ≤ N) (h2 : (1:ℝ) ≤ 2*l) (hpos : 0 < 2*l) : N / (2*l) ≤ N := by
  rw [div_le_iff₀ hpos]
  nlinarith

-- @ G2|gcongr
example (N l : ℝ) (hN : 0 ≤ N) (h2 : (1:ℝ) ≤ 2*l) (hpos : 0 < 2*l) : N / (2*l) ≤ N := by gcongr

-- @ G3|exact_lemma
example (p : ℝ) (hp : 1 < p) (a b : ℝ) (h : b ≤ a) : p^(-a) ≤ p^(-b) :=
  Real.rpow_le_rpow_of_exponent_le hp.le (neg_le_neg h)

-- @ G3|apply_lemma
example (p : ℝ) (hp : 1 < p) (a b : ℝ) (h : b ≤ a) : p^(-a) ≤ p^(-b) := by
  apply Real.rpow_le_rpow_of_exponent_le hp.le
  omega

-- @ G3|gcongr
example (p : ℝ) (hp : 1 < p) (a b : ℝ) (h : b ≤ a) : p^(-a) ≤ p^(-b) := by gcongr

-- @ G3|grind_hint
example (p : ℝ) (hp : 1 < p) (a b : ℝ) (h : b ≤ a) : p^(-a) ≤ p^(-b) := by
  grind [Real.rpow_le_rpow_of_exponent_le]

-- @ G4|lemma+nlinarith
example (p : ℝ) (hp : 1 < p) (N : ℝ) (hN : 0 ≤ N) (l : ℝ) (hl : 5 ≤ l) : p^(-(N/(2*l))) ≤ p^(-(N/(4*l))) := by
  apply Real.rpow_le_rpow_of_exponent_le hp.le
  rw [neg_le_neg_iff]
  exact div_le_div_of_nonneg_left hN (by positivity) (by nlinarith)

-- @ G4|gcongr
example (p : ℝ) (hp : 1 < p) (N : ℝ) (hN : 0 ≤ N) (l : ℝ) (hl : 5 ≤ l) : p^(-(N/(2*l))) ≤ p^(-(N/(4*l))) := by gcongr

-- @ G5|rw_add;ring
example (p : ℝ) (hp : 0 < p) (a b : ℝ) : p^(-(a+b)) = p^(-a) * p^(-b) := by
  rw [show -(a+b) = -a + -b by ring, Real.rpow_add hp]

-- @ G5|exact
example (p : ℝ) (hp : 0 < p) (a b : ℝ) : p^(-(a+b)) = p^(-a) * p^(-b) := by
  simpa [neg_add] using (Real.rpow_add hp (-a) (-b)).symm

-- @ G6|induction
example (k : ℕ) : (Finset.range k).sum (fun i => ((i:ℝ)+1)^2) = (k:ℝ)*((k:ℝ)+1)*(2*(k:ℝ)+1)/6 := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

-- @ G6|norm_num_only
example (k : ℕ) : (Finset.range k).sum (fun i => ((i:ℝ)+1)^2) = (k:ℝ)*((k:ℝ)+1)*(2*(k:ℝ)+1)/6 := by
  norm_num

-- @ G6|simp_only
example (k : ℕ) : (Finset.range k).sum (fun i => ((i:ℝ)+1)^2) = (k:ℝ)*((k:ℝ)+1)*(2*(k:ℝ)+1)/6 := by
  simp

-- @ G7|norm_num
example : (1/(14:ℝ)) * (∑ i : Fin 14, ((((i.1:ℝ)+1)^2) / (2*29))) = 5/4 := by norm_num

-- @ G7|norm_num_Fin_succ
example : (1/(14:ℝ)) * (∑ i : Fin 14, ((((i.1:ℝ)+1)^2) / (2*29))) = 5/4 := by
  norm_num [Fin.sum_univ_succ]

-- @ G7|simp_Fin_succ
example : (1/(14:ℝ)) * (∑ i : Fin 14, ((((i.1:ℝ)+1)^2) / (2*29))) = 5/4 := by
  simp [Fin.sum_univ_succ]
  norm_num

-- @ G7|l30_refute
example : ¬ ((1/(15:ℝ)) * (∑ i : Fin 15, ((((i.1:ℝ)+1)^2) / (2*31))) ≤ 1) := by
  norm_num [Fin.sum_univ_succ]

-- @ G10|exact_mod_cast
example (p : ℕ) [Fact (Nat.Prime p)] : (1:ℝ) < (p:ℝ) := by
  exact_mod_cast (Fact.out : Nat.Prime p).one_lt

-- @ G10|positivity
example (p : ℕ) [Fact (Nat.Prime p)] : (1:ℝ) < (p:ℝ) := by positivity

-- @ G10|norm_num
example (p : ℕ) [Fact (Nat.Prime p)] : (1:ℝ) < (p:ℝ) := by norm_num

-- @ G11|field_simp
example (N l : ℝ) (hl : l ≠ 0) : (N / (2*l)) * (2*l) = N := by
  field_simp

-- @ G11|field_simp;ring
example (N l : ℝ) (hl : l ≠ 0) : (N / (2*l)) * (2*l) = N := by
  field_simp; ring

-- @ G12|field_simp;ring
example (N l : ℝ) (hl : l ≠ 0) : N / (2*l) = N/2/l := by
  field_simp; ring

-- @ G13|exact
example (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) : Real.log a ≤ Real.log b :=
  Real.log_le_log ha hab

-- @ G13|gcongr
example (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) : Real.log a ≤ Real.log b := by gcongr

-- @ G13|grind_hint
example (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) : Real.log a ≤ Real.log b := by
  grind [Real.log_le_log]

-- @ G14|exact
example (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) : Real.log x ≤ 0 :=
  Real.log_nonpos hx hx1

-- @ G14|gcongr
example (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) : Real.log x ≤ 0 := by gcongr

