import Mathlib

noncomputable section

namespace LeanFormal.IUT.XiFPaper.QBinomialCommRing

universe u

variable {K : Type u} [CommRing K]

noncomputable def qBinom : Nat -> Nat -> K -> K
  | 0, 0, _ => 1
  | 0, _ + 1, _ => 0
  | N + 1, 0, q => qBinom N 0 q
  | N + 1, k + 1, q => qBinom N (k + 1) q + q ^ (N - k) * qBinom N k q

theorem qBinom_succ_zero (N : Nat) (q : K) :
    qBinom (N + 1) 0 q = qBinom N 0 q := by
  rw [qBinom]

theorem qBinom_succ_succ (N k : Nat) (q : K) :
    qBinom (N + 1) (k + 1) q =
      qBinom N (k + 1) q + q ^ (N - k) * qBinom N k q := by
  rw [qBinom]

theorem qBinom_eq_zero_of_lt {N k : Nat} (q : K) (h : k > N) :
    qBinom N k q = 0 := by
  induction N generalizing k with
  | zero =>
      cases k with
      | zero => omega
      | succ k => rw [qBinom]
  | succ N ih =>
      cases k with
      | zero => omega
      | succ k =>
          rw [qBinom]
          have h1 : qBinom N (k + 1) q = 0 := ih (by omega)
          have h2 : qBinom N k q = 0 := ih (by omega)
          simp [h1, h2]

theorem qBinom_self_succ (N : Nat) (q : K) :
    qBinom N (N + 1) q = 0 :=
  qBinom_eq_zero_of_lt q (by omega)

noncomputable def qBinoTermC (N k : Nat) (q z : K) : K :=
  q ^ (Nat.choose k 2) * qBinom N k q * z ^ k

def qBinomialTheoremTarget (N : Nat) (q z : K) : Prop :=
  Finset.prod (Finset.range N) (fun m : Nat => (1 : K) + z * q ^ m) =
    Finset.sum (Finset.range (N + 1)) (fun k : Nat =>
      q ^ (k * (k - 1) / 2) * qBinom N k q * z ^ k)

theorem sum_range_Icc_shift (f : Nat -> K) (N : Nat) :
    Finset.sum (Finset.range N) f =
      Finset.sum (Finset.Icc 1 N) (fun j : Nat => f (j - 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      rw [Finset.sum_Icc_succ_top (by omega)]
      simp

theorem qBinoTermC_succ (N k : Nat) (q z : K) :
    qBinoTermC N (k + 1) q z +
        qBinoTermC N k q z * (z * q ^ N) =
      qBinoTermC (N + 1) (k + 1) q z := by
  by_cases hk : k <= N
  · have hchoose : Nat.choose (k + 1) 2 = Nat.choose k 2 + k := by
      have := Nat.choose_succ_succ k 1
      simpa [Nat.choose_one_right, add_comm] using this
    have hrec := qBinom_succ_succ N k q
    have hpow : q ^ (Nat.choose (k + 1) 2) * q ^ (N - k) =
        q ^ (Nat.choose k 2) * q ^ N := by
      rw [← pow_add, ← pow_add]
      congr 1
      rw [hchoose]
      omega
    unfold qBinoTermC
    rw [hrec]
    calc
      q ^ (Nat.choose (k + 1) 2) * qBinom N (k + 1) q * z ^ (k + 1) +
          q ^ (Nat.choose k 2) * qBinom N k q * z ^ k * (z * q ^ N)
        = q ^ (Nat.choose (k + 1) 2) * qBinom N (k + 1) q * z ^ (k + 1) +
            (q ^ (Nat.choose k 2) * q ^ N) * qBinom N k q * z ^ (k + 1) := by ring
      _ = q ^ (Nat.choose (k + 1) 2) * qBinom N (k + 1) q * z ^ (k + 1) +
            (q ^ (Nat.choose (k + 1) 2) * q ^ (N - k)) * qBinom N k q * z ^ (k + 1) := by rw [hpow]
      _ = q ^ (Nat.choose (k + 1) 2) *
            (qBinom N (k + 1) q + q ^ (N - k) * qBinom N k q) * z ^ (k + 1) := by ring
  · have hk' : N < k := by omega
    have h1 : qBinom N (k + 1) q = 0 :=
      qBinom_eq_zero_of_lt q (by omega)
    have h2 : qBinom N k q = 0 :=
      qBinom_eq_zero_of_lt q hk'
    have h3 : qBinom (N + 1) (k + 1) q = 0 :=
      qBinom_eq_zero_of_lt q (by omega)
    unfold qBinoTermC
    simp [h1, h2, h3]

theorem qBinomial_sum_step (N : Nat) (q z : K) :
    (Finset.sum (Finset.range (N + 1)) (fun k : Nat =>
        qBinoTermC N k q z)) * (1 + z * q ^ N) =
      Finset.sum (Finset.range (N + 2)) (fun k : Nat =>
        qBinoTermC (N + 1) k q z) := by
  let f : Nat -> K := fun k => qBinoTermC N k q z
  let h : Nat -> K := fun k => qBinoTermC (N + 1) k q z
  have h0 : h 0 = f 0 := by
    simp [f, h, qBinoTermC, qBinom_succ_zero]
  have hchoose : Nat.choose (N + 1) 2 = Nat.choose N 2 + N := by
    have := Nat.choose_succ_succ N 1
    simpa [Nat.choose_one_right, add_comm] using this
  have hN : h (N + 1) = f N * (z * q ^ N) := by
    have hq : qBinom (N + 1) (N + 1) q = qBinom N N q := by
      rw [qBinom_succ_succ]
      simp [qBinom_self_succ]
    simp only [h, f, qBinoTermC]
    rw [hq, hchoose]
    ring
  have hterm : forall k : Nat, k < N ->
      h (k + 1) = f (k + 1) + f k * (z * q ^ N) := by
    intro k hk
    exact (qBinoTermC_succ N k q z).symm
  rw [mul_add, mul_one]
  rw [Finset.sum_mul]
  conv_lhs => arg 1; rw [Finset.sum_range_succ']
  conv_lhs => arg 2; rw [Finset.sum_range_succ]
  conv_rhs => rw [Finset.sum_range_succ']
  conv_rhs => arg 1; rw [Finset.sum_range_succ]
  have hsum : Finset.sum (Finset.range N) (fun k => h (k + 1)) =
      Finset.sum (Finset.range N) (fun k => f (k + 1) + f k * (z * q ^ N)) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact hterm k (Finset.mem_range.mp hk)
  change (Finset.sum (Finset.range N) (fun k => f (k + 1))) + f 0 +
      ((Finset.sum (Finset.range N) (fun k => f k * (z * q ^ N))) +
        f N * (z * q ^ N)) =
    (Finset.sum (Finset.range N) (fun k => h (k + 1))) +
      h (N + 1) + h 0
  rw [hsum, hN, h0, Finset.sum_add_distrib]
  ring

theorem qBinomialTheoremChoose (N : Nat) (q z : K) :
    Finset.prod (Finset.range N) (fun m : Nat => (1 : K) + z * q ^ m) =
      Finset.sum (Finset.range (N + 1)) (fun k : Nat =>
        qBinoTermC N k q z) := by
  induction N with
  | zero => simp [qBinoTermC, qBinom]
  | succ N ih =>
      rw [Finset.prod_range_succ, ih]
      exact qBinomial_sum_step N q z

theorem qBinomialTheorem (N : Nat) (q z : K) :
    qBinomialTheoremTarget N q z := by
  unfold qBinomialTheoremTarget
  rw [qBinomialTheoremChoose N q z]
  apply Finset.sum_congr rfl
  intro k hk
  unfold qBinoTermC
  rw [← Nat.choose_two_right k]

end LeanFormal.IUT.XiFPaper.QBinomialCommRing
