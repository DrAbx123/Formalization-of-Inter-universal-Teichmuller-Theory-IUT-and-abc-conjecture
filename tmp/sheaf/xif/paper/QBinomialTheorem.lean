import tmp.sheaf.xif.paper.TateJacobiHahnAttempt

noncomputable section
open LeanFormal.IUT.XiFPaper.TateJacobiHahnAttempt
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.QBinomialTheorem

universe u

/-- Statement of the q-binomial theorem in the form needed for the Jacobi product. -/
def QBinomialTheoremStatement (K : Type u) [Field K] : Prop :=
  forall (N : Nat) (q z : K), qBinomialTheoremTarget N q z


theorem S3133_sum_range_Icc_shift (K : Type u) [Field K]
    (f : Nat -> K) (N : Nat) :
    Finset.sum (Finset.range N) f =
      Finset.sum (Finset.Icc 1 N) (fun j : Nat => f (j - 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      rw [Finset.sum_Icc_succ_top (by omega)]
      simp



noncomputable def qBinoTermC (K : Type u) [Field K]
    (N k : Nat) (q z : K) : K :=
  q ^ (Nat.choose k 2) * qBinom N k q * z ^ k

theorem S3133_qBinoTermC_succ (K : Type u) [Field K]
    (N k : Nat) (q z : K) :
    qBinoTermC K N (k + 1) q z +
        qBinoTermC K N k q z * (z * q ^ N) =
      qBinoTermC K (N + 1) (k + 1) q z := by
  by_cases hk : k <= N
  · have hchoose : Nat.choose (k + 1) 2 = Nat.choose k 2 + k := by
      have := Nat.choose_succ_succ k 1
      simpa [Nat.choose_one_right, add_comm] using this
    have hrec := S3132_qBinom_succ_succ N k q
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
      S3132_qBinom_eq_zero_of_lt q (by omega)
    have h2 : qBinom N k q = 0 :=
      S3132_qBinom_eq_zero_of_lt q hk'
    have h3 : qBinom (N + 1) (k + 1) q = 0 :=
      S3132_qBinom_eq_zero_of_lt q (by omega)
    unfold qBinoTermC
    simp [h1, h2, h3]


theorem S3133_qBinomial_sum_step (K : Type u) [Field K]
    (N : Nat) (q z : K) :
    (Finset.sum (Finset.range (N + 1)) (fun k : Nat =>
        qBinoTermC K N k q z)) * (1 + z * q ^ N) =
      Finset.sum (Finset.range (N + 2)) (fun k : Nat =>
        qBinoTermC K (N + 1) k q z) := by
  let f : Nat -> K := fun k => qBinoTermC K N k q z
  let h : Nat -> K := fun k => qBinoTermC K (N + 1) k q z
  have h0 : h 0 = f 0 := by
    simp [f, h, qBinoTermC, S3132_qBinom_succ_zero]
  have hchoose : Nat.choose (N + 1) 2 = Nat.choose N 2 + N := by
    have := Nat.choose_succ_succ N 1
    simpa [Nat.choose_one_right, add_comm] using this
  have hN : h (N + 1) = f N * (z * q ^ N) := by
    have hq : qBinom (N + 1) (N + 1) q = qBinom N N q := by
      rw [S3132_qBinom_succ_succ]
      simp [S3132_qBinom_self_succ]
    simp only [h, f, qBinoTermC]
    rw [hq, hchoose]
    ring
  have hterm : forall k : Nat, k < N ->
      h (k + 1) = f (k + 1) + f k * (z * q ^ N) := by
    intro k hk
    exact (S3133_qBinoTermC_succ K N k q z).symm
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


theorem S3133_qBinomialTheoremChoose (K : Type u) [Field K]
    (N : Nat) (q z : K) :
    Finset.prod (Finset.range N) (fun m : Nat => (1 : K) + z * q ^ m) =
      Finset.sum (Finset.range (N + 1)) (fun k : Nat =>
        qBinoTermC K N k q z) := by
  induction N with
  | zero => simp [qBinoTermC, qBinom]
  | succ N ih =>
      rw [Finset.prod_range_succ, ih]
      exact S3133_qBinomial_sum_step K N q z

theorem S3133_qBinomialTheorem (K : Type u) [Field K] :
    QBinomialTheoremStatement K := by
  intro N q z
  unfold qBinomialTheoremTarget
  rw [S3133_qBinomialTheoremChoose K N q z]
  apply Finset.sum_congr rfl
  intro k hk
  unfold qBinoTermC
  rw [← Nat.choose_two_right k]

#check QBinomialTheoremStatement
#check qBinomialTheoremTarget
#check S3132_qBinomialTheorem_zero
#check S3132_qBinomialTheorem_one
#check S3132_qBinom_succ_succ
#check S3132_qBinom_self_succ

end LeanFormal.IUT.XiFPaper.QBinomialTheorem
