import Mathlib
import Mathlib.RingTheory.Polynomial.Vieta
import LeanFormal.IUT.Audit.Status

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma24F0BoundActual

/-- The k-th elementary symmetric sum of the roots alpha_i (as a complex number). -/
def symSum (d : Nat) (α : Fin d → ℂ) (k : Nat) : ℂ :=
  ∑ s ∈ (Finset.univ : Finset (Fin d)).powersetCard k, ∏ i ∈ s, α i

/-- Elementary symmetric sums are bounded by the binomial coefficient when all roots
have absolute value at most 1. -/
theorem s3135_norm_symSum_le_choose (d : Nat) (α : Fin d → ℂ)
    (hα : ∀ i, ‖α i‖ ≤ 1) (k : Nat) :
    ‖symSum d α k‖ ≤ (d.choose k : ℝ) := by
  unfold symSum
  calc ‖∑ s ∈ (Finset.univ : Finset (Fin d)).powersetCard k, ∏ i ∈ s, α i‖
      ≤ ∑ s ∈ (Finset.univ : Finset (Fin d)).powersetCard k, ‖∏ i ∈ s, α i‖ :=
        norm_sum_le _ _
    _ ≤ ∑ s ∈ (Finset.univ : Finset (Fin d)).powersetCard k, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro s hs
        rw [norm_prod]
        calc ∏ i ∈ s, ‖α i‖ ≤ ∏ i ∈ s, (1 : ℝ) :=
              Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hα i)
          _ = 1 := by simp
    _ = (d.choose k : ℝ) := by
        rw [Finset.sum_const, Finset.card_powersetCard]
        simp

/-- The binomial coefficient is bounded by d^d for d >= 1 (paper [Mzk1] lines
187-199 use the crude bound d0^d0). -/
theorem s3135_choose_le_self_pow (d k : Nat) (hd : 1 ≤ d) : d.choose k ≤ d ^ d := by
  by_cases hk : k ≤ d
  · calc d.choose k ≤ d ^ k := Nat.choose_le_pow d k
      _ ≤ d ^ d := Nat.pow_le_pow_right hd hk
  · have hzero : d.choose k = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [hzero]
    exact Nat.zero_le _

/-- The elementary symmetric bound in the paper's shape d0^d0. -/
theorem s3135_norm_symSum_le_self_pow (d : Nat) (α : Fin d → ℂ)
    (hα : ∀ i, ‖α i‖ ≤ 1) (k : Nat) (hd : 1 ≤ d) :
    ‖symSum d α k‖ ≤ (d : ℝ) ^ d := by
  refine le_trans (s3135_norm_symSum_le_choose d α hα k) ?_
  exact_mod_cast s3135_choose_le_self_pow d k hd

/-- **(F) f0 coefficient bound, PROVED** (paper [Mzk1] Lemma 2.4 lines 183-199): for a
monic degree-d polynomial whose roots all lie in the closed unit disk, every
coefficient is bounded in absolute value by d^d.  The product is the minimal
polynomial f0 after the paper's normalization of S.  Proof: Mathlib Vieta
(Finset.prod_X_add_C_coeff, Mathlib.RingTheory.Polynomial.Vieta) gives each coefficient
as a signed elementary symmetric sum of the roots, bounded by C(d,k) <= d^d. -/
theorem s3135_f0_coeff_bound (d : Nat) (hd : 1 ≤ d) (a : Fin d → ℂ)
    (ha : ∀ i, ‖a i‖ ≤ 1) (k : Nat) :
    ‖(∏ i : Fin d, (Polynomial.X - Polynomial.C (a i))).coeff k‖ ≤ (d : ℝ) ^ d := by
  by_cases hk : k ≤ d
  · have hp : (∏ i : Fin d, (Polynomial.X - Polynomial.C (a i))) =
        ∏ i : Fin d, (Polynomial.X + Polynomial.C (- a i)) := by
      simp [sub_eq_add_neg]
    have hcoe := Finset.prod_X_add_C_coeff (s := (Finset.univ : Finset (Fin d)))
      (r := fun i => - a i) (k := k) (by simpa using hk)
    rw [hp, hcoe]
    calc ‖∑ t ∈ (Finset.univ : Finset (Fin d)).powersetCard (Finset.card Finset.univ - k),
            ∏ i ∈ t, - a i‖
        ≤ ∑ t ∈ (Finset.univ : Finset (Fin d)).powersetCard (Finset.card Finset.univ - k),
            ‖∏ i ∈ t, - a i‖ := norm_sum_le _ _
      _ ≤ ∑ t ∈ (Finset.univ : Finset (Fin d)).powersetCard (Finset.card Finset.univ - k),
            (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro t ht
          rw [norm_prod]
          calc ∏ i ∈ t, ‖- a i‖ ≤ ∏ i ∈ t, (1 : ℝ) :=
                Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => by simpa using ha i)
            _ = 1 := by simp
      _ = ((d.choose (d - k)) : ℝ) := by
          rw [Finset.sum_const, Finset.card_powersetCard]
          simp
      _ ≤ (d : ℝ) ^ d := by
          have hc := s3135_choose_le_self_pow d (d - k) hd
          exact_mod_cast hc
  · have hdeg : (∏ i : Fin d, (Polynomial.X - Polynomial.C (a i))).natDegree ≤ d := by
      calc _ ≤ ∑ i : Fin d, (Polynomial.X - Polynomial.C (a i)).natDegree :=
            Polynomial.natDegree_prod_le _ _
        _ = d := by simp [Polynomial.natDegree_X_sub_C]
    have hzero : (∏ i : Fin d, (Polynomial.X - Polynomial.C (a i))).coeff k = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg (by omega))
    rw [hzero, norm_zero]
    exact pow_nonneg (Nat.cast_nonneg d) d

/-- (F) status: the f0 coefficient bound is now PROVED unconditionally using Mathlib's
general Vieta formula; no remaining interface. -/
def s3135Mzk1F0Status : Audit.Obligation :=
  { id := "MZK1.lemma24.f0-coefficient-bound"
    source := "papers/motizuki_corpus/text/Noncritical Belyi Maps.txt Lemma 2.4 lines 183-199"
    status := Audit.VerificationStatus.interface
    note := "PROVED: symmetric-sum bound (‖e_k‖ <= C(d,k)), C(d,k) <= d^d, and the unconditional f0 coefficient bound s3135_f0_coeff_bound using Mathlib Vieta (Finset.prod_X_add_C_coeff, Mathlib.RingTheory.Polynomial.Vieta) for k <= d and natDegree_prod_le for k > d. (F) CLOSED; previous VietaCoefficientBridge interface eliminated (general Vieta exists in pinned Mathlib). No fake witnesses; registry frozen 14041."
    dependsOn := [ "MZK1.lemma24.measure-monotonicity" ]
    sorryItems := [] }

#check s3135_f0_coeff_bound
#check s3135_norm_symSum_le_choose
end LeanFormal.IUT.XiFPaper.Mzk1Lemma24F0BoundActual
end