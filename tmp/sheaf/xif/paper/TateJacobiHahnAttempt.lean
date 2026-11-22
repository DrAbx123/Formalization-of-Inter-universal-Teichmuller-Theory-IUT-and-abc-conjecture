import Mathlib.RingTheory.HahnSeries.Basic
import Mathlib.RingTheory.HahnSeries.Summable
import tmp.sheaf.xif.paper.TateJacobiStandardAttempt

noncomputable section
open HahnSeries
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1600000

namespace LeanFormal.IUT.XiFPaper.TateJacobiHahnAttempt

universe u

variable {K : Type u} [Field K]

/-- Formal variable r as the Hahn series single 1 1. -/
noncomputable def formalR : HahnSeries Int K :=
  HahnSeries.single (1 : Int) (1 : K)

/-- Formal q = r^2. -/
noncomputable def formalQ : HahnSeries Int K := formalR ^ 2

/-- Finite standard Jacobi product with q = r^2, truncated at N. -/
noncomputable def jacobiFormalProduct (z : K) (N : Nat) : HahnSeries Int K :=
  Finset.prod (Finset.range N) (fun m : Nat =>
    ((1 : HahnSeries Int K) -
        HahnSeries.single (4 * (m + 1) : Int) (1 : K)) *
      ((1 : HahnSeries Int K) +
        HahnSeries.single (4 * (m + 1) - 2 : Int) z) *
      ((1 : HahnSeries Int K) +
        HahnSeries.single (4 * (m + 1) - 2 : Int) z⁻¹))



private lemma support_add_nonneg {x y : HahnSeries Int K}
    (hx : x.support ⊆ {n : Int | 0 <= n})
    (hy : y.support ⊆ {n : Int | 0 <= n}) :
    (x + y).support ⊆ {n : Int | 0 <= n} := by
  intro n hn
  rcases HahnSeries.support_add_subset x y hn with h | h
  · exact hx h
  · exact hy h

private lemma support_neg_nonneg {x : HahnSeries Int K}
    (hx : x.support ⊆ {n : Int | 0 <= n}) :
    (-x).support ⊆ {n : Int | 0 <= n} :=
  fun n hn => hx (HahnSeries.support_neg_subset x hn)

private lemma support_mul_nonneg {x y : HahnSeries Int K}
    (hx : x.support ⊆ {n : Int | 0 <= n})
    (hy : y.support ⊆ {n : Int | 0 <= n}) :
    (x * y).support ⊆ {n : Int | 0 <= n} := by
  intro n hn
  rcases HahnSeries.support_mul_subset hn with ⟨a, ha, b, hb, rfl⟩
  exact add_nonneg (by simpa using hx ha) (by simpa using hy hb)

private lemma single_support_nonneg {a : Int} (ha : 0 <= a) (r : K) :
    (HahnSeries.single a r).support ⊆ {n : Int | 0 <= n} := by
  intro n hn
  have h : n = a := HahnSeries.support_single_subset hn
  rw [h]
  exact ha

private lemma one_support_nonneg :
    ((1 : HahnSeries Int K)).support ⊆ {n : Int | 0 <= n} := by
  intro n hn
  have h : n = 0 := by
    simpa [HahnSeries.support_one] using hn
  rw [h]
  norm_num

private lemma jacobiFormalFactor_support_nonneg (z : K) (m : Nat) :
    (((1 : HahnSeries Int K) -
        HahnSeries.single (4 * (m + 1) : Int) (1 : K)) *
      ((1 : HahnSeries Int K) +
        HahnSeries.single (4 * (m + 1) - 2 : Int) z) *
      ((1 : HahnSeries Int K) +
        HahnSeries.single (4 * (m + 1) - 2 : Int) z⁻¹)).support ⊆
      {n : Int | 0 <= n} := by
  have ha : (0 : Int) <= (4 * (m + 1) : Int) := by omega
  have hb : (0 : Int) <= (4 * (m + 1) - 2 : Int) := by omega
  have h1 : ((1 : HahnSeries Int K) -
      HahnSeries.single (4 * (m + 1) : Int) (1 : K)).support ⊆
      {n : Int | 0 <= n} := by
    rw [sub_eq_add_neg]
    exact support_add_nonneg one_support_nonneg
      (support_neg_nonneg (single_support_nonneg ha 1))
  have h2 : ((1 : HahnSeries Int K) +
      HahnSeries.single (4 * (m + 1) - 2 : Int) z).support ⊆
      {n : Int | 0 <= n} :=
    support_add_nonneg one_support_nonneg (single_support_nonneg hb z)
  have h3 : ((1 : HahnSeries Int K) +
      HahnSeries.single (4 * (m + 1) - 2 : Int) z⁻¹).support ⊆
      {n : Int | 0 <= n} :=
    support_add_nonneg one_support_nonneg (single_support_nonneg hb z⁻¹)
  exact support_mul_nonneg (support_mul_nonneg h1 h2) h3

theorem S3130_jacobiFormal_support_nonneg (z : K) :
    forall N : Nat,
      (jacobiFormalProduct z N).support ⊆ {n : Int | 0 <= n} := by
  intro N
  induction N with
  | zero => simp [jacobiFormalProduct]
  | succ N ih =>
      rw [jacobiFormalProduct, Finset.prod_range_succ]
      change (jacobiFormalProduct z N *
        (((1 : HahnSeries Int K) -
            HahnSeries.single (4 * (N + 1) : Int) (1 : K)) *
          ((1 : HahnSeries Int K) +
            HahnSeries.single (4 * (N + 1) - 2 : Int) z) *
          ((1 : HahnSeries Int K) +
            HahnSeries.single (4 * (N + 1) - 2 : Int) z⁻¹))).support ⊆
        {n : Int | 0 <= n}
      exact support_mul_nonneg ih (jacobiFormalFactor_support_nonneg z N)


noncomputable def jacobiFormalFactor (z : K) (k : Nat) : HahnSeries Int K :=
  ((1 : HahnSeries Int K) -
      HahnSeries.single (4 * (k + 1) : Int) (1 : K)) *
    ((1 : HahnSeries Int K) +
      HahnSeries.single (4 * (k + 1) - 2 : Int) z) *
    ((1 : HahnSeries Int K) +
      HahnSeries.single (4 * (k + 1) - 2 : Int) z⁻¹)

private lemma support_one_add_single_upper (b : Int) (hb : 0 <= b) (r : K) :
    ((1 : HahnSeries Int K) + HahnSeries.single b r).support ⊆
      ({0} : Set Int) ∪ {n : Int | b <= n} := by
  intro n hn
  rcases HahnSeries.support_add_subset (1 : HahnSeries Int K)
    (HahnSeries.single b r) hn with h | h
  · left
    simpa [HahnSeries.support_one] using h
  · right
    have hn' : n = b := HahnSeries.support_single_subset h
    rw [hn']
    simpa using (le_rfl : b <= b)

private lemma support_one_sub_single_upper (a b : Int) (hb : 0 <= b) (ha : b <= a) (r : K) :
    ((1 : HahnSeries Int K) - HahnSeries.single a r).support ⊆
      ({0} : Set Int) ∪ {n : Int | b <= n} := by
  intro n hn
  rw [sub_eq_add_neg] at hn
  rcases HahnSeries.support_add_subset (1 : HahnSeries Int K)
    (-HahnSeries.single a r) hn with h | h
  · left
    simpa [HahnSeries.support_one] using h
  · right
    have h' := HahnSeries.support_neg_subset (HahnSeries.single a r) h
    have hn' : n = a := HahnSeries.support_single_subset h'
    rw [hn']
    exact ha

private lemma support_mul_upper (b : Int) (hb : 0 <= b) {x y : HahnSeries Int K}
    (hx : x.support ⊆ ({0} : Set Int) ∪ {n : Int | b <= n})
    (hy : y.support ⊆ ({0} : Set Int) ∪ {n : Int | b <= n}) :
    (x * y).support ⊆ ({0} : Set Int) ∪ {n : Int | b <= n} := by
  intro n hn
  rcases HahnSeries.support_mul_subset hn with ⟨a, ha, c, hc, rfl⟩
  rcases hx ha with ha0 | ha1
  · rcases hy hc with hc0 | hc1
    · left; rw [Set.mem_singleton_iff] at ha0 hc0; rw [ha0, hc0]; rfl
    · right; rw [Set.mem_singleton_iff] at ha0; rw [ha0]; simpa using hc1
  · right
    rcases hy hc with hc0 | hc1
    · rw [Set.mem_singleton_iff] at hc0; rw [hc0]; simpa using ha1
    · have ha1' : b <= a := by simpa using ha1
      have hc1' : b <= c := by simpa using hc1
      simp only [Set.mem_setOf_eq]
      omega

private lemma jacobiFormalFactor_support_upper (z : K) (k : Nat) :
    (jacobiFormalFactor z k).support ⊆
      ({0} : Set Int) ∪ {n : Int | 4 * (k + 1) - 2 <= n} := by
  have hb : (0 : Int) <= 4 * (k + 1) - 2 := by omega
  have ha : 4 * (k + 1) - 2 <= (4 * (k + 1) : Int) := by omega
  have hA := support_one_sub_single_upper
    (4 * (k + 1) : Int) (4 * (k + 1) - 2 : Int) hb ha (1 : K)
  have hB := support_one_add_single_upper
    (4 * (k + 1) - 2 : Int) hb z
  have hC := support_one_add_single_upper
    (4 * (k + 1) - 2 : Int) hb z⁻¹
  unfold jacobiFormalFactor
  exact support_mul_upper _ hb (support_mul_upper _ hb hA hB) hC




theorem S3130_jacobiFormalFactor_coeff_zero (z : K) (k : Nat) :
    (jacobiFormalFactor z k).coeff 0 = 1 := by
  have h4 : (0 : Int) ≠ 4 + (k : Int) * 4 := by omega
  have h6 : (0 : Int) ≠ 6 + (k : Int) * 8 := by omega
  have h8 : (0 : Int) ≠ 8 + (k : Int) * 12 := by omega
  have h2 : (0 : Int) ≠ 2 + (k : Int) * 4 := by omega
  have h4' : (0 : Int) ≠ 4 + (k : Int) * 8 := by omega
  have hab : (0 : Int) ≠ 4 + (k : Int) * 4 + (2 + (k : Int) * 4) := by omega
  have habb : (0 : Int) ≠
      4 + (k : Int) * 4 + (2 + (k : Int) * 4) + (2 + (k : Int) * 4) := by omega
  have hbb : (0 : Int) ≠ 2 + (k : Int) * 4 + (2 + (k : Int) * 4) := by omega
  unfold jacobiFormalFactor
  ring_nf
  simp only [HahnSeries.single_mul_single]
  simp only [HahnSeries.coeff_add, HahnSeries.coeff_single,
    HahnSeries.coeff_one]
  simp [HahnSeries.coeff_add, HahnSeries.coeff_single,
    HahnSeries.coeff_one, h4, h6, h8, h2, h4', hab, habb, hbb]


theorem S3130_jacobiFormalFactor_tail_support (z : K) (k : Nat) :
    (jacobiFormalFactor z k - 1).support ⊆
      {n : Int | 4 * (k + 1) - 2 <= n} := by
  intro n hn
  have hncoeff : (jacobiFormalFactor z k - 1).coeff n ≠ 0 :=
    (HahnSeries.mem_support _ _).1 hn
  have h0 : (jacobiFormalFactor z k - 1).coeff 0 = 0 := by
    rw [sub_eq_add_neg, HahnSeries.coeff_add, HahnSeries.coeff_neg,
      S3130_jacobiFormalFactor_coeff_zero, HahnSeries.coeff_one]
    norm_num
  rw [sub_eq_add_neg] at hn
  rcases HahnSeries.support_add_subset (jacobiFormalFactor z k)
    (-(1 : HahnSeries Int K)) hn with h | h
  · rcases jacobiFormalFactor_support_upper z k h with h0' | hb
    · rw [Set.mem_singleton_iff] at h0'
      exfalso
      apply hncoeff
      rw [h0']
      exact h0
    · exact hb
  · have h' := HahnSeries.support_neg_subset (1 : HahnSeries Int K) h
    have hn0 : n = 0 := by simpa [HahnSeries.support_one] using h'
    exfalso
    apply hncoeff
    rw [hn0]
    exact h0

theorem S3130_jacobiFormal_truncation (z : K) :
    forall k : Nat,
      (jacobiFormalProduct z k).coeff (2 * k) =
        (jacobiFormalProduct z (k + 1)).coeff (2 * k) := by
  intro k
  have htail := S3130_jacobiFormalFactor_tail_support z k
  have hprod : jacobiFormalProduct z (k + 1) =
      jacobiFormalProduct z k * jacobiFormalFactor z k := by
    rw [jacobiFormalProduct, Finset.prod_range_succ]
    rfl
  have hzero : ((jacobiFormalProduct z k) *
      (jacobiFormalFactor z k - 1)).coeff (2 * k) = 0 := by
    by_contra hcoeff
    have hnmem : (2 * k : Int) ∈ ((jacobiFormalProduct z k) *
        (jacobiFormalFactor z k - 1)).support :=
      (HahnSeries.mem_support _ _).2 hcoeff
    rcases HahnSeries.support_mul_subset hnmem with ⟨a, ha, b, hb, hEq⟩
    have ha0 : 0 <= a := S3130_jacobiFormal_support_nonneg z k ha
    have hb0 : 4 * (k + 1) - 2 <= b := htail hb
    have hEq' : (2 * (k : Int)) = a + b := by simpa using hEq.symm
    have hb0' : (4 * (k : Int) + 2) <= b := by omega
    omega
  rw [hprod]
  rw [show jacobiFormalFactor z k = 1 + (jacobiFormalFactor z k - 1) by ring]
  rw [mul_add, mul_one, HahnSeries.coeff_add, hzero, add_zero]


theorem S3130_jacobiFormal_coeff_recurrence (z : K) (N k : Nat)
    (hk : 2 * k < 4 * N + 2) :
    (jacobiFormalProduct z (N + 1)).coeff (2 * k) =
      (jacobiFormalProduct z N).coeff (2 * k) := by
  have htail := S3130_jacobiFormalFactor_tail_support z N
  have hprod : jacobiFormalProduct z (N + 1) =
      jacobiFormalProduct z N * jacobiFormalFactor z N := by
    rw [jacobiFormalProduct, Finset.prod_range_succ]
    rfl
  have hzero : ((jacobiFormalProduct z N) *
      (jacobiFormalFactor z N - 1)).coeff (2 * k : Int) = 0 := by
    by_contra hcoeff
    have hnmem : (2 * k : Int) ∈ ((jacobiFormalProduct z N) *
        (jacobiFormalFactor z N - 1)).support :=
      (HahnSeries.mem_support _ _).2 hcoeff
    rcases HahnSeries.support_mul_subset hnmem with ⟨a, ha, b, hb, hEq⟩
    have ha0 : 0 <= a := S3130_jacobiFormal_support_nonneg z N ha
    have hb0 : 4 * (N + 1) - 2 <= b := htail hb
    have hEq' : (2 * (k : Int)) = a + b := by simpa using hEq.symm
    have hb0' : (4 * (N : Int) + 2) <= b := by omega
    omega
  rw [hprod]
  rw [show jacobiFormalFactor z N = 1 + (jacobiFormalFactor z N - 1) by ring]
  rw [mul_add, mul_one, HahnSeries.coeff_add, hzero, add_zero]

theorem S3130_jacobiFormal_q2 (z : K) (hz : z ≠ 0) :
    (jacobiFormalProduct z 1).coeff 4 = 0 := by
  rw [jacobiFormalProduct, Finset.prod_range_one]
  norm_num
  rw [mul_add, mul_one, HahnSeries.coeff_add]
  rw [HahnSeries.coeff_mul_single]
  rw [mul_add, mul_one]
  rw [HahnSeries.coeff_add, HahnSeries.coeff_add]
  rw [HahnSeries.coeff_mul_single, HahnSeries.coeff_mul_single]
  simp [HahnSeries.coeff_add, HahnSeries.coeff_single,
    HahnSeries.coeff_one, HahnSeries.coeff_zero]
  field_simp [hz]
  ring





theorem S3130_jacobiFormal_q3 (z : K) (hz : z ≠ 0) :
    (jacobiFormalProduct z 2).coeff 6 = 0 := by
  rw [jacobiFormalProduct, Finset.prod_range_succ,
    Finset.prod_range_succ]
  norm_num
  ring_nf
  simp only [HahnSeries.single_pow, HahnSeries.single_mul_single]
  simp [HahnSeries.coeff_add, HahnSeries.coeff_single,
    HahnSeries.coeff_one, HahnSeries.coeff_zero]
  field_simp [hz]
  ring


theorem S3130_jacobiFormal_q4 (z : K) (hz : z ≠ 0) :
    (jacobiFormalProduct z 2).coeff 8 = z ^ 2 + z⁻¹ ^ 2 := by
  rw [jacobiFormalProduct, Finset.prod_range_succ,
    Finset.prod_range_succ]
  norm_num
  ring_nf
  simp only [HahnSeries.single_pow, HahnSeries.single_mul_single]
  simp [HahnSeries.coeff_add, HahnSeries.coeff_single,
    HahnSeries.coeff_one, HahnSeries.coeff_zero]
  field_simp [hz]
  ring

def jacobiFormalQ2CoeffTarget (z : K) : Prop :=
  (jacobiFormalProduct z 1).coeff 4 = 0

def jacobiFormalQ3CoeffTarget (z : K) : Prop :=
  (jacobiFormalProduct z 2).coeff 6 = 0

def jacobiFormalQ4CoeffTarget (z : K) : Prop :=
  (jacobiFormalProduct z 2).coeff 8 = z ^ 2 + z⁻¹ ^ 2

/-- Truncation target: coefficient of r^(2k) only depends on the first k factors. -/
def jacobiFormalTruncationTarget (z : K) : Prop :=
  forall k : Nat, (jacobiFormalProduct z k).coeff (2 * k) =
    (jacobiFormalProduct z (k + 1)).coeff (2 * k)


/-- Support-nonneg target for the finite Jacobi product. -/
def jacobiFormalSupportNonnegTarget (z : K) : Prop :=
  forall N : Nat,
    (jacobiFormalProduct z N).support ⊆ {n : Int | 0 <= n}


/-- General coefficient target: a single coefficient sequence whose first five
values are the verified q^0..q^4 coefficients, and whose k-th value is the
truncated product coefficient. -/
def TateJacobiGeneralCoeffTarget (z : K) : Prop :=
  exists c : Nat -> K,
    c 0 = 1 ∧
      c 1 = z + z⁻¹ ∧
        c 2 = 0 ∧
          c 3 = 0 ∧
            c 4 = z ^ 2 + z⁻¹ ^ 2 ∧
              forall k : Nat,
                (jacobiFormalProduct z (k + 1)).coeff (2 * k) = c k


noncomputable def jacobiRHScoeff (k : Nat) (z : K) : K := by
  classical
  exact if k = 0 then 1
    else if h : ∃ n : Nat, 0 < n ∧ n * n = k then
      let n := Classical.choose h
      z ^ n + z⁻¹ ^ n
    else 0

theorem S3130_jacobiRHScoeff_zero (z : K) :
    jacobiRHScoeff 0 z = 1 := by
  simp [jacobiRHScoeff]

theorem S3130_jacobiSquare_unique {n m : Nat} (hn : 0 < n) (hm : 0 < m)
    (h : n * n = m * m) : n = m := by
  have hInt : (n : Int) * (n : Int) = (m : Int) * (m : Int) := by
    exact_mod_cast h
  have hfac : ((n : Int) - (m : Int)) * ((n : Int) + (m : Int)) = 0 := by
    nlinarith
  have hsum : (n : Int) + (m : Int) ≠ 0 := by positivity
  have hdiff : (n : Int) - (m : Int) = 0 := by
    rcases mul_eq_zero.mp hfac with h' | h'
    · exact h'
    · exact absurd h' hsum
  omega


noncomputable def qBinomialProduct (z : K) (N : Nat) : HahnSeries Int K :=
  Finset.prod (Finset.range N) (fun m : Nat =>
    (1 : HahnSeries Int K) +
      HahnSeries.single (2 * (m : Int)) z)

theorem S3131_qBinomialProduct_succ (z : K) (N : Nat) :
    qBinomialProduct z (N + 1) =
      qBinomialProduct z N *
        ((1 : HahnSeries Int K) +
          HahnSeries.single (2 * (N : Int)) z) := by
  rw [qBinomialProduct, Finset.prod_range_succ]
  rfl


noncomputable def qBinom : Nat -> Nat -> K -> K
  | 0, 0, _ => 1
  | 0, _ + 1, _ => 0
  | N + 1, 0, q => qBinom N 0 q
  | N + 1, k + 1, q => qBinom N (k + 1) q +
      q ^ (N - k) * qBinom N k q


theorem S3132_qBinom_eq_zero_of_lt {N k : Nat} (q : K) (h : k > N) :
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

theorem S3132_qBinom_self_succ (N : Nat) (q : K) :
    qBinom N (N + 1) q = 0 :=
  S3132_qBinom_eq_zero_of_lt q (by omega)

theorem S3132_qBinom_succ_zero (N : Nat) (q : K) :
    qBinom (N + 1) 0 q = qBinom N 0 q := by
  rw [qBinom]

theorem S3132_qBinom_succ_succ (N k : Nat) (q : K) :
    qBinom (N + 1) (k + 1) q =
      qBinom N (k + 1) q + q ^ (N - k) * qBinom N k q := by
  rw [qBinom]

def qBinomialTheoremTarget (N : Nat) (q z : K) : Prop :=
  Finset.prod (Finset.range N) (fun m : Nat => (1 : K) + z * q ^ m) =
    Finset.sum (Finset.range (N + 1)) (fun k : Nat =>
      q ^ (k * (k - 1) / 2) * qBinom N k q * z ^ k)


theorem S3132_qBinomialTheorem_zero (q z : K) :
    qBinomialTheoremTarget 0 q z := by
  simp [qBinomialTheoremTarget, qBinom]

theorem S3132_qBinomialTheorem_one (q z : K) :
    qBinomialTheoremTarget 1 q z := by
  have h10 : qBinom 1 0 q = 1 := by simp [qBinom]
  have h11 : qBinom 1 1 q = 1 := by simp [qBinom]
  simp only [qBinomialTheoremTarget, Finset.prod_range_one]
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  simp [h10, h11]


noncomputable def jacobiAlignedProduct (z : K) (N : Nat) : HahnSeries Int K :=
  (Finset.prod (Finset.range N) (fun m : Nat =>
      (1 : HahnSeries Int K) +
        (HahnSeries.C z * formalR ^ 2) * formalR ^ (4 * m))) *
    (Finset.prod (Finset.range N) (fun m : Nat =>
      (1 : HahnSeries Int K) +
        (HahnSeries.C z⁻¹ * formalR ^ 2) * formalR ^ (4 * m))) *
    (Finset.prod (Finset.range N) (fun m : Nat =>
      (1 : HahnSeries Int K) - formalR ^ (4 * (m + 1))))

def jacobiAlignedProductTarget (z : K) : Prop :=
  forall N : Nat, jacobiFormalProduct z N = jacobiAlignedProduct z N


#check formalR
#check formalQ
#check jacobiFormalProduct
#check jacobiFormalQ2CoeffTarget
#check HahnSeries.coeff
#check HahnSeries.coeff_single
#check HahnSeries.C

end LeanFormal.IUT.XiFPaper.TateJacobiHahnAttempt
end