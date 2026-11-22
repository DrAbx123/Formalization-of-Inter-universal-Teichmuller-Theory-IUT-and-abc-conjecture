import tmp.sheaf.xif.paper.Mzk1BadParamFiniteActual
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 1000000

noncomputable section

open Polynomial

namespace LeanFormal.IUT.XiFPaper.Mzk1BadParamProofActual

open LeanFormal.IUT.XiFPaper.Mzk1BadParamFiniteActual

/-!
# Mzk1BadParamProofActual --- the bad-parameter analysis for the scaling family (m,n) = k(p,q)

## Verdict on the two named targets of Mzk1BadParamFiniteActual

* Mzk1BadParamFiniteActual.badParamSet_finite is FALSE (`not_badParamSet_finite`).
* Mzk1BadParamFiniteActual.exists_good_param is FALSE (`not_exists_good_param`).
* The naive collision statement is FALSE (`not_collision_finite_statement`).

## Why

The docstring plan of the prior file analyses the normalizing constant as if it grew only
polynomially in k, and concludes that the exponential factor u^(kp)(1-u)^(kq) dominates. In fact

  c_{kp,kq} = (c_{p,q})^k     (belyiConst_scaling)

so the whole sequence is exactly geometric:

  B_{kp,kq}(u) = (B_{p,q}(u))^k     (belyiEvalQ_scaling).

Consequently the bad set is the set of exponents k with (B_{p,q}(u))^k = 1, and by the rational
power classification:

* B_{p,q}(u) = 1  => every k is bad, the bad set is all of N;
* B_{p,q}(u) = -1 => exactly the even k are bad;
* otherwise only k = 0 is bad, i.e. the bad set is contained in {0}.

The case B_{p,q}(u) = 1 is non-vacuous: the Belyi normalisation satisfies
B_{p,q}(p/(p+q)) = 1, so for u = p/(p+q) the stated targets fail for every p, q
(badParamSet_div_add_eq_univ). The concrete counterexample p = q = 1, u = 1/2 is
badParamSet_one_one_half. Likewise B_{1,1} = 4X(1-X) is symmetric, so u = 1/4, v = 3/4 collide
for every k (collisionParamSet_one_one_quarter).

## What is proved instead

* belyiEvalQ_scaling : the exact geometric identity.
* badParamSet_finite_iff : the bad set is finite iff B_{p,q}(u) is neither 1 nor -1
  (with badParamSet_eq_univ_of_eval_eq_one / badParamSet_eq_even_of_eval_eq_neg_one giving the
  two infinite cases explicitly).
* badParamSet_finite_of_ne, exists_good_param_of_ne_one : the corrected sharp statements, with the
  necessary extra hypothesis B_{p,q}(u) is not 1 (resp. not -1); badParamSet_finite_corrected and
  exists_good_param_corrected package them as Props in the shape of the original targets.
* collisionParamSet_finite_iff : the exact collision classification, finite iff B(u) is neither
  B(v) nor -B(v). The statement "finitely many collisions for every u != v" is false.

Every proof is complete (no unfinished proof steps, no new axioms): all declarations depend only on
propext, Classical.choice, Quot.sound
(see the #print axioms block at the end).
-/

/-- The normalizing constant (m+n)^(m+n)/(m^m n^n) of the Belyi polynomial, over Q. -/
def belyiConst (m n : ℕ) : ℚ :=
  ((m : ℚ) + n) ^ (m + n) / ((m : ℚ) ^ m * (n : ℚ) ^ n)

/-- The evaluation formula: B_{m,n}(u) = c_{m,n} u^m (1-u)^n. -/
theorem belyiEvalQ_eq_belyiConst_mul (m n : ℕ) (u : ℚ) :
    belyiEvalQ m n u = belyiConst m n * u ^ m * (1 - u) ^ n := by
  simp [belyiEvalQ, belyiConst, TauCeti.eval_belyiPolynomial]

/-- a ^ (a * b) is nonzero for natural a, b (for a = 0 the exponent is 0, so the power is 1). -/
theorem rat_pow_self_mul_ne_zero (a b : ℕ) : ((a : ℚ) ^ (a * b)) ≠ 0 := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · exact pow_ne_zero _ (by exact_mod_cast ha)

/-- The k-th power of the normalizing constant, with the exponent pulled inside. -/
theorem belyiConst_pow_eq (k p q : ℕ) :
    belyiConst p q ^ k =
      ((p : ℚ) + q) ^ (k * (p + q)) / ((p : ℚ) ^ (k * p) * (q : ℚ) ^ (k * q)) := by
  unfold belyiConst
  rw [div_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]
  rw [show (p + q) * k = k * (p + q) by ring, show p * k = k * p by ring,
    show q * k = k * q by ring]

/-- The normalizing constant is multiplicative under scaling (m,n) -> k(m,n):
c_{kp,kq} = (c_{p,q})^k. This is the point missed by the plan in the prior file: the constant is
exponential in k, not polynomial. -/
theorem belyiConst_scaling (k p q : ℕ) :
    belyiConst (k * p) (k * q) = belyiConst p q ^ k := by
  rcases k with _ | k
  · simp [belyiConst]
  rw [belyiConst_pow_eq]
  unfold belyiConst
  rw [Nat.cast_mul, Nat.cast_mul]
  rw [show (↑(k + 1) : ℚ) * ↑p + (↑(k + 1) : ℚ) * ↑q =
      (↑(k + 1) : ℚ) * (↑p + ↑q) by ring]
  rw [show (k + 1) * p + (k + 1) * q = (k + 1) * (p + q) by ring]
  simp only [mul_pow]
  have hk1 : ((k + 1 : ℕ) : ℚ) ^ ((k + 1) * (p + q)) =
      ((k + 1 : ℕ) : ℚ) ^ ((k + 1) * p) * ((k + 1 : ℕ) : ℚ) ^ ((k + 1) * q) := by
    rw [← pow_add, show (k + 1) * p + (k + 1) * q = (k + 1) * (p + q) by ring]
  have hk : ((k + 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have h1 : ((k + 1 : ℕ) : ℚ) ^ ((k + 1) * p) ≠ 0 := pow_ne_zero _ hk
  have h2 : ((k + 1 : ℕ) : ℚ) ^ ((k + 1) * q) ≠ 0 := pow_ne_zero _ hk
  have h3 : ((p : ℚ) ^ ((k + 1) * p)) ≠ 0 := by
    simpa [Nat.mul_comm p (k + 1)] using rat_pow_self_mul_ne_zero p (k + 1)
  have h4 : ((q : ℚ) ^ ((k + 1) * q)) ≠ 0 := by
    simpa [Nat.mul_comm q (k + 1)] using rat_pow_self_mul_ne_zero q (k + 1)
  rw [hk1]
  rw [div_eq_div_iff (mul_ne_zero (mul_ne_zero h1 h3) (mul_ne_zero h2 h4))
    (mul_ne_zero h3 h4)]
  ring

/-- KEY: the whole scaling family is geometric: B_{kp,kq}(u) = (B_{p,q}(u))^k. -/
theorem belyiEvalQ_scaling (p q : ℕ) (u : ℚ) (k : ℕ) :
    belyiEvalQ (k * p) (k * q) u = belyiEvalQ p q u ^ k := by
  rw [belyiEvalQ_eq_belyiConst_mul, belyiEvalQ_eq_belyiConst_mul, belyiConst_scaling]
  have hu : u ^ (k * p) = (u ^ p) ^ k := by
    rw [Nat.mul_comm k p, pow_mul]
  have hv : (1 - u) ^ (k * q) = ((1 - u) ^ q) ^ k := by
    rw [Nat.mul_comm k q, pow_mul]
  rw [hu, hv, mul_pow, mul_pow]

/-- The bad parameter set is exactly the set of exponents k with (B_{p,q}(u))^k = 1. -/
theorem badParamSet_eq_pow_one (u : ℚ) (p q : ℕ) :
    badParamSet u p q = {k : ℕ | belyiEvalQ p q u ^ k = 1} := by
  ext k
  simp [badParamSet, belyiEvalQ_scaling]

/-- Classification of the powers of a rational number that equal 1. -/
theorem pow_eq_one_imp_eq_or_even {r : ℚ} {k : ℕ} (h : r ^ k = 1) :
    k = 0 ∨ r = 1 ∨ (r = -1 ∧ Even k) := by
  rcases pow_eq_one_iff_cases.mp h with hk | h1 | ⟨h1, h2⟩
  · exact Or.inl hk
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr ⟨h1, h2⟩)

/-- For a rational r outside {1, -1}, the only exponent with r^k = 1 is k = 0. -/
theorem pow_setOf_eq_one_subset_zero (r : ℚ) (h1 : r ≠ 1) (h2 : r ≠ -1) :
    {k : ℕ | r ^ k = 1} ⊆ {0} := by
  intro k hk
  rw [Set.mem_setOf_eq] at hk
  rw [Set.mem_singleton_iff]
  by_contra hk0
  rcases pow_eq_one_imp_eq_or_even hk with rfl | h | ⟨h, -⟩
  · exact hk0 rfl
  · exact h1 h
  · exact h2 h

/-- EXACT classification for an arbitrary rational base: the exponent set {k | r^k = 1} is
finite iff r is neither 1 nor -1. -/
theorem pow_setOf_eq_one_finite_iff (r : ℚ) :
    ({k : ℕ | r ^ k = 1} : Set ℕ).Finite ↔ r ≠ 1 ∧ r ≠ -1 := by
  constructor
  · rintro hfin
    constructor
    · intro h1
      obtain ⟨K, hK⟩ := hfin.bddAbove
      have hmem : K + 1 ∈ {k : ℕ | r ^ k = 1} := by
        rw [Set.mem_setOf_eq, h1, one_pow]
      have := hK hmem
      omega
    · intro h2
      obtain ⟨K, hK⟩ := hfin.bddAbove
      have hmem : 2 * (K + 1) ∈ {k : ℕ | r ^ k = 1} := by
        rw [Set.mem_setOf_eq, h2]
        exact Even.neg_one_pow ⟨K + 1, by ring⟩
      have := hK hmem
      omega
  · rintro ⟨h1, h2⟩
    exact (Set.finite_singleton (0 : ℕ)).subset (pow_setOf_eq_one_subset_zero r h1 h2)

/-- If the base value is 1, EVERY k is bad: the bad set is all of N. -/
theorem badParamSet_eq_univ_of_eval_eq_one (u : ℚ) (p q : ℕ)
    (h : belyiEvalQ p q u = 1) : badParamSet u p q = Set.univ := by
  rw [badParamSet_eq_pow_one]
  ext k
  simp [h]

/-- If the base value is -1, exactly the even k are bad. -/
theorem badParamSet_eq_even_of_eval_eq_neg_one (u : ℚ) (p q : ℕ)
    (h : belyiEvalQ p q u = -1) : badParamSet u p q = {k : ℕ | Even k} := by
  rw [badParamSet_eq_pow_one]
  ext k
  rw [Set.mem_setOf_eq, Set.mem_setOf_eq, h]
  exact neg_one_pow_eq_one_iff_even (by norm_num)

/-- Away from the two exceptional base values 1 and -1, only k = 0 can be bad. -/
theorem badParamSet_subset_zero_of_ne (u : ℚ) (p q : ℕ)
    (h1 : belyiEvalQ p q u ≠ 1) (h2 : belyiEvalQ p q u ≠ -1) :
    badParamSet u p q ⊆ {0} := by
  rw [badParamSet_eq_pow_one]
  exact pow_setOf_eq_one_subset_zero _ h1 h2

/-- CORRECTED (sharp) finite-bad-parameter lemma: the bad set is finite whenever
B_{p,q}(u) is neither 1 nor -1 (and then it is contained in {0}). -/
theorem badParamSet_finite_of_ne (u : ℚ) (p q : ℕ)
    (h1 : belyiEvalQ p q u ≠ 1) (h2 : belyiEvalQ p q u ≠ -1) :
    (badParamSet u p q).Finite :=
  (Set.finite_singleton (0 : ℕ)).subset (badParamSet_subset_zero_of_ne u p q h1 h2)

/-- EXACT classification: the bad set is finite iff the base value is neither 1 nor -1.
If it is 1 the bad set is all of N; if it is -1 the bad set is the set of even numbers. -/
theorem badParamSet_finite_iff (u : ℚ) (p q : ℕ) :
    (badParamSet u p q).Finite ↔ belyiEvalQ p q u ≠ 1 ∧ belyiEvalQ p q u ≠ -1 := by
  rw [badParamSet_eq_pow_one]
  exact pow_setOf_eq_one_finite_iff _

/-- The Belyi critical point: B_{p,q}(p/(p+q)) = 1. -/
theorem belyiEvalQ_div_add_eq_one (p q : ℕ) :
    belyiEvalQ p q ((p : ℚ) / ((p : ℚ) + q)) = 1 := by
  simpa [belyiEvalQ] using TauCeti.eval_div_belyiPolynomial (K := ℚ) p q

/-- The generic failure of the stated target: at the critical point u = p/(p+q) EVERY k is bad,
for every choice of p, q. -/
theorem badParamSet_div_add_eq_univ (p q : ℕ) :
    badParamSet ((p : ℚ) / ((p : ℚ) + q)) p q = Set.univ :=
  badParamSet_eq_univ_of_eval_eq_one _ p q (belyiEvalQ_div_add_eq_one p q)

/-- Concrete instance: B_{1,1} = 4X(1-X) is symmetric, and B_{k,k}(1/2) = 1 for every k. -/
theorem belyiEvalQ_one_one_half_eq_one (k : ℕ) : belyiEvalQ (k * 1) (k * 1) (1 / 2) = 1 := by
  rw [belyiEvalQ_scaling]
  have h : belyiEvalQ 1 1 (1 / 2) = 1 := by
    have hc := belyiEvalQ_div_add_eq_one 1 1
    norm_num at hc ⊢
    exact hc
  rw [h, one_pow]

/-- The counterexample set: p = q = 1, u = 1/2 gives the full bad set. -/
theorem badParamSet_one_one_half : badParamSet (1 / 2) 1 1 = Set.univ :=
  badParamSet_eq_univ_of_eval_eq_one (1 / 2) 1 1 (belyiEvalQ_one_one_half_eq_one 1)

/-- DISPROOF of the stated target Prop badParamSet_finite. -/
theorem not_badParamSet_finite : ¬ badParamSet_finite := by
  intro h
  have hfin : (badParamSet (1 / 2) 1 1).Finite :=
    h (1 / 2) 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [badParamSet_one_one_half] at hfin
  have hinf : ¬ (Set.univ : Set ℕ).Finite := Set.infinite_univ
  exact hinf hfin

/-- DISPROOF of the stated target Prop exists_good_param. -/
theorem not_exists_good_param : ¬ exists_good_param := by
  intro h
  obtain ⟨k, -, hkne⟩ :=
    h (1 / 2) 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact hkne (belyiEvalQ_one_one_half_eq_one k)

/-- CORRECTED existence of a good parameter: k = 1 is good as soon as B_{p,q}(u) is not 1. -/
theorem exists_good_param_of_ne_one (u : ℚ) (p q : ℕ) (h : belyiEvalQ p q u ≠ 1) :
    ∃ k : ℕ, 0 < k ∧ belyiEvalQ (k * p) (k * q) u ≠ 1 := by
  refine ⟨1, one_pos, ?_⟩
  rw [belyiEvalQ_scaling]
  simpa using h

/-- The corrected replacement for the false Prop badParamSet_finite. -/
def badParamSet_finite_corrected : Prop :=
  ∀ (u : ℚ) (p q : ℕ), p ≠ 0 → q ≠ 0 → u ≠ 0 → u ≠ 1 →
    belyiEvalQ p q u ≠ 1 → belyiEvalQ p q u ≠ -1 → (badParamSet u p q).Finite

theorem badParamSet_finite_corrected_proof : badParamSet_finite_corrected := by
  intro u p q _ _ _ _ h1 h2
  exact badParamSet_finite_of_ne u p q h1 h2

/-- The corrected replacement for the false Prop exists_good_param. -/
def exists_good_param_corrected : Prop :=
  ∀ (u : ℚ) (p q : ℕ), p ≠ 0 → q ≠ 0 → u ≠ 0 → u ≠ 1 →
    belyiEvalQ p q u ≠ 1 → ∃ k : ℕ, 0 < k ∧ belyiEvalQ (k * p) (k * q) u ≠ 1

theorem exists_good_param_corrected_proof : exists_good_param_corrected := by
  intro u p q _ _ _ _ h
  exact exists_good_param_of_ne_one u p q h

/-- The Belyi value at a rational point in (Q minus {0,1}) is nonzero (for p, q positive). -/
theorem belyiEvalQ_ne_zero (p q : ℕ) (hp : p ≠ 0) (hq : q ≠ 0) (u : ℚ)
    (hu0 : u ≠ 0) (hu1 : u ≠ 1) : belyiEvalQ p q u ≠ 0 := by
  rw [belyiEvalQ_eq_belyiConst_mul]
  have hp' : (p : ℚ) ≠ 0 := by
    have h : (0 : ℚ) < (p : ℚ) := by exact_mod_cast Nat.pos_of_ne_zero hp
    linarith
  have hq' : (q : ℚ) ≠ 0 := by
    have h : (0 : ℚ) < (q : ℚ) := by exact_mod_cast Nat.pos_of_ne_zero hq
    linarith
  have hsum : ((p : ℚ) + q) ≠ 0 := by
    have h1 : (0 : ℚ) < (p : ℚ) := by exact_mod_cast Nat.pos_of_ne_zero hp
    have h2 : (0 : ℚ) < (q : ℚ) := by exact_mod_cast Nat.pos_of_ne_zero hq
    linarith
  have hc : belyiConst p q ≠ 0 := by
    unfold belyiConst
    exact div_ne_zero (pow_ne_zero _ hsum) (mul_ne_zero (pow_ne_zero _ hp') (pow_ne_zero _ hq'))
  exact mul_ne_zero (mul_ne_zero hc (pow_ne_zero _ hu0))
    (pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm hu1)))

/-! ### Collision variant: k with B_{kp,kq}(u) = B_{kp,kq}(v) -/

/-- The collision set: the parameters k with B_{kp,kq}(u) = B_{kp,kq}(v). -/
def collisionParamSet (u v : ℚ) (p q : ℕ) : Set ℕ :=
  {k : ℕ | belyiEvalQ (k * p) (k * q) u = belyiEvalQ (k * p) (k * q) v}

/-- For a nonzero base value at v, the collision set is the set of k with (B(u)/B(v))^k = 1. -/
theorem collisionParamSet_eq_of_ne_zero (u v : ℚ) (p q : ℕ)
    (hv : belyiEvalQ p q v ≠ 0) :
    collisionParamSet u v p q =
      {k : ℕ | (belyiEvalQ p q u / belyiEvalQ p q v) ^ k = 1} := by
  ext k
  simp only [collisionParamSet, Set.mem_setOf_eq, belyiEvalQ_scaling]
  constructor
  · intro h
    rw [div_pow, h, div_self (pow_ne_zero k hv)]
  · intro h
    rw [div_pow, div_eq_one_iff_eq (pow_ne_zero k hv)] at h
    exact h

/-- EXACT classification of the collision set: it is finite iff B(u) is neither B(v) nor -B(v).
The naive statement "finitely many collisions for every u != v" is false (see
collisionParamSet_one_one_quarter). -/
theorem collisionParamSet_finite_iff (u v : ℚ) (p q : ℕ)
    (hv : belyiEvalQ p q v ≠ 0) :
    (collisionParamSet u v p q).Finite ↔
      belyiEvalQ p q u ≠ belyiEvalQ p q v ∧
        belyiEvalQ p q u ≠ -belyiEvalQ p q v := by
  rw [collisionParamSet_eq_of_ne_zero u v p q hv, pow_setOf_eq_one_finite_iff]
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · intro he
      exact h1 (by rw [div_eq_one_iff_eq hv]; exact he)
    · intro he
      exact h2 (by rw [div_eq_iff hv]; rw [he]; ring)
  · rintro ⟨h1, h2⟩
    constructor
    · intro hd
      exact h1 ((div_eq_one_iff_eq hv).mp hd)
    · intro hd
      have hh : belyiEvalQ p q u = -1 * belyiEvalQ p q v := (div_eq_iff hv).mp hd
      exact h2 (by rw [hh]; ring)

/-- Collision classification in the natural hypotheses u, v outside {0,1} and p, q positive. -/
theorem collisionParamSet_finite_iff' (u v : ℚ) (p q : ℕ) (hp : p ≠ 0) (hq : q ≠ 0)
    (hu0 : u ≠ 0) (hu1 : u ≠ 1) (hv0 : v ≠ 0) (hv1 : v ≠ 1) :
    (collisionParamSet u v p q).Finite ↔
      belyiEvalQ p q u ≠ belyiEvalQ p q v ∧
        belyiEvalQ p q u ≠ -belyiEvalQ p q v :=
  collisionParamSet_finite_iff u v p q (belyiEvalQ_ne_zero p q hp hq v hv0 hv1)

/-- B_{1,1}(1/4) = B_{1,1}(3/4) = 3/4 (the symmetry u -> 1-u of 4X(1-X)). -/
theorem belyiEvalQ_one_one_quarter_eq_three_quarters :
    belyiEvalQ 1 1 (1 / 4) = belyiEvalQ 1 1 (3 / 4) := by
  norm_num [belyiEvalQ, TauCeti.eval_belyiPolynomial]

/-- The collision instance u = 1/4, v = 3/4 with p = q = 1, valid for every k. -/
theorem belyiEvalQ_collision_quarter (k : ℕ) :
    belyiEvalQ k k (1 / 4) = belyiEvalQ k k (3 / 4) := by
  have h1 := belyiEvalQ_scaling 1 1 (1 / 4) k
  have h2 := belyiEvalQ_scaling 1 1 (3 / 4) k
  rw [Nat.mul_one] at h1 h2
  rw [h1, h2, belyiEvalQ_one_one_quarter_eq_three_quarters]

/-- The collision counterexample set is all of N. -/
theorem collisionParamSet_one_one_quarter :
    collisionParamSet (1 / 4) (3 / 4) 1 1 = Set.univ := by
  apply Set.eq_univ_of_forall
  intro k
  show belyiEvalQ (k * 1) (k * 1) (1 / 4) = belyiEvalQ (k * 1) (k * 1) (3 / 4)
  simpa [Nat.mul_one] using belyiEvalQ_collision_quarter k

/-- DISPROOF of the naive collision statement (finite for every u != v). -/
theorem not_collision_finite_statement :
    ¬ (∀ (u v : ℚ) (p q : ℕ), u ≠ v → p ≠ 0 → q ≠ 0 → u ≠ 0 → u ≠ 1 →
        v ≠ 0 → v ≠ 1 → (collisionParamSet u v p q).Finite) := by
  intro h
  have hfin := h (1 / 4) (3 / 4) 1 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [collisionParamSet_one_one_quarter] at hfin
  have hinf : ¬ (Set.univ : Set ℕ).Finite := Set.infinite_univ
  exact hinf hfin

#print axioms belyiEvalQ_eq_belyiConst_mul
#print axioms rat_pow_self_mul_ne_zero
#print axioms belyiConst_pow_eq
#print axioms belyiConst_scaling
#print axioms belyiEvalQ_scaling
#print axioms badParamSet_eq_pow_one
#print axioms pow_eq_one_imp_eq_or_even
#print axioms pow_setOf_eq_one_subset_zero
#print axioms pow_setOf_eq_one_finite_iff
#print axioms badParamSet_eq_univ_of_eval_eq_one
#print axioms badParamSet_eq_even_of_eval_eq_neg_one
#print axioms badParamSet_subset_zero_of_ne
#print axioms badParamSet_finite_of_ne
#print axioms badParamSet_finite_iff
#print axioms belyiEvalQ_div_add_eq_one
#print axioms badParamSet_div_add_eq_univ
#print axioms belyiEvalQ_one_one_half_eq_one
#print axioms badParamSet_one_one_half
#print axioms not_badParamSet_finite
#print axioms not_exists_good_param
#print axioms exists_good_param_of_ne_one
#print axioms badParamSet_finite_corrected_proof
#print axioms exists_good_param_corrected_proof
#print axioms belyiEvalQ_ne_zero
#print axioms collisionParamSet_eq_of_ne_zero
#print axioms collisionParamSet_finite_iff
#print axioms collisionParamSet_finite_iff'
#print axioms belyiEvalQ_one_one_quarter_eq_three_quarters
#print axioms belyiEvalQ_collision_quarter
#print axioms collisionParamSet_one_one_quarter
#print axioms not_collision_finite_statement

end LeanFormal.IUT.XiFPaper.Mzk1BadParamProofActual

end
