import tmp.external.ported.tauceti_belyi_core.TauCeti.Algebra.Polynomial.Belyi
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

noncomputable section

/-!
# Beta-avoiding Belyi construction over ℚ: the general (all S) case

Target of this file: for every finite S : Finset ℚ and every β : ℚ with β ∉ S, produce a
polynomial q : ℚ[X] with 0 < q.natDegree, q(s) ∈ {0,1} for all s ∈ S,
q(β) ∉ {0,1}, and all critical values of q in {0,1}.

CritIn01 q below is the *precise aeval form* of the critical-value condition requested by
the task: forall z : ℂ, aeval z (derivative q) = 0 -> aeval z q = 0 or aeval z q = 1.

## What is proved here

* critIn01_iff_criticalValues : the aeval form is equivalent (for nonconstant q) to
  q.criticalValues ℂ ⊆ {0,1} in the sense of the ported TauCeti CriticalValues file.
* critIn01_comp : critical-value control is stable under composition, provided the outer
  polynomial maps 0 and 1 into {0,1}.  (This re-proves the private TauCeti lemma
  criticalValues_comp_subset_zero_one in the aeval formulation used here.)
* exists_betaAvoiding_card_le_two : the base case S.card ≤ 2 of the induction,
  *unconditional*.
* BetaAvoidingStep : the single missing parametric lemma (a beta-avoiding degree reduction
  with a strict cardinality drop), stated exactly.
* exists_betaAvoiding_of_step : the induction: BetaAvoidingStep implies the full target
  for every finite S.  So the whole remaining gap is the single named Prop BetaAvoidingStep.
* tauCetiStep_not_betaAvoiding : **obstruction**.  The ported TauCeti three-point step
  (TauCeti.exists_card_image_lt, i.e. a Belyi polynomial B_{m,n} composed with the affine
  normalization min -> 0, max -> 1) is *provably not* beta-avoiding: for S = {0,1,3} and
  β = 4 the forced shape is m/(m+n) = 1/3, and for **every** admissible (m,n) one has
  B_{m,n}(4/3) = 1, i.e. the step output satisfies f(4) = 1 ∈ f(S).
* example_solvable_two_step : the target itself is nevertheless satisfiable for that instance
  (explicit two-step witness B_{8,1} composed with B_{1,1}(X/3)), so the obstruction is a
  property of the canonical step and not a counterexample to the theorem.
* belyi_eval_one_imp : **uniqueness of the normalized maximum** (interior branch):
  0 < u < 1 and B_{m,n}(u) = 1 imply u = m/(m+n), proved from the ported derivative identity
  X(1-X)B' = B(m-(m+n)X) together with Rolle's theorem.  Consequently
  (belyi_eval_mem_zero_one_of_interior) a point u strictly inside (0,1) is mapped into {0,1}
  only if u is the critical point m/(m+n): inside the range the canonical step *does* avoid
  {0,1}, so the obstruction above is a genuinely outside-the-range phenomenon.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1BetaAvoidingBelyiRationalActual

open Polynomial
open TauCeti

/-- CritIn01 q: every critical point of q (over ℂ) is mapped into {0,1}.  This is the
precise aeval formulation of CV(q) ⊆ {0,1} used as the target of this file. -/
def CritIn01 (q : ℚ[X]) : Prop :=
  ∀ z : ℂ, Polynomial.aeval z (Polynomial.derivative q) = 0 →
    Polynomial.aeval z q = 0 ∨ Polynomial.aeval z q = 1

/-- For a nonconstant polynomial the aeval formulation of the critical-value condition is
equivalent to the criticalValues inclusion of the ported TauCeti file. -/
theorem critIn01_iff_criticalValues {q : ℚ[X]} (hq : 0 < q.natDegree) :
    CritIn01 q ↔ q.criticalValues ℂ ⊆ {0, 1} := by
  constructor
  · intro h y hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hzero : Polynomial.aeval x (Polynomial.derivative q) = 0 :=
      Polynomial.aeval_eq_zero_of_mem_rootSet hx
    rcases h x hzero with h' | h'
    · simp [h']
    · simp [h']
  · intro h z hz
    have hder : Polynomial.derivative q ≠ 0 := Polynomial.derivative_ne_zero.mpr hq.ne'
    have hx : z ∈ (Polynomial.derivative q).rootSet ℂ :=
      (Polynomial.mem_rootSet_of_ne hder).mpr hz
    have hmem : Polynomial.aeval z q ∈ q.criticalValues ℂ := ⟨z, hx, rfl⟩
    have h' := h hmem
    simpa using h'

/-- A rational value p.eval 0 ∈ {0,1} is also a complex critical-permissible centre. -/
theorem aeval_zero_of_eval_zero_mem {p : ℚ[X]} (h : p.eval 0 ∈ ({0, 1} : Set ℚ)) :
    Polynomial.aeval (0 : ℂ) p ∈ ({0, 1} : Set ℂ) := by
  have h0 : (0 : ℂ) = algebraMap ℚ ℂ 0 := by simp
  rw [h0, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]
  rcases h with h | h
  · rw [h]; simp
  · rw [h]; simp

/-- A rational value p.eval 1 ∈ {0,1} is also a complex critical-permissible centre. -/
theorem aeval_one_of_eval_one_mem {p : ℚ[X]} (h : p.eval 1 ∈ ({0, 1} : Set ℚ)) :
    Polynomial.aeval (1 : ℂ) p ∈ ({0, 1} : Set ℂ) := by
  have h0 : (1 : ℂ) = algebraMap ℚ ℂ 1 := by simp
  rw [h0, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]
  rcases h with h | h
  · rw [h]; simp
  · rw [h]; simp

/-- Composition preserves CritIn01, provided the outer factor sends 0 and 1 into {0,1}.
(Public re-proof of the TauCeti private lemma criticalValues_comp_subset_zero_one, in the
aeval formulation.) -/
theorem critIn01_comp {p q : ℚ[X]} (hp : 0 < p.natDegree) (hq : 0 < q.natDegree)
    (hp0 : p.eval 0 ∈ ({0, 1} : Set ℚ)) (hp1 : p.eval 1 ∈ ({0, 1} : Set ℚ))
    (hpC : CritIn01 p) (hqC : CritIn01 q) : CritIn01 (p.comp q) := by
  have hcomp : 0 < (p.comp q).natDegree := by
    rw [Polynomial.natDegree_comp]
    exact Nat.mul_pos hp hq
  rw [critIn01_iff_criticalValues hcomp]
  have hq' : q.criticalValues ℂ ⊆ {0, 1} := (critIn01_iff_criticalValues hq).mp hqC
  have hp' : p.criticalValues ℂ ⊆ {0, 1} := (critIn01_iff_criticalValues hp).mp hpC
  refine (Polynomial.criticalValues_comp_subset p q).trans (Set.union_subset ?_ hp')
  rintro - ⟨y, hy, rfl⟩
  rcases hq' hy with h | h
  · rw [h]
    exact aeval_zero_of_eval_zero_mem hp0
  · rw [h]
    exact aeval_one_of_eval_one_mem hp1

/-- The value of B_{m,n} composed with the affine map c (X - s), at x. -/
theorem eval_belyi_affine (m n : ℕ) (c s x : ℚ) :
    ((belyiPolynomial ℚ m n).comp (Polynomial.C c * (Polynomial.X - Polynomial.C s))).eval x
      = (belyiPolynomial ℚ m n).eval (c * (x - s)) := by
  rw [Polynomial.eval_comp]
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X]

/-- A Belyi polynomial pre-composed with a nonconstant affine map still has all its critical
values in {0,1} (and remains nonconstant). -/
theorem critIn01_belyi_affine (m n : ℕ) (hmn : 0 < m + n) (c s : ℚ) (hc : c ≠ 0) :
    0 < ((belyiPolynomial ℚ m n).comp (Polynomial.C c * (Polynomial.X - Polynomial.C s))).natDegree ∧
    CritIn01 ((belyiPolynomial ℚ m n).comp (Polynomial.C c * (Polynomial.X - Polynomial.C s))) := by
  have hA : (Polynomial.C c * (Polynomial.X - Polynomial.C s) : ℚ[X]).natDegree = 1 := by
    rw [Polynomial.natDegree_C_mul hc, Polynomial.natDegree_X_sub_C]
  have hnd : ((belyiPolynomial ℚ m n).comp
      (Polynomial.C c * (Polynomial.X - Polynomial.C s))).natDegree = m + n := by
    rw [Polynomial.natDegree_comp, natDegree_belyiPolynomial, hA, mul_one]
  refine ⟨by rw [hnd]; exact hmn, ?_⟩
  rw [critIn01_iff_criticalValues (by rw [hnd]; exact hmn)]
  refine (Polynomial.criticalValues_comp_subset (belyiPolynomial ℚ m n)
    (Polynomial.C c * (Polynomial.X - Polynomial.C s))).trans
    (Set.union_subset ?_ (criticalValues_belyiPolynomial_subset ℂ m n))
  simp [Polynomial.criticalValues_eq_empty_of_natDegree_le_one (R := ℚ) (S := ℂ) hA.le]

/-- **Base case of the induction.**  For at most two prescribed rational points and any
excluded rational value β there is a nonconstant rational polynomial with all critical values
in {0,1}, mapping the prescribed points into {0,1} and β outside {0,1}. -/
theorem exists_betaAvoiding_card_le_two (S : Finset ℚ) (hS : S.card ≤ 2) (β : ℚ) (hβ : β ∉ S) :
    ∃ q : ℚ[X], 0 < q.natDegree ∧ CritIn01 q ∧
      (∀ s ∈ S, q.eval s = 0 ∨ q.eval s = 1) ∧ q.eval β ≠ 0 ∧ q.eval β ≠ 1 := by
  have hcard : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 := by omega
  rcases hcard with h | h | h
  · -- no prescribed point: an affine map
    have hSe : S = ∅ := Finset.card_eq_zero.mp h
    have hnd : (Polynomial.X + Polynomial.C (2 - β) : ℚ[X]).natDegree = 1 :=
      Polynomial.natDegree_X_add_C _
    have hev : (Polynomial.X + Polynomial.C (2 - β) : ℚ[X]).eval β = 2 := by
      rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]; ring
    refine ⟨Polynomial.X + Polynomial.C (2 - β), by rw [hnd]; norm_num, ?_, ?_, ?_, ?_⟩
    · rw [critIn01_iff_criticalValues (by rw [hnd]; norm_num)]
      rw [Polynomial.criticalValues_eq_empty_of_natDegree_le_one (R := ℚ) (S := ℂ) (by rw [hnd])]
      simp
    · intro s hs
      rw [hSe] at hs
      simp at hs
    · rw [hev]; norm_num
    · rw [hev]; norm_num
  · -- one prescribed point s: β - s is nonzero, so 2/(β-s) (β-s) = 2 is a value where
    -- B_{1,1} takes the value -8
    obtain ⟨s, rfl⟩ := Finset.card_eq_one.mp h
    have hβs : β ≠ s := fun hh => hβ (by rw [hh]; simp)
    have hu : β - s ≠ 0 := sub_ne_zero.mpr hβs
    have hc : 2 / (β - s) ≠ 0 := div_ne_zero (by norm_num) hu
    have hgood : ((belyiPolynomial ℚ 1 1).comp
        (Polynomial.C (2 / (β - s)) * (Polynomial.X - Polynomial.C s))).eval β = -8 := by
      rw [eval_belyi_affine]
      have hv : 2 / (β - s) * (β - s) = 2 := by field_simp
      rw [hv, TauCeti.eval_belyiPolynomial]
      norm_num
    refine ⟨(belyiPolynomial ℚ 1 1).comp
      (Polynomial.C (2 / (β - s)) * (Polynomial.X - Polynomial.C s)), ?_, ?_, ?_, ?_, ?_⟩
    · exact (critIn01_belyi_affine 1 1 (by norm_num) (2 / (β - s)) s hc).1
    · exact (critIn01_belyi_affine 1 1 (by norm_num) (2 / (β - s)) s hc).2
    · intro x hx
      rw [Finset.mem_singleton] at hx
      rw [hx]
      left
      rw [eval_belyi_affine]
      have h0 : 2 / (β - s) * (s - s) = 0 := by ring
      rw [h0, TauCeti.eval_belyiPolynomial]
      norm_num
    · rw [hgood]; norm_num
    · rw [hgood]; norm_num
  · -- two prescribed points a, b: normalize to 0 and 1.  B_{1,1} works unless the image of β
    -- is the midpoint 1/2, in which case B_{1,2} works.
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h
    have hβa : β ≠ a := fun hh => hβ (by rw [hh]; simp)
    have hβb : β ≠ b := fun hh => hβ (by rw [hh]; simp)
    have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
    have hcinv : (b - a)⁻¹ ≠ 0 := inv_ne_zero hba
    have hs_eq : (b - a)⁻¹ * (a - a) = 0 := by ring
    have ht_eq : (b - a)⁻¹ * (b - a) = 1 := inv_mul_cancel₀ hba
    have hva : (b - a)⁻¹ * (β - a) ≠ 0 :=
      mul_ne_zero hcinv (sub_ne_zero.mpr hβa)
    have hvb : (b - a)⁻¹ * (β - a) ≠ 1 := by
      intro hh
      apply hβb
      have hmul : ((b - a)⁻¹ * (β - a)) * (b - a) = (b - a) := by rw [hh, one_mul]
      have hmul2 : ((b - a)⁻¹ * (β - a)) * (b - a) = (β - a) := by
        rw [mul_assoc, mul_comm (β - a) (b - a), ← mul_assoc, inv_mul_cancel₀ hba, one_mul]
      rw [hmul2] at hmul
      linarith
    set q1 : ℚ[X] := (belyiPolynomial ℚ 1 1).comp
      (Polynomial.C ((b - a)⁻¹) * (Polynomial.X - Polynomial.C a)) with hq1
    have hq1a : q1.eval a = 0 := by
      rw [hq1, eval_belyi_affine]
      rw [hs_eq, TauCeti.eval_belyiPolynomial]
      norm_num
    have hq1b : q1.eval b = 0 := by
      rw [hq1, eval_belyi_affine]
      rw [ht_eq, TauCeti.eval_belyiPolynomial]
      norm_num
    by_cases hbad : q1.eval β ∈ ({0, 1} : Set ℚ)
    · -- bad branch: q1.eval β = 4 v (1 - v) with v = (b-a)⁻¹(β-a); v ≠ 0, 1 forces v = 1/2
      have hvform : q1.eval β = 4 * ((b - a)⁻¹ * (β - a)) *
          (1 - (b - a)⁻¹ * (β - a)) := by
        rw [hq1, eval_belyi_affine, TauCeti.eval_belyiPolynomial]
        norm_num
      have hhalf : (b - a)⁻¹ * (β - a) = 1 / 2 := by
        rw [hvform] at hbad
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hbad
        rcases hbad with h0 | h0
        · rcases mul_eq_zero.mp h0 with h1 | h1
          · rcases mul_eq_zero.mp h1 with h2 | h2
            · exact absurd h2 (by norm_num)
            · exact absurd h2 hva
          · exact absurd (by linarith : (b - a)⁻¹ * (β - a) = 1) hvb
        · have h2 : (2 * ((b - a)⁻¹ * (β - a)) - 1) ^ 2 = 0 := by
            linear_combination -h0
          have h3 : 2 * ((b - a)⁻¹ * (β - a)) - 1 = 0 := by
            simpa using h2
          linarith
      have hgood2 : ((belyiPolynomial ℚ 1 2).comp
          (Polynomial.C ((b - a)⁻¹) * (Polynomial.X - Polynomial.C a))).eval β = 27 / 32 := by
        rw [eval_belyi_affine, hhalf, TauCeti.eval_belyiPolynomial]
        norm_num
      refine ⟨(belyiPolynomial ℚ 1 2).comp
        (Polynomial.C ((b - a)⁻¹) * (Polynomial.X - Polynomial.C a)), ?_, ?_, ?_, ?_, ?_⟩
      · exact (critIn01_belyi_affine 1 2 (by norm_num) _ a hcinv).1
      · exact (critIn01_belyi_affine 1 2 (by norm_num) _ a hcinv).2
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · left
          rw [eval_belyi_affine]
          rw [hs_eq, TauCeti.eval_belyiPolynomial]
          norm_num
        · left
          rw [eval_belyi_affine]
          rw [ht_eq, TauCeti.eval_belyiPolynomial]
          norm_num
      · rw [hgood2]; norm_num
      · rw [hgood2]; norm_num
    · refine ⟨q1, (critIn01_belyi_affine 1 1 (by norm_num) _ a hcinv).1,
        (critIn01_belyi_affine 1 1 (by norm_num) _ a hcinv).2, ?_, ?_, ?_⟩
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · left; exact hq1a
        · left; exact hq1b
      · intro hh
        exact hbad (by rw [hh]; simp)
      · intro hh
        exact hbad (by rw [hh]; simp)

/-! ### The single missing parametric lemma, and the reduction of the target to it -/

/-- **The missing parametric lemma (named gap, class-B candidate; NOT proved here).**

For every finite set S of rational numbers with 2 < S.card and every β ∉ S there is a
nonconstant rational polynomial f such that

* all critical values of f lie in {0,1} (CritIn01 f);
* the image f(S) is strictly smaller than S, and contains both 0 and 1
  (so the critical values of f are images of points of S, which is what makes the
  composite critical-value bookkeeping work);
* f(β) is *not* in the image f(S) (this is the beta-tracking condition; only
  f(β) ∉ {0,1} would not suffice, because f(β) = f(s) for some s ∈ S can never be
  repaired by a later composition).

The obstruction proved below (tauCetiStep_not_betaAvoiding) shows that the *canonical*
TauCeti three-point step does **not** satisfy this, so this is a genuine extra statement
and not a restatement of TauCeti.exists_card_image_lt. -/
def BetaAvoidingStep : Prop :=
  ∀ (S : Finset ℚ) (β : ℚ), 2 < S.card → β ∉ S →
    ∃ f : ℚ[X], 0 < f.natDegree ∧ CritIn01 f ∧
      (S.image (fun x => f.eval x)).card < S.card ∧
      (0 : ℚ) ∈ S.image (fun x => f.eval x) ∧
      (1 : ℚ) ∈ S.image (fun x => f.eval x) ∧
      f.eval β ∉ S.image (fun x => f.eval x)

/-- **Reduction theorem**: the parametric step lemma BetaAvoidingStep implies the full
beta-avoiding Belyi construction for every finite set of rational points.

The induction is on S.card; the base case S.card ≤ 2 is unconditional
(exists_betaAvoiding_card_le_two).  In the step, T := f(S) is a strictly smaller set
containing 0 and 1, f(β) ∉ T, and the induction hypothesis applied to (T, f β) gives
q; then q.comp f is the answer, because CritIn01 is stable under composition
(critIn01_comp) and 0, 1 ∈ T, so the induction hypothesis gives q(0), q(1) ∈ {0,1}. -/
theorem exists_betaAvoiding_of_step (hstep : BetaAvoidingStep) :
    ∀ (S : Finset ℚ) (β : ℚ), β ∉ S →
      ∃ q : ℚ[X], 0 < q.natDegree ∧ CritIn01 q ∧
        (∀ s ∈ S, q.eval s = 0 ∨ q.eval s = 1) ∧ q.eval β ≠ 0 ∧ q.eval β ≠ 1 := by
  suffices H : ∀ n, ∀ (S : Finset ℚ) (β : ℚ), S.card = n → β ∉ S →
      ∃ q : ℚ[X], 0 < q.natDegree ∧ CritIn01 q ∧
        (∀ s ∈ S, q.eval s = 0 ∨ q.eval s = 1) ∧ q.eval β ≠ 0 ∧ q.eval β ≠ 1 by
    intro S β hβ
    exact H S.card S β rfl hβ
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S β hcard hβ
    by_cases hle : S.card ≤ 2
    · exact exists_betaAvoiding_card_le_two S hle β hβ
    · have h3 : 2 < S.card := by omega
      obtain ⟨f, hfdeg, hfC, hTcard, hT0, hT1, hfβ⟩ := hstep S β h3 hβ
      obtain ⟨q, hqdeg, hqC, hqT, hqβ0, hqβ1⟩ :=
        ih (S.image (fun x => f.eval x)).card (by omega) (S.image (fun x => f.eval x))
          (f.eval β) rfl hfβ
      refine ⟨q.comp f, ?_, ?_, ?_, ?_, ?_⟩
      · rw [Polynomial.natDegree_comp]
        exact Nat.mul_pos hqdeg hfdeg
      · exact critIn01_comp hqdeg hfdeg (hqT 0 hT0) (hqT 1 hT1) hqC hfC
      · intro s hs
        rw [Polynomial.eval_comp]
        exact hqT (f.eval s) (Finset.mem_image_of_mem _ hs)
      · intro hh
        rw [Polynomial.eval_comp] at hh
        exact hqβ0 hh
      · intro hh
        rw [Polynomial.eval_comp] at hh
        exact hqβ1 hh

/-! ### Obstruction: the canonical TauCeti three-point step is not beta-avoiding -/

/-- A Belyi polynomial pre-composed with ANY affine map of natDegree 1 keeps all critical
values in {0,1} (general form of critIn01_belyi_affine). -/
theorem critIn01_belyi_comp_linear {A : ℚ[X]} (hA : A.natDegree = 1) (m n : ℕ) (hmn : 0 < m + n) :
    0 < ((belyiPolynomial ℚ m n).comp A).natDegree ∧
      CritIn01 ((belyiPolynomial ℚ m n).comp A) := by
  have hnd : ((belyiPolynomial ℚ m n).comp A).natDegree = m + n := by
    rw [Polynomial.natDegree_comp, natDegree_belyiPolynomial, hA, mul_one]
  refine ⟨by rw [hnd]; exact hmn, ?_⟩
  rw [critIn01_iff_criticalValues (by rw [hnd]; exact hmn)]
  refine (Polynomial.criticalValues_comp_subset (belyiPolynomial ℚ m n) A).trans
    (Set.union_subset ?_ (criticalValues_belyiPolynomial_subset ℂ m n))
  simp [Polynomial.criticalValues_eq_empty_of_natDegree_le_one (R := ℚ) (S := ℂ) hA.le]

/-- The scaling identity inside the family with fixed critical point r = 1/3:
B_{m,2m}(t) = (27/4)^m t^m (1-t)^{2m}, i.e. B_{m,2m} is the m-th power of B_{1,2}. -/
theorem eval_belyi_two_mul (m : ℕ) (hm : 1 ≤ m) (t : ℚ) :
    (belyiPolynomial ℚ m (2 * m)).eval t = (27 / 4) ^ m * t ^ m * (1 - t) ^ (2 * m) := by
  have hmQ : (m : ℚ) ≠ 0 := by positivity
  have hcast1 : ((m : ℚ) + ((2 * m : ℕ) : ℚ)) = 3 * (m : ℚ) := by push_cast; ring
  have hcast2 : ((2 * m : ℕ) : ℚ) = 2 * (m : ℚ) := by push_cast; ring
  have hexp : m + 2 * m = 3 * m := by omega
  have hmain : (3 : ℚ) ^ (3 * m) * (m : ℚ) ^ (3 * m) /
      ((m : ℚ) ^ m * ((2 : ℚ) ^ (2 * m) * (m : ℚ) ^ (2 * m))) = (27 / 4) ^ m := by
    have h3 : (3 : ℚ) ^ (3 * m) = (27 : ℚ) ^ m := by
      rw [pow_mul, show (3 : ℚ) ^ 3 = 27 by norm_num]
    have h4 : (2 : ℚ) ^ (2 * m) = (4 : ℚ) ^ m := by
      rw [pow_mul, show (2 : ℚ) ^ 2 = 4 by norm_num]
    have h1 : (m : ℚ) ^ m * (m : ℚ) ^ (2 * m) = (m : ℚ) ^ (3 * m) := by
      rw [← pow_add, show m + 2 * m = 3 * m by omega]
    have hden : (m : ℚ) ^ m * ((2 : ℚ) ^ (2 * m) * (m : ℚ) ^ (2 * m))
        = (2 : ℚ) ^ (2 * m) * (m : ℚ) ^ (3 * m) := by
      rw [← h1]; ring
    rw [hden, h3, h4, div_pow]
    have hmne : (m : ℚ) ^ (3 * m) ≠ 0 := pow_ne_zero _ hmQ
    have h4m : (4 : ℚ) ^ m ≠ 0 := by positivity
    field_simp
  rw [TauCeti.eval_belyiPolynomial, hcast1, hcast2, hexp, mul_pow, mul_pow, hmain]

/-- **Obstruction to the suggested strategy.**  For S = {0,1,3} and β = 4 the canonical
TauCeti three-point step (TauCeti.exists_card_image_lt) normalizes min = 0 to 0 and max = 3
to 1 and is forced to put the third point c = 1 at the critical point r = m/(m+n) = 1/3.
For EVERY admissible (m,n) the resulting step output f = B_{m,n}(X/3) then satisfies
f(4) = 1 = f(1) ∈ f(S): the beta-tracking condition f(β) ∉ f(S) FAILS.  So the canonical
step cannot prove BetaAvoidingStep. -/
theorem tauCetiStep_not_betaAvoiding (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hr : (m : ℚ) / (m + n) = 1 / 3) :
    ((belyiPolynomial ℚ m n).comp (Polynomial.C (1 / 3) * Polynomial.X)).eval 4 = 1 ∧
      ((belyiPolynomial ℚ m n).comp (Polynomial.C (1 / 3) * Polynomial.X)).eval 1 = 1 := by
  have hval : ∀ x : ℚ, ((belyiPolynomial ℚ m n).comp
      (Polynomial.C (1 / 3) * Polynomial.X)).eval x
        = (belyiPolynomial ℚ m n).eval ((1 / 3) * x) := by
    intro x
    rw [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  have hthree : (m : ℚ) * 3 = (m : ℚ) + (n : ℚ) := by
    have h := hr
    field_simp at h
    linarith
  have hn2 : n = 2 * m := by
    have h' : (n : ℚ) = 2 * (m : ℚ) := by linarith
    exact_mod_cast h'
  constructor
  · rw [hval]
    have h43 : (1 / 3 : ℚ) * 4 = 4 / 3 := by norm_num
    rw [h43, hn2, eval_belyi_two_mul m hm]
    have hA : (27 / 4 : ℚ) ^ m * (4 / 3 : ℚ) ^ m = (9 : ℚ) ^ m := by
      rw [← mul_pow]; norm_num
    have hB : (1 - 4 / 3 : ℚ) = -(1 / 3) := by norm_num
    rw [hA, hB]
    have hC : (-(1 / 3) : ℚ) ^ (2 * m) = ((1 / 9 : ℚ)) ^ m := by
      rw [pow_mul]; norm_num
    rw [hC, ← mul_pow]
    norm_num
  · rw [hval]
    have h13 : (1 / 3 : ℚ) * 1 = 1 / 3 := by norm_num
    rw [h13, ← hr]
    exact eval_div_belyiPolynomial (K := ℚ) m n

/-- **The obstruction is not a counterexample.**  For S = {0,1,3} and β = 4 the target of the
task is nevertheless satisfiable, by the explicit two-step composite
q = B_{8,1} ∘ B_{1,1}(X/3): q maps 0 and 3 to 0, 1 to 1, and 4 to 6400.  Hence only the
one-step parametric lemma needs a genuinely different (multi-step or non-canonical) proof. -/
theorem example_solvable_two_step :
    ∃ q : ℚ[X], 0 < q.natDegree ∧ CritIn01 q ∧
      (∀ s ∈ ({0, 1, 3} : Finset ℚ), q.eval s = 0 ∨ q.eval s = 1) ∧
      q.eval 4 ≠ 0 ∧ q.eval 4 ≠ 1 := by
  set g : ℚ[X] := (belyiPolynomial ℚ 1 1).comp (Polynomial.C (1 / 3) * Polynomial.X) with hg
  have hA1 : (Polynomial.C (1 / 3) * Polynomial.X : ℚ[X]).natDegree = 1 := by
    rw [Polynomial.natDegree_C_mul (by norm_num), Polynomial.natDegree_X]
  have hgpair := critIn01_belyi_comp_linear hA1 1 1 (by norm_num)
  have hgnd : g.natDegree = 2 := by
    rw [hg, Polynomial.natDegree_comp, natDegree_belyiPolynomial, hA1, mul_one]
  have hgdeg : 0 < g.natDegree := by rw [hgnd]; norm_num
  have hgC : CritIn01 g := hgpair.2
  have hg_eval : ∀ x : ℚ, g.eval x = (belyiPolynomial ℚ 1 1).eval ((1 / 3) * x) := by
    intro x
    rw [hg, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  have hg0 : g.eval 0 = 0 := by
    rw [hg_eval, show (1 / 3 : ℚ) * 0 = 0 by norm_num]
    exact TauCeti.eval_zero_belyiPolynomial (K := ℚ) (m := 1) (by norm_num) 1
  have hg1 : g.eval 1 = 8 / 9 := by
    rw [hg_eval, show (1 / 3 : ℚ) * 1 = 1 / 3 by norm_num, TauCeti.eval_belyiPolynomial]
    norm_num
  have hg3 : g.eval 3 = 0 := by
    rw [hg_eval, show (1 / 3 : ℚ) * 3 = 1 by norm_num]
    exact TauCeti.eval_one_belyiPolynomial (K := ℚ) 1 (n := 1) (by norm_num)
  have hg4 : g.eval 4 = -16 / 9 := by
    rw [hg_eval, show (1 / 3 : ℚ) * 4 = 4 / 3 by norm_num, TauCeti.eval_belyiPolynomial]
    norm_num
  have hq4 : ((belyiPolynomial ℚ 8 1).comp g).eval 4 = 6400 := by
    rw [Polynomial.eval_comp, hg4, TauCeti.eval_belyiPolynomial]
    norm_num
  have hp0 : (belyiPolynomial ℚ 8 1).eval 0 ∈ ({0, 1} : Set ℚ) := by
    rw [TauCeti.eval_zero_belyiPolynomial (K := ℚ) (m := 8) (by norm_num) 1]
    simp
  have hp1 : (belyiPolynomial ℚ 8 1).eval 1 ∈ ({0, 1} : Set ℚ) := by
    rw [TauCeti.eval_one_belyiPolynomial (K := ℚ) 8 (n := 1) (by norm_num)]
    simp
  have hpdeg : 0 < (belyiPolynomial ℚ 8 1).natDegree := by
    rw [natDegree_belyiPolynomial]; norm_num
  have hpC : CritIn01 (belyiPolynomial ℚ 8 1) :=
    (critIn01_iff_criticalValues hpdeg).mpr (criticalValues_belyiPolynomial_subset ℂ 8 1)
  refine ⟨(belyiPolynomial ℚ 8 1).comp g, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Polynomial.natDegree_comp, natDegree_belyiPolynomial, hgnd]
    norm_num
  · exact critIn01_comp hpdeg hgdeg hp0 hp1 hpC hgC
  · intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with h | h | h
    · rw [h, Polynomial.eval_comp, hg0]
      exact Or.inl (TauCeti.eval_zero_belyiPolynomial (K := ℚ) (m := 8) (by norm_num) 1)
    · rw [h, Polynomial.eval_comp, hg1, TauCeti.eval_belyiPolynomial]
      norm_num
    · rw [h, Polynomial.eval_comp, hg3]
      exact Or.inl (TauCeti.eval_zero_belyiPolynomial (K := ℚ) (m := 8) (by norm_num) 1)
  · rw [hq4]; norm_num
  · rw [hq4]; norm_num

/-! ### Interior branch: uniqueness of the normalized maximum -/

/-- Core of the uniqueness argument: two distinct points of (0,1) whose common value is 1
cannot have the critical point r = m/(m+n) among them.  Rolle's theorem on the interval they
span produces an interior critical point, and the ported identity
X(1-X)B' = B (m - (m+n)X) shows that the only critical point of B in (0,1) is r. -/
theorem belyi_no_two_preimages_one {m n : ℕ} (hm : 1 ≤ m) {a b : ℝ} (hab : a < b) (h0 : 0 < a)
    (h1 : b < 1) (ha : (belyiPolynomial ℝ m n).eval a = 1)
    (hb : (belyiPolynomial ℝ m n).eval b = 1)
    (hend : a = (m : ℝ) / ((m : ℝ) + n) ∨ b = (m : ℝ) / ((m : ℝ) + n)) : False := by
  obtain ⟨c, hc, hc0⟩ := exists_hasDerivAt_eq_zero
    (f := fun x : ℝ => (belyiPolynomial ℝ m n).eval x)
    (f' := fun x : ℝ => (belyiPolynomial ℝ m n).derivative.eval x) hab
    (belyiPolynomial ℝ m n).continuousOn (by rw [ha, hb])
    (fun x _ => (belyiPolynomial ℝ m n).hasDerivAt x)
  obtain ⟨hac, hcb⟩ := hc
  have hcpos : 0 < c := lt_trans h0 hac
  have hclt : c < 1 := lt_trans hcb h1
  have hpc : (belyiPolynomial ℝ m n).eval c ≠ 0 := by
    rw [TauCeti.eval_belyiPolynomial]
    refine mul_ne_zero (mul_ne_zero (TauCeti.belyiConstant_ne_zero (K := ℝ) m n)
      (pow_ne_zero _ hcpos.ne')) (pow_ne_zero _ ?_)
    rw [sub_ne_zero]
    exact hclt.ne'
  have hid := congr_arg (Polynomial.eval c)
    (TauCeti.X_mul_one_sub_X_mul_derivative_belyiPolynomial (K := ℝ) m n)
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one,
    Polynomial.eval_C] at hid
  rw [hc0, mul_zero] at hid
  have hlin : (m : ℝ) - ((m : ℝ) + n) * c = 0 := by
    rcases mul_eq_zero.mp hid.symm with h | h
    · exact absurd h hpc
    · exact h
  have hmR : (0 : ℝ) < (m : ℝ) := by
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hden : (m : ℝ) + n ≠ 0 := by
    have hpos : (0 : ℝ) < (m : ℝ) + n := by positivity
    exact hpos.ne'
  have hcr : c = (m : ℝ) / ((m : ℝ) + n) := by
    rw [eq_div_iff hden]
    linarith
  rcases hend with h | h
  · linarith
  · linarith

/-- **Uniqueness of the normalized maximum** (real form): for 0 < u < 1, B_{m,n}(u) = 1
forces u = m/(m+n). -/
theorem belyi_eval_one_imp_real (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) {u : ℝ}
    (h0 : 0 < u) (h1 : u < 1) (hu : (belyiPolynomial ℝ m n).eval u = 1) :
    u = (m : ℝ) / ((m : ℝ) + n) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hnR : (0 : ℝ) < (n : ℝ) := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hden : (0 : ℝ) < (m : ℝ) + n := by linarith
  have hvalr : (belyiPolynomial ℝ m n).eval ((m : ℝ) / ((m : ℝ) + n)) = 1 :=
    TauCeti.eval_div_belyiPolynomial (K := ℝ) m n
  have hr0 : 0 < (m : ℝ) / ((m : ℝ) + n) := div_pos hmR hden
  have hr1 : (m : ℝ) / ((m : ℝ) + n) < 1 := by
    rw [div_lt_one hden]
    linarith
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact belyi_no_two_preimages_one hm hlt h0 hr1 hu hvalr (Or.inr rfl)
  · exact belyi_no_two_preimages_one hm hlt hr0 h1 hvalr hu (Or.inl rfl)

/-- **Uniqueness of the normalized maximum** (rational form): for 0 < u < 1,
B_{m,n}(u) = 1 forces u = m/(m+n). -/
theorem belyi_eval_one_imp (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) {u : ℚ}
    (h0 : 0 < u) (h1 : u < 1) (hu : (belyiPolynomial ℚ m n).eval u = 1) :
    u = (m : ℚ) / (m + n) := by
  have h0R : (0 : ℝ) < (u : ℝ) := by exact_mod_cast h0
  have h1R : (u : ℝ) < 1 := by exact_mod_cast h1
  have huR : (belyiPolynomial ℝ m n).eval (u : ℝ) = 1 := by
    have h1' : algebraMap ℚ ℝ ((belyiPolynomial ℚ m n).eval u) = 1 := by rw [hu]; simp
    have h2 : (belyiPolynomial ℝ m n).eval (algebraMap ℚ ℝ u) = 1 := by
      rw [← TauCeti.map_belyiPolynomial (f := algebraMap ℚ ℝ), Polynomial.eval_map_algebraMap,
        Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]
      simpa using h1'
    exact h2
  have hres := belyi_eval_one_imp_real m n hm hn h0R h1R huR
  have hcast : ((m : ℚ) / (m + n) : ℝ) = (m : ℝ) / ((m : ℝ) + n) := by push_cast; ring
  have : (u : ℝ) = ((m : ℚ) / (m + n) : ℝ) := by rw [hres, hcast]
  exact_mod_cast this

/-- **Interior branch of beta-avoidance.**  A point u strictly inside (0,1) is mapped into
{0,1} by B_{m,n} only if u is the critical point m/(m+n).  Hence, for the canonical
three-point step, a β lying strictly between the two normalized endpoints (and not in S)
is automatically avoided: inside the range the step is beta-avoiding. -/
theorem belyi_eval_mem_zero_one_of_interior {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) {u : ℚ}
    (h0 : 0 < u) (h1 : u < 1) (h : (belyiPolynomial ℚ m n).eval u ∈ ({0, 1} : Set ℚ)) :
    u = (m : ℚ) / (m + n) := by
  have hm0 : m ≠ 0 := by omega
  have hn0 : n ≠ 0 := by omega
  rcases h with h | h
  · rw [TauCeti.eval_belyiPolynomial] at h
    rcases mul_eq_zero.mp h with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · exact absurd h'' (TauCeti.belyiConstant_ne_zero (K := ℚ) m n)
      · rw [pow_eq_zero_iff hm0] at h''
        linarith
    · rw [pow_eq_zero_iff hn0] at h'
      linarith
  · exact belyi_eval_one_imp m n hm hn h0 h1 h


/-- The beta-avoiding construction for all finite rational sets, conditional on the single
named step lemma BetaAvoidingStep. -/
theorem exists_betaAvoiding_of_step_apply (hstep : BetaAvoidingStep) (S : Finset ℚ) (β : ℚ)
    (hβ : β ∉ S) :
    ∃ q : ℚ[X], 0 < q.natDegree ∧ CritIn01 q ∧
      (∀ s ∈ S, q.eval s = 0 ∨ q.eval s = 1) ∧ q.eval β ≠ 0 ∧ q.eval β ≠ 1 :=
  exists_betaAvoiding_of_step hstep S β hβ

end LeanFormal.IUT.XiFPaper.Mzk1BetaAvoidingBelyiRationalActual
end