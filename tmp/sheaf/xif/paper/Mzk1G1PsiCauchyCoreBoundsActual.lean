/- B1 analytic h, batch 3 CORE (kurt): coefficient/derivative bounds for AlgPoint use.
Split from Mzk1G1PsiCauchyBound3Actual (which now re-exports) to decouple compilation.

Unconditional statements:
* norm of the k-th elementary symmetric sum of unit-disc complex numbers;
* coefficients of a monic split complex polynomial with unit-disc roots are bounded
  by Nat.choose natDegree k, hence by 2^natDegree;
* roots of the derivative are bounded by 1 + natDegree * 2^natDegree
  (Cauchy bound via Mathlib Polynomial.cauchyBound).

THIS FILE ONLY uses maxHeartbeats 1000000 (paper-level budget); RC list.
-/
import tmp.sheaf.xif.paper.Mzk1G1PsiCauchyBoundActual
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open scoped BigOperators NNReal NNReal

namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiCauchyBound3Actual

open Polynomial

/-- NNReal norm of a natural number in C. -/
theorem nnnorm_complex_natCast (n : ℕ) : ‖(n : ℂ)‖₊ = (n : ℝ≥0) := by
  apply NNReal.coe_injective
  rw [coe_nnnorm, Complex.norm_natCast]
  push_cast
  rfl

/-- Norm of the k-th elementary symmetric sum of unit-disc complex numbers. -/
theorem norm_esymm_le_choose (s : Multiset ℂ) (hs : ∀ z ∈ s, ‖z‖ ≤ 1) (k : ℕ) :
    ‖s.esymm k‖ ≤ (Nat.choose s.card k : ℝ) := by
  rw [Multiset.esymm]
  refine (norm_sum_le _ _).trans ?_
  have hterm : (s.powersetCard k).sum (fun t => ‖t.prod‖) ≤
      (s.powersetCard k).sum (fun _ => (1 : ℝ)) := by
    apply Finset.sum_le_sum
    intro t ht
    obtain ⟨hle, _⟩ := Multiset.mem_powersetCard.mp ht
    have h1 : ‖t.prod‖₊ ≤ 1 := by
      have hfac : ∀ z ∈ (t.map fun z => ‖z‖₊), z ≤ (1 : ℝ≥0) := by
        intro z hz
        obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hz
        exact_mod_cast hs x (Multiset.mem_of_le hle hx)
      refine (Multiset.prod_le_pow_card _ _ hfac).trans_eq ?_
      simp
    have h2 : (‖t.prod‖₊ : ℝ) ≤ (1 : ℝ) := NNReal.coe_le_coe.mpr h1
    simpa only [coe_nnnorm] using h2
  refine hterm.trans ?_
  rw [Finset.sum_const, Multiset.card_powersetCard]
  simp

/-- A binomial coefficient is at most 2 ^ d. -/
theorem choose_le_two_pow (d i : ℕ) : (Nat.choose d i : ℝ) ≤ 2 ^ d := by
  by_cases hi : i ≤ d
  · have hsum : (∑ j ∈ Finset.range (d + 1), (Nat.choose d j : ℝ)) = 2 ^ d := by
      rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]
    have hmem : i ∈ Finset.range (d + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hi)
    exact (Finset.single_le_sum (fun j _ => Nat.cast_nonneg j) hmem).trans_eq hsum
  · rw [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_le hi)]
    norm_num

/-- Monic split complex polynomial with unit-disc roots has coefficients bounded by
Nat.choose natDegree k. -/
theorem coeff_norm_le_choose (p : ℂ[X]) (hp : p.Monic)
    (hroots : ∀ z ∈ p.roots, ‖z‖ ≤ 1) (k : ℕ) :
    ‖p.coeff k‖ ≤ (Nat.choose p.natDegree k : ℝ) := by
  by_cases hk : k ≤ p.natDegree
  · rw [Polynomial.coeff_eq_esymm_roots_of_splits (IsAlgClosed.splits p) hk]
    rw [hp.leadingCoeff, norm_mul, norm_mul, norm_one, one_mul]
    have hsign : ‖(-1 : ℂ) ^ (p.natDegree - k)‖ = 1 := by
      rw [norm_pow, norm_neg, norm_one, one_pow]
    rw [hsign, one_mul]
    have hcard : Multiset.card p.roots = p.natDegree :=
      (IsAlgClosed.splits p).natDegree_eq_card_roots.symm
    have hes := norm_esymm_le_choose p.roots hroots (p.natDegree - k)
    rw [hcard] at hes
    refine hes.trans ?_
    rw [Nat.choose_symm hk]
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_of_not_le hk),
      Nat.choose_eq_zero_of_lt (Nat.lt_of_not_le hk)]
    norm_num

/-- Roots of the derivative of a monic unit-disc-root polynomial are bounded by
1 + natDegree * 2^natDegree. -/
theorem derivative_root_bound_choose (p : ℂ[X]) (hp : p.Monic)
    (hroots : ∀ z ∈ p.roots, ‖z‖ ≤ 1) {z : ℂ}
    (hz : p.derivative.IsRoot z) (hd : 1 ≤ p.natDegree) :
    ‖z‖ ≤ 1 + (p.natDegree : ℝ) * 2 ^ p.natDegree := by
  have hder : p.derivative ≠ 0 := by
    rw [Polynomial.derivative_ne_zero]
    omega
  have hlt : ‖z‖₊ < Polynomial.cauchyBound p.derivative :=
    Polynomial.IsRoot.norm_lt_cauchyBound hder hz
  have hB : ((p.natDegree : ℝ≥0) * 2 ^ p.natDegree) = ((p.natDegree : ℝ) * (2 : ℝ) ^ p.natDegree : ℝ≥0) := by
    push_cast
    rfl
  have hcoeff : ∀ i, ‖p.derivative.coeff i‖₊ ≤
      ((p.natDegree : ℝ≥0) * 2 ^ p.natDegree) := by
    intro i
    by_cases hi : i + 1 ≤ p.natDegree
    · have hstep : p.derivative.coeff i = (i + 1) * p.coeff (i + 1) := by
        rw [Polynomial.coeff_derivative]
        push_cast
        ring
      rw [hstep, nnnorm_mul]
      have h1 : ‖p.coeff (i + 1)‖₊ ≤ (2 : ℝ≥0) ^ p.natDegree := by
        have h2 : ‖p.coeff (i + 1)‖ ≤ 2 ^ p.natDegree :=
          (coeff_norm_le_choose p hp hroots (i + 1)).trans
            (choose_le_two_pow p.natDegree (i + 1))
        exact_mod_cast h2
      have h2 : ‖((i + 1 : ℕ) : ℂ)‖₊ ≤ (p.natDegree : ℝ≥0) := by
        rw [nnnorm_complex_natCast]
        exact_mod_cast Nat.le_of_succ_le hi
      exact mul_le_mul h2 h1 (by positivity) (by positivity)
    · have hzero : p.derivative.coeff i = 0 := by
        rw [Polynomial.coeff_derivative]
        have hgt : p.natDegree < i + 1 := Nat.lt_of_not_le hi
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt hgt]
        simp
      rw [hzero]
      simp
  have hsup : (Finset.range p.derivative.natDegree).sup
      (fun i => ‖p.derivative.coeff i‖₊) ≤ ((p.natDegree : ℝ≥0) * 2 ^ p.natDegree) :=
    Finset.sup_le (fun i _ => hcoeff i)
  have hlead : (1 : ℝ≥0) ≤ ‖p.derivative.leadingCoeff‖₊ := by
    rw [Polynomial.leadingCoeff_derivative, hp.leadingCoeff, one_mul,
      nnnorm_complex_natCast]
    exact_mod_cast hd
  have hcb : Polynomial.cauchyBound p.derivative ≤
      ((p.natDegree : ℝ≥0) * 2 ^ p.natDegree) + 1 := by
    unfold Polynomial.cauchyBound
    have hdiv : (Finset.range p.derivative.natDegree).sup
        (fun i => ‖p.derivative.coeff i‖₊) / ‖p.derivative.leadingCoeff‖₊ ≤
        (Finset.range p.derivative.natDegree).sup (fun i => ‖p.derivative.coeff i‖₊) := by
      calc (Finset.range p.derivative.natDegree).sup (fun i => ‖p.derivative.coeff i‖₊) /
            ‖p.derivative.leadingCoeff‖₊
          ≤ (Finset.range p.derivative.natDegree).sup (fun i => ‖p.derivative.coeff i‖₊) / 1 := by
              gcongr
        _ = (Finset.range p.derivative.natDegree).sup (fun i => ‖p.derivative.coeff i‖₊) := by
              simp
    exact add_le_add_right (hdiv.trans hsup) 1
  have hle : ‖z‖₊ ≤ ((p.natDegree : ℝ≥0) * 2 ^ p.natDegree) + 1 :=
    le_of_lt (lt_of_lt_of_le hlt hcb)
  have hcast : (((p.natDegree : ℝ≥0) * 2 ^ p.natDegree) + 1 : ℝ≥0) =
      (1 : ℝ) + (p.natDegree : ℝ) * (2 : ℝ) ^ p.natDegree := by
    push_cast
    ring
  have hle' : (‖z‖₊ : ℝ) ≤ ((((p.natDegree : ℝ≥0) * 2 ^ p.natDegree) + 1 : ℝ≥0) : ℝ) := by
    exact_mod_cast hle
  have hnorm : ‖z‖ = (‖z‖₊ : ℝ) := by
    simpa using (coe_nnnorm z).symm
  rw [hnorm]
  rwa [hcast] at hle'

#print axioms norm_esymm_le_choose
#print axioms choose_le_two_pow
#print axioms coeff_norm_le_choose
#print axioms derivative_root_bound_choose

end LeanFormal.IUT.XiFPaper.Mzk1G1PsiCauchyBound3Actual
end