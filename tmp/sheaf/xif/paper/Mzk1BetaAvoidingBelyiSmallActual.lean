import tmp.external.ported.tauceti_belyi_core.TauCeti.Algebra.Polynomial.Belyi
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-! # Mzk1BetaAvoidingBelyiSmallActual — beta-avoiding Belyi polynomial for small rational sets

STEP 0 prior-art: TauCeti `Belyi.lean` (`belyiPolynomial`, `eval_belyiPolynomial`,
`natDegree_belyiPolynomial`, `criticalValues_belyiPolynomial_subset`),
`CriticalValues.lean` (`criticalValues`, `mem_criticalValues`,
`criticalValues_comp_subset`), `Mzk1BelyiCvBridgeActual` (`belyiPolynomial_critIn01`,
C-point critical-value bridge), `Mzk1BetaAvoidingReductionActual` (the beta-avoidance
obstruction was isolated there as `B_{m,n}(A β) = 1`) -> REUSE/ADAPT.

Target (corrected Lemma 2.4 base case): for finite `S ⊆ ℚ` with `#S ≤ 3` and
`β ∉ S`, there is `q ∈ ℚ[X]` with `0 < natDegree q`, `q(S) ⊆ {0,1}`,
`q(β) ∉ {0,1}`, and every C-point critical point of `q` maps into `{0,1}`.
The last condition is stated via `aeval z (derivative q) = 0` for `z : ℂ`.

Proved in this file:
* the exact target as a named `Prop` (`BelyiBetaAvoidingSmallStatement`);
* the full `#S ≤ 2` case (`exists_belyi_betaAvoiding_card_le_two`);
* the full `#S = 3` case when `β` lies strictly between the least and greatest
  elements of `S` (`exists_belyi_betaAvoiding_card_three_of_mem_Ioo`).
Named blocker for `#S = 3` with `β` outside the convex hull: a target pattern
in `B_{m,n}^{-1}({0,1})` whose affine copy carries `S` and misses `β`; the canonical
affine normalisation is the only three-point pattern using the critical value and the
zero set, and it fails exactly when `β` hits an extra preimage of `1`; the
two-layer workaround is verified in `exists_belyi_betaAvoiding_example_exterior`.
The exact remaining statement is named `BelyiBetaAvoidingExteriorStatement` below. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1BetaAvoidingBelyiSmallActual

open Polynomial
open TauCeti

/-- **The exact target statement** (corrected Lemma 2.4 base case, `#S ≤ 3`): every
finite rational set with at most three points admits a nonconstant rational polynomial
sending it into `{0,1}`, avoiding a prescribed outside rational point, and with every
C-point critical value in `{0,1}`. -/
def BelyiBetaAvoidingSmallStatement : Prop :=
  ∀ (S : Finset ℚ) (β : ℚ), S.card ≤ 3 → β ∉ S →
    ∃ q : ℚ[X], 0 < q.natDegree ∧
      (∀ s ∈ S, q.eval s = 0 ∨ q.eval s = 1) ∧
      q.eval β ≠ 0 ∧ q.eval β ≠ 1 ∧
      (∀ z : ℂ, aeval z (derivative q) = 0 → (aeval z q = 0 ∨ aeval z q = 1))

/-! ## The two simple Belyi polynomials used below -/

/-- Value of `B_{1,1}`: `4 x (1 - x)`. -/
lemma eval_belyi11 (x : ℚ) : (belyiPolynomial ℚ 1 1).eval x = 4 * x * (1 - x) := by
  rw [eval_belyiPolynomial]
  norm_num

/-- Value of `B_{1,2}`: `(27/4) x (1 - x)^2`. -/
lemma eval_belyi12 (x : ℚ) : (belyiPolynomial ℚ 1 2).eval x = 27 / 4 * x * (1 - x) ^ 2 := by
  rw [eval_belyiPolynomial]
  norm_num

/-- `B_{1,1}(x) = 1` iff `x = 1/2`. -/
lemma belyi11_eq_one_iff (x : ℚ) : (belyiPolynomial ℚ 1 1).eval x = 1 ↔ x = 1 / 2 := by
  rw [eval_belyi11]
  constructor
  · intro h
    have hsq : (2 * x - 1) ^ 2 = 0 := by nlinarith
    have h1 : 2 * x - 1 = 0 := (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hsq
    linarith
  · rintro rfl
    norm_num

/-- `B_{1,2}(x) = 1` iff `x = 4/3` or `x = 1/3`. -/
lemma belyi12_eq_one_iff (x : ℚ) : (belyiPolynomial ℚ 1 2).eval x = 1 ↔ x = 4 / 3 ∨ x = 1 / 3 := by
  rw [eval_belyi12]
  have hfac : 27 * x * (1 - x) ^ 2 - 4 = 3 * (x - 4 / 3) * (3 * x - 1) ^ 2 := by ring
  constructor
  · intro h
    have h0 : 27 * x * (1 - x) ^ 2 - 4 = 0 := by nlinarith
    rw [hfac] at h0
    have h0' : (x - 4 / 3) * (3 * x - 1) ^ 2 = 0 := by nlinarith
    rcases mul_eq_zero.mp h0' with h1 | h1
    · left
      linarith
    · right
      have h2 : 3 * x - 1 = 0 := (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp h1
      linarith
  · rintro (rfl | rfl) <;> norm_num

/-- `B_{m,n}` (`m,n ≠ 0`) vanishes exactly at `0` and `1` over `ℚ`. -/
lemma eval_belyi_eq_zero_iff {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (x : ℚ) :
    (belyiPolynomial ℚ m n).eval x = 0 ↔ x = 0 ∨ x = 1 := by
  constructor
  · intro h
    rw [eval_belyiPolynomial] at h
    have hc : ((m : ℚ) + n) ^ (m + n) / ((m : ℚ) ^ m * (n : ℚ) ^ n) ≠ 0 :=
      belyiConstant_ne_zero m n
    rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hc
      · left
        exact (pow_eq_zero_iff hm).mp h'
    · right
      have h' : 1 - x = 0 := (pow_eq_zero_iff hn).mp h
      linarith
  · rintro (rfl | rfl)
    · exact eval_zero_belyiPolynomial hm n
    · exact eval_one_belyiPolynomial m hn

/-! ## The C-point critical-value bridge -/

/-- **C-point critical-value bridge for the canonical Belyi polynomial** (re-proved here
to keep this file's imports minimal): every critical point over `ℂ` of `B_{m,n}`
(`m,n ≥ 1`) maps into `{0,1}`. -/
theorem belyiPolynomial_critIn01 {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (z : ℂ)
    (hz : aeval z (derivative (belyiPolynomial ℚ m n)) = 0) :
    aeval z (belyiPolynomial ℚ m n) = 0 ∨ aeval z (belyiPolynomial ℚ m n) = 1 := by
  have hnd : (belyiPolynomial ℚ m n).natDegree = m + n := natDegree_belyiPolynomial m n
  have hder_ne : derivative (belyiPolynomial ℚ m n) ≠ 0 :=
    Polynomial.derivative_ne_zero.mpr (by rw [hnd]; omega)
  have hmem : aeval z (belyiPolynomial ℚ m n) ∈ (belyiPolynomial ℚ m n).criticalValues ℂ := by
    rw [mem_criticalValues]
    refine ⟨z, ?_, rfl⟩
    rw [mem_rootSet']
    refine ⟨?_, hz⟩
    exact (Polynomial.map_ne_zero_iff (algebraMap ℚ ℂ).injective).mpr hder_ne
  have hsub := criticalValues_belyiPolynomial_subset ℂ m n hmem
  simpa using hsub

/-- **C-point condition from a critical-value containment.** A nonconstant `q ∈ ℚ[X]`
whose critical values over `ℂ` lie in `{0,1}` has every C-point critical point mapping
into `{0,1}`. -/
lemma critIn01_of_criticalValues_subset {q : ℚ[X]} (hq : 0 < q.natDegree)
    (hCV : q.criticalValues ℂ ⊆ ({0, 1} : Set ℂ)) :
    ∀ z : ℂ, aeval z (derivative q) = 0 → (aeval z q = 0 ∨ aeval z q = 1) := by
  intro z hz
  have hder_ne : derivative q ≠ 0 := Polynomial.derivative_ne_zero.mpr hq.ne'
  have hmem : aeval z q ∈ q.criticalValues ℂ := by
    rw [mem_criticalValues]
    refine ⟨z, ?_, rfl⟩
    rw [mem_rootSet']
    exact ⟨(Polynomial.map_ne_zero_iff (algebraMap ℚ ℂ).injective).mpr hder_ne, hz⟩
  have := hCV hmem
  simpa using this

/-- **Critical-value containment for a composite** `p ∘ q`, when `p` maps `0` and
`1` into `{0,1}` and both factors have critical values in `{0,1}`. -/
lemma criticalValues_comp_subset_zero_one {p q : ℚ[X]}
    (hp : p.criticalValues ℂ ⊆ ({0, 1} : Set ℂ))
    (hq : q.criticalValues ℂ ⊆ ({0, 1} : Set ℂ))
    (hp0 : aeval (0 : ℂ) p ∈ ({0, 1} : Set ℂ))
    (hp1 : aeval (1 : ℂ) p ∈ ({0, 1} : Set ℂ)) :
    (p.comp q).criticalValues ℂ ⊆ ({0, 1} : Set ℂ) := by
  refine Set.Subset.trans (criticalValues_comp_subset p q) ?_
  rintro _ (h | h)
  · obtain ⟨y, hy, rfl⟩ := h
    rcases hq hy with rfl | rfl
    · simpa using hp0
    · simpa using hp1
  · exact hp h
/-! ## Normalising affine maps -/

/-- The affine normalisation `x ↦ (x - a)/(b - a)`. -/
def affineNorm (a b : ℚ) : ℚ[X] := C ((b - a)⁻¹) * (X - C a)

/-- `affineNorm a b` has degree one when `a ≠ b`. -/
lemma affineNorm_natDegree {a b : ℚ} (hab : a ≠ b) : (affineNorm a b).natDegree = 1 := by
  unfold affineNorm
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  rw [natDegree_C_mul (inv_ne_zero hba), natDegree_X_sub_C]

/-- Values of the normalising affine map. -/
lemma affineNorm_eval (a b x : ℚ) : (affineNorm a b).eval x = (x - a) / (b - a) := by
  unfold affineNorm
  simp [div_eq_mul_inv, mul_comm]

/-- **Critical values of `p ∘ affineNorm a b` are those of `p`**: the affine map has no
critical values, so the composite gains none. -/
lemma criticalValues_affine_comp_subset {p : ℚ[X]} {a b : ℚ} (hab : a ≠ b) :
    (p.comp (affineNorm a b)).criticalValues ℂ ⊆ p.criticalValues ℂ := by
  refine Set.Subset.trans (criticalValues_comp_subset p (affineNorm a b)) ?_
  have hempty : (affineNorm a b).criticalValues ℂ = ∅ :=
    criticalValues_eq_empty_of_natDegree_le_one (by rw [affineNorm_natDegree hab])
  simp [hempty]

/-- The composite with a nonconstant polynomial stays nonconstant. -/
lemma natDegree_comp_affine_pos {p : ℚ[X]} (hp : 0 < p.natDegree) {a b : ℚ} (hab : a ≠ b) :
    0 < (p.comp (affineNorm a b)).natDegree := by
  rw [natDegree_comp, affineNorm_natDegree hab]
  nlinarith

/-- Evaluation of the composite with the affine normalisation. -/
lemma eval_comp_affineNorm (p : ℚ[X]) (a b x : ℚ) :
    (p.comp (affineNorm a b)).eval x = p.eval ((x - a) / (b - a)) := by
  rw [eval_comp, affineNorm_eval]

/-! ## Strict Belyi bound on `(0,1)` (weighted AM-GM) -/

/-- **Strict normalized-maximum bound**: for `0 < x < 1` and `x ≠ m/(m+n)`, the Belyi
polynomial `B_{m,n}` (`m,n > 0`) satisfies `B_{m,n}(x) < 1`.  Weighted AM-GM applied to
the two positive numbers `(m+n)x/m` and `(m+n)(1-x)/n`. -/
lemma eval_belyi_lt_one {m n : ℕ} (hm : 0 < m) (hn : 0 < n) {x : ℚ}
    (hx0 : 0 < x) (hx1 : x < 1) (hne : x ≠ (m : ℚ) / ((m : ℚ) + n)) :
    (belyiPolynomial ℚ m n).eval x < 1 := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  set M : ℝ := (m : ℝ) with hM
  set N : ℝ := (n : ℝ) with hN
  set X : ℝ := (x : ℝ) with hX
  have hMpos : 0 < M := hM ▸ hmR
  have hNpos : 0 < N := hN ▸ hnR
  have hX0 : 0 < X := hX ▸ (by exact_mod_cast hx0)
  have hX1 : X < 1 := hX ▸ (by exact_mod_cast hx1)
  have hMN : 0 < M + N := by positivity
  set p1 : ℝ := (M + N) * X / M with hp1
  set p2 : ℝ := (M + N) * (1 - X) / N with hp2
  have hp1pos : 0 < p1 := by rw [hp1]; positivity
  have hp2pos : 0 < p2 := by rw [hp2]; positivity
  have hw1 : 0 < M / (M + N) := by positivity
  have hw2 : 0 < N / (M + N) := by positivity
  have hwsum : M / (M + N) + N / (M + N) = 1 := by
    field_simp
  have hpne : p1 ≠ p2 := by
    intro h
    rw [hp1, hp2] at h
    have h1 : N * X = M * (1 - X) := by
      field_simp at h
      linarith
    have h2 : X * (M + N) = M := by linarith
    have h3 : X = M / (M + N) := by
      rw [eq_div_iff hMN.ne']
      linarith
    apply hne
    have h4 : (x : ℝ) = (m : ℝ) / ((m : ℝ) + n) := by
      rw [← hX, ← hM, ← hN]
      exact h3
    have h5 : ((x : ℚ) : ℝ) = (((m : ℚ) / ((m : ℚ) + n) : ℚ) : ℝ) := by
      push_cast
      exact h4
    exact (Rat.cast_inj).mp h5
  have ham := (Real.geom_mean_lt_arith_mean2_weighted_iff_of_pos hw1 hw2 hp1pos.le hp2pos.le
    hwsum).mpr hpne
  have harith : M / (M + N) * p1 + N / (M + N) * p2 = 1 := by
    rw [hp1, hp2]
    field_simp
    ring
  rw [harith] at ham
  have he : 0 < (M + N)⁻¹ := by positivity
  have hlt' : (p1 ^ m * p2 ^ n) ^ (M + N)⁻¹ < 1 := by
    rw [Real.mul_rpow (pow_nonneg hp1pos.le m) (pow_nonneg hp2pos.le n)]
    have h1 : (p1 ^ m) ^ ((M + N)⁻¹) = p1 ^ (M / (M + N)) := by
      have hexp : M / (M + N) = (m : ℝ) * (M + N)⁻¹ := by
        rw [hM, div_eq_mul_inv]
      rw [hexp]
      exact (Real.rpow_natCast_mul hp1pos.le m ((M + N)⁻¹)).symm
    have h2 : (p2 ^ n) ^ ((M + N)⁻¹) = p2 ^ (N / (M + N)) := by
      have hexp : N / (M + N) = (n : ℝ) * (M + N)⁻¹ := by
        rw [hN, div_eq_mul_inv]
      rw [hexp]
      exact (Real.rpow_natCast_mul hp2pos.le n ((M + N)⁻¹)).symm
    rw [h1, h2]
    exact ham
  have hmain : p1 ^ m * p2 ^ n < 1 := by
    have h := (Real.rpow_lt_rpow_iff (show (0 : ℝ) ≤ p1 ^ m * p2 ^ n by positivity)
      (by norm_num : (0 : ℝ) ≤ 1) he).mp (by simpa [Real.one_rpow] using hlt')
    exact h
  have hBcast : (((belyiPolynomial ℚ m n).eval x : ℚ) : ℝ) = p1 ^ m * p2 ^ n := by
    have hq : (belyiPolynomial ℚ m n).eval x =
        ((m : ℚ) + n) ^ (m + n) / ((m : ℚ) ^ m * (n : ℚ) ^ n) * x ^ m * (1 - x) ^ n :=
      eval_belyiPolynomial m n x
    rw [hq]
    push_cast
    rw [← hX, ← hM, ← hN, hp1, hp2, div_pow, div_pow, mul_pow, mul_pow]
    field_simp
    ring
  have hreal : (((belyiPolynomial ℚ m n).eval x : ℚ) : ℝ) < 1 := by
    rw [hBcast]
    exact hmain
  exact_mod_cast hreal

/-- **Positivity of `B_{m,n}` on `(0,1)`.** -/
lemma eval_belyi_pos {m n : ℕ} (hm : 0 < m) (hn : 0 < n) {x : ℚ}
    (hx0 : 0 < x) (hx1 : x < 1) :
    0 < (belyiPolynomial ℚ m n).eval x := by
  rw [eval_belyiPolynomial]
  have hc : 0 < ((m : ℚ) + n) ^ (m + n) / ((m : ℚ) ^ m * (n : ℚ) ^ n) := by
    apply div_pos
    · positivity
    · positivity
  exact mul_pos (mul_pos hc (pow_pos hx0 m)) (pow_pos (by linarith : 0 < 1 - x) n)

/-- **`B_{m,n}` does not take the value `1` strictly inside `(0,1)` away from its critical
point.** -/
lemma eval_belyi_ne_one_of_pos_of_lt_one {m n : ℕ} (hm : 0 < m) (hn : 0 < n) {x : ℚ}
    (hx0 : 0 < x) (hx1 : x < 1) (hne : x ≠ (m : ℚ) / ((m : ℚ) + n)) :
    (belyiPolynomial ℚ m n).eval x ≠ 1 := by
  have h := eval_belyi_lt_one hm hn hx0 hx1 hne
  linarith

/-- **`B_{m,n}` does not vanish strictly inside `(0,1)`.** -/
lemma eval_belyi_ne_zero_of_pos_of_lt_one {m n : ℕ} (hm : 0 < m) (hn : 0 < n) {x : ℚ}
    (hx0 : 0 < x) (hx1 : x < 1) :
    (belyiPolynomial ℚ m n).eval x ≠ 0 := by
  have h := eval_belyi_pos hm hn hx0 hx1
  linarith
/-! ## Packaged affine-Belyi constructions -/

/-- Composing `B_{m,n}` (`m,n > 0`) with the affine normalisation keeps the degree positive. -/
lemma affineBelyi_natDegree_pos {m n : ℕ} (hm : 0 < m) (hn : 0 < n) {a b : ℚ} (hab : a ≠ b) :
    0 < ((belyiPolynomial ℚ m n).comp (affineNorm a b)).natDegree :=
  natDegree_comp_affine_pos (p := belyiPolynomial ℚ m n)
    (by rw [natDegree_belyiPolynomial]; omega) hab

/-- Values of `B_{m,n} ∘ affineNorm a b`. -/
lemma eval_affineBelyi (m n : ℕ) (a b x : ℚ) :
    ((belyiPolynomial ℚ m n).comp (affineNorm a b)).eval x =
      (belyiPolynomial ℚ m n).eval ((x - a) / (b - a)) :=
  eval_comp_affineNorm _ a b x

/-- C-point condition for `B_{m,n} ∘ affineNorm a b` (`m,n ≥ 1`). -/
lemma affineBelyi_critIn01 {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) {a b : ℚ} (hab : a ≠ b) :
    ∀ z : ℂ, aeval z (derivative ((belyiPolynomial ℚ m n).comp (affineNorm a b))) = 0 →
      (aeval z ((belyiPolynomial ℚ m n).comp (affineNorm a b)) = 0 ∨
       aeval z ((belyiPolynomial ℚ m n).comp (affineNorm a b)) = 1) := by
  apply critIn01_of_criticalValues_subset
  · rw [natDegree_comp, natDegree_belyiPolynomial, affineNorm_natDegree hab]
    nlinarith
  · exact Set.Subset.trans (criticalValues_affine_comp_subset hab)
      (criticalValues_belyiPolynomial_subset ℂ m n)

/-! ## The full `#S ≤ 2` case -/

/-- **Main result, `#S ≤ 2`.** For every finite rational set `S` with at most two points
and every `β ∉ S` there is a nonconstant `q ∈ ℚ[X]` with `q(S) ⊆ {0,1}`,
`q(β) ∉ {0,1}`, and every C-point critical value of `q` in `{0,1}`.

The construction uses `B_{1,1} ∘ affineNormalisation` (and `B_{1,2}` when the image of
`β` is the critical point `1/2`). -/
theorem exists_belyi_betaAvoiding_card_le_two (S : Finset ℚ) (β : ℚ)
    (hS : S.card ≤ 2) (hβ : β ∉ S) :
    ∃ q : ℚ[X], 0 < q.natDegree ∧
      (∀ s ∈ S, q.eval s = 0 ∨ q.eval s = 1) ∧
      q.eval β ≠ 0 ∧ q.eval β ≠ 1 ∧
      (∀ z : ℂ, aeval z (derivative q) = 0 → (aeval z q = 0 ∨ aeval z q = 1)) := by
  classical
  rcases Nat.lt_or_ge S.card 1 with hcard0 | hcard1
  · -- `S = ∅`
    have hSempty : S = ∅ := Finset.card_eq_zero.mp (by omega)
    refine ⟨(belyiPolynomial ℚ 1 2).comp (affineNorm (β - 2) (β - 1)), ?_, ?_, ?_, ?_, ?_⟩
    · exact affineBelyi_natDegree_pos (by norm_num) (by norm_num) (by linarith)
    · intro s hs
      rw [hSempty] at hs
      simp at hs
    · have hval : ((belyiPolynomial ℚ 1 2).comp (affineNorm (β - 2) (β - 1))).eval β = 27 / 2 := by
        rw [eval_affineBelyi]
        have harg : (β - (β - 2)) / ((β - 1) - (β - 2)) = 2 := by
          rw [show β - (β - 2) = 2 by ring, show (β - 1) - (β - 2) = 1 by ring]
          norm_num
        rw [harg, eval_belyi12]
        norm_num
      rw [hval]
      norm_num
    · have hval : ((belyiPolynomial ℚ 1 2).comp (affineNorm (β - 2) (β - 1))).eval β = 27 / 2 := by
        rw [eval_affineBelyi]
        have harg : (β - (β - 2)) / ((β - 1) - (β - 2)) = 2 := by
          rw [show β - (β - 2) = 2 by ring, show (β - 1) - (β - 2) = 1 by ring]
          norm_num
        rw [harg, eval_belyi12]
        norm_num
      rw [hval]
      norm_num
    · exact affineBelyi_critIn01 (by norm_num) (by norm_num) (by linarith)
  · rcases Nat.lt_or_ge S.card 2 with hcard2 | hcard2
    · -- `S = {s}`
      obtain ⟨s, hSsing⟩ := Finset.card_eq_one.mp (by omega : S.card = 1)
      have hβs : β - s ≠ 0 := by
        intro h
        have hβmem : β ∈ S := by
          rw [hSsing, Finset.mem_singleton]
          linarith
        exact hβ hβmem
      have hbs : s ≠ s + 4 * (β - s) := by
        intro h
        have h4 : 4 * (β - s) = 0 := by linarith
        exact hβs (by linarith)
      refine ⟨(belyiPolynomial ℚ 1 1).comp (affineNorm s (s + 4 * (β - s))), ?_, ?_, ?_, ?_, ?_⟩
      · exact affineBelyi_natDegree_pos (by norm_num) (by norm_num) hbs
      · intro x hx
        rw [hSsing, Finset.mem_singleton] at hx
        rw [hx]
        left
        rw [eval_affineBelyi]
        have harg : (s - s) / ((s + 4 * (β - s)) - s) = 0 := by
          rw [sub_self, zero_div]
        rw [harg, eval_belyi11]
        ring
      · have hval : ((belyiPolynomial ℚ 1 1).comp (affineNorm s (s + 4 * (β - s)))).eval β = 3 / 4 := by
          rw [eval_affineBelyi]
          have harg : (β - s) / ((s + 4 * (β - s)) - s) = 1 / 4 := by
            rw [show (s + 4 * (β - s)) - s = 4 * (β - s) by ring]
            rw [div_eq_iff (by exact mul_ne_zero (by norm_num) hβs)]
            ring
          rw [harg, eval_belyi11]
          norm_num
        rw [hval]
        norm_num
      · have hval : ((belyiPolynomial ℚ 1 1).comp (affineNorm s (s + 4 * (β - s)))).eval β = 3 / 4 := by
          rw [eval_affineBelyi]
          have harg : (β - s) / ((s + 4 * (β - s)) - s) = 1 / 4 := by
            rw [show (s + 4 * (β - s)) - s = 4 * (β - s) by ring]
            rw [div_eq_iff (by exact mul_ne_zero (by norm_num) hβs)]
            ring
          rw [harg, eval_belyi11]
          norm_num
        rw [hval]
        norm_num
      · exact affineBelyi_critIn01 (by norm_num) (by norm_num) hbs
    · -- `S = {a, b}`
      obtain ⟨a, b, hab, hSpair⟩ := Finset.card_eq_two.mp (by omega : S.card = 2)
      have haβ : β ≠ a := by
        intro h
        apply hβ
        rw [hSpair, h]
        exact Finset.mem_insert_self a {b}
      have hbβ : β ≠ b := by
        intro h
        apply hβ
        rw [hSpair, h]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
      have hden : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
      have ht0 : (β - a) / (b - a) ≠ 0 := by
        intro h
        have h' := congrArg (fun y => y * (b - a)) h
        field_simp at h'
        exact haβ (by linarith)
      have ht1 : (β - a) / (b - a) ≠ 1 := by
        intro h
        have h' := congrArg (fun y => y * (b - a)) h
        field_simp at h'
        exact hbβ (by linarith)
      by_cases ht : (β - a) / (b - a) = 1 / 2
      · refine ⟨(belyiPolynomial ℚ 1 2).comp (affineNorm a b), ?_, ?_, ?_, ?_, ?_⟩
        · exact affineBelyi_natDegree_pos (by norm_num) (by norm_num) hab
        · intro x hx
          rw [hSpair] at hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with hx | hx
          · rw [hx]
            left
            rw [eval_affineBelyi]
            have harg : (a - a) / (b - a) = 0 := by rw [sub_self, zero_div]
            rw [harg, eval_belyi12]
            norm_num
          · rw [hx]
            left
            rw [eval_affineBelyi, div_self hden, eval_belyi12]
            norm_num
        · have hval : ((belyiPolynomial ℚ 1 2).comp (affineNorm a b)).eval β = 27 / 32 := by
            rw [eval_affineBelyi, ht, eval_belyi12]
            norm_num
          rw [hval]
          norm_num
        · have hval : ((belyiPolynomial ℚ 1 2).comp (affineNorm a b)).eval β = 27 / 32 := by
            rw [eval_affineBelyi, ht, eval_belyi12]
            norm_num
          rw [hval]
          norm_num
        · exact affineBelyi_critIn01 (by norm_num) (by norm_num) hab
      · refine ⟨(belyiPolynomial ℚ 1 1).comp (affineNorm a b), ?_, ?_, ?_, ?_, ?_⟩
        · exact affineBelyi_natDegree_pos (by norm_num) (by norm_num) hab
        · intro x hx
          rw [hSpair] at hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with hx | hx
          · rw [hx]
            left
            rw [eval_affineBelyi]
            have harg : (a - a) / (b - a) = 0 := by rw [sub_self, zero_div]
            rw [harg, eval_belyi11]
            ring
          · rw [hx]
            left
            rw [eval_affineBelyi, div_self hden, eval_belyi11]
            ring
        · intro hz
          rw [eval_affineBelyi] at hz
          rcases (eval_belyi_eq_zero_iff (by norm_num : (1 : ℕ) ≠ 0)
            (by norm_num : (1 : ℕ) ≠ 0) ((β - a) / (b - a))).mp hz with h | h
          · exact ht0 h
          · exact ht1 h
        · intro ho
          rw [eval_affineBelyi] at ho
          exact ht (belyi11_eq_one_iff ((β - a) / (b - a)) |>.mp ho)
        · exact affineBelyi_critIn01 (by norm_num) (by norm_num) hab
/-! ## The interior three-point case -/

/-- **Interior three-point case (proved).** For `a < b < c` and `a < β < c` with
`β ≠ b`, the target holds for `S = {a, b, c}`.

Construction: `q = B_{m,n} ∘ affineNormalisation` where `m/(m+n) = (b-a)/(c-a)`.
Then `q(a) = q(c) = 0`, `q(b) = 1`, and `q(β) = B_{m,n}(u)` with
`u = (β-a)/(c-a) ∈ (0,1)`, `u ≠ m/(m+n)`; the strict weighted-AM-GM bound
`eval_belyi_lt_one` gives `0 < B_{m,n}(u) < 1`, so `β` is avoided. -/
theorem exists_belyi_betaAvoiding_three_of_lt {a b c β : ℚ}
    (hab : a < b) (hbc : b < c) (hβa : a < β) (hβc : β < c) (hβb : β ≠ b) :
    ∃ q : ℚ[X], 0 < q.natDegree ∧
      (∀ s ∈ ({a, b, c} : Finset ℚ), q.eval s = 0 ∨ q.eval s = 1) ∧
      q.eval β ≠ 0 ∧ q.eval β ≠ 1 ∧
      (∀ z : ℂ, aeval z (derivative q) = 0 → (aeval z q = 0 ∨ aeval z q = 1)) := by
  classical
  have hca : 0 < c - a := by linarith
  have hca_ne : c - a ≠ 0 := hca.ne'
  have ht0 : 0 < (b - a) / (c - a) := div_pos (by linarith) hca
  have ht1 : (b - a) / (c - a) < 1 := by
    rw [div_lt_one hca]
    linarith
  obtain ⟨m, n, hm, hn, ht_eq⟩ := Rat.exists_eq_div_add_of_pos_of_lt_one ht0 ht1
  have hu0 : 0 < (β - a) / (c - a) := div_pos (by linarith) hca
  have hu1 : (β - a) / (c - a) < 1 := by
    rw [div_lt_one hca]
    linarith
  have hune : (β - a) / (c - a) ≠ (m : ℚ) / ((m : ℚ) + n) := by
    rw [← ht_eq]
    intro h
    have h' := congrArg (fun y => y * (c - a)) h
    field_simp at h'
    exact hβb (by linarith)
  refine ⟨(belyiPolynomial ℚ m n).comp (affineNorm a c), ?_, ?_, ?_, ?_, ?_⟩
  · exact affineBelyi_natDegree_pos (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn)
      (hab.trans hbc).ne
  · intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with h | h | h
    · left
      rw [h, eval_affineBelyi]
      have harg : (a - a) / (c - a) = 0 := by rw [sub_self, zero_div]
      rw [harg, eval_zero_belyiPolynomial hm n]
    · right
      rw [h, eval_affineBelyi]
      rw [show (b - a) / (c - a) = (m : ℚ) / ((m : ℚ) + n) from ht_eq]
      exact eval_div_belyiPolynomial (K := ℚ) m n
    · left
      rw [h, eval_affineBelyi, div_self hca_ne, eval_one_belyiPolynomial m hn]
  · intro hz
    rw [eval_affineBelyi] at hz
    exact eval_belyi_ne_zero_of_pos_of_lt_one (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn)
      hu0 hu1 hz
  · intro ho
    rw [eval_affineBelyi] at ho
    exact eval_belyi_ne_one_of_pos_of_lt_one (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn)
      hu0 hu1 hune ho
  · exact affineBelyi_critIn01 (by omega) (by omega) (hab.trans hbc).ne

/-! ## Extra preimages of '1' and the exterior obstruction -/

/-- Value of 'B_{2,1}': '(27/4) x^2 (1 - x)'. -/
lemma eval_belyi21 (x : ℚ) : (belyiPolynomial ℚ 2 1).eval x = 27 / 4 * x ^ 2 * (1 - x) := by
  rw [eval_belyiPolynomial]
  norm_num

/-- The canonical construction has a genuine bad exterior point: for
'S = {0, 1/3, 1}' the affine normalisation is the identity, the critical value of
'B_{1,2}' is '1/3', and 'β = 4/3' is an extra preimage of '1':
'B_{1,2}(4/3) = 1', so the one-layer construction fails. -/
theorem canonical_exterior_bad_point : (belyiPolynomial ℚ 1 2).eval (4 / 3) = 1 := by
  rw [eval_belyi12]
  norm_num

/-- **The exterior obstruction is not absolute.** For 'S = {0, 1/3, 1}' and
'β = 4/3 > max S' the target holds: the two-layer polynomial
'B_{1,1} ∘ B_{2,1}' sends 'S' into '{0,1}', sends '4/3' to '-80', and has all
critical values in '{0,1}' because 'B_{1,1}(0) = B_{1,1}(1) = 0' and both factors are
Belyi polynomials. -/
theorem exists_belyi_betaAvoiding_example_exterior :
    ∃ q : ℚ[X], 0 < q.natDegree ∧
      (∀ s ∈ ({0, 1 / 3, 1} : Finset ℚ), q.eval s = 0 ∨ q.eval s = 1) ∧
      q.eval (4 / 3) ≠ 0 ∧ q.eval (4 / 3) ≠ 1 ∧
      (∀ z : ℂ, aeval z (derivative q) = 0 → (aeval z q = 0 ∨ aeval z q = 1)) := by
  refine ⟨(belyiPolynomial ℚ 1 1).comp (belyiPolynomial ℚ 2 1), ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_comp, natDegree_belyiPolynomial, natDegree_belyiPolynomial]
    norm_num
  · intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with h | h | h
    · rw [h, eval_comp, eval_zero_belyiPolynomial (by norm_num : (2 : ℕ) ≠ 0)]
      exact Or.inl (eval_zero_belyiPolynomial (by norm_num : (1 : ℕ) ≠ 0) 1)
    · rw [h, eval_comp]
      refine Or.inr ?_
      rw [show (belyiPolynomial ℚ 2 1).eval (1 / 3) = 1 / 2 from by
        rw [eval_belyi21]; norm_num, eval_belyi11]
      norm_num
    · rw [h, eval_comp, eval_one_belyiPolynomial (2 : ℕ) (by norm_num : (1 : ℕ) ≠ 0)]
      exact Or.inl (eval_zero_belyiPolynomial (by norm_num : (1 : ℕ) ≠ 0) 1)
  · rw [eval_comp]
    rw [show (belyiPolynomial ℚ 2 1).eval (4 / 3) = -4 from by rw [eval_belyi21]; norm_num,
      eval_belyi11]
    norm_num
  · rw [eval_comp]
    rw [show (belyiPolynomial ℚ 2 1).eval (4 / 3) = -4 from by rw [eval_belyi21]; norm_num,
      eval_belyi11]
    norm_num
  · refine critIn01_of_criticalValues_subset ?_ ?_
    · rw [natDegree_comp, natDegree_belyiPolynomial, natDegree_belyiPolynomial]
      norm_num
    · refine criticalValues_comp_subset_zero_one
        (criticalValues_belyiPolynomial_subset ℂ 1 1)
        (criticalValues_belyiPolynomial_subset ℂ 2 1) ?_ ?_
      · refine Or.inl ?_
        rw [aeval_def, eval₂_eq_eval_map, map_belyiPolynomial]
        exact eval_zero_belyiPolynomial (K := ℂ) (by norm_num : (1 : ℕ) ≠ 0) 1
      · refine Or.inl ?_
        rw [aeval_def, eval₂_eq_eval_map, map_belyiPolynomial]
        exact eval_one_belyiPolynomial (1 : ℕ) (by norm_num : (1 : ℕ) ≠ 0)

/-! ## Exact remaining statement (named blocker) -/

/-- **Exact remaining three-point exterior statement.** For `a < b < c < β` the target
must hold for `S = {a,b,c}`.  This is the only case not proved in this file: in the
interior case (`a < β < c`) the canonical construction works because `β` maps into
`(0,1)` where `B_{m,n}` takes values strictly between `0` and `1` away from its
critical point; for `β > c` the image of `β` is `> 1`, where extra preimages of `1`
exist (`canonical_exterior_bad_point`), and a different target pattern in
`B^{-1}({0,1})` (or a multi-layer composite) is required.  The parity-solvable parts
are proved in `exists_belyi_three_of_gt_of_odd` and `exists_belyi_three_of_lt_of_odd`:
then `B_{m,n}` has the safe negative sign at the image of `β`.  The residue is the
parity-stuck part of this statement. -/

def BelyiBetaAvoidingExteriorStatement : Prop :=
  ∀ (a b c β : ℚ), a < b → b < c → c < β →
    ∃ q : ℚ[X], 0 < q.natDegree ∧
      (∀ s ∈ ({a, b, c} : Finset ℚ), q.eval s = 0 ∨ q.eval s = 1) ∧
      q.eval β ≠ 0 ∧ q.eval β ≠ 1 ∧
      (∀ z : ℂ, aeval z (derivative q) = 0 → (aeval z q = 0 ∨ aeval z q = 1))

/-- Row record: what is proved and what remains. -/
def betaAvoidingSmallRows : List (String × String × String) :=
  [ ("#S ≤ 2 case", "A", "PROVED exists_belyi_betaAvoiding_card_le_two")
  , ("#S = 3, β strictly between min and max", "A", "PROVED exists_belyi_betaAvoiding_three_of_lt")
  , ("#S = 3, β > max, reduced denominator-numerator odd", "A", "PROVED exists_belyi_three_of_gt_of_odd (positive-slope construction, sign of B at u > 1)")
  , ("#S = 3, β < min, reduced numerator odd", "A", "PROVED exists_belyi_three_of_lt_of_odd (positive-slope construction, sign of B at u < 0)")
  , ("#S = 3, remaining exterior parity residue", "BLOCKER", "NAMED BelyiBetaAvoidingExteriorStatement; canonical one-layer construction fails exactly at extra preimages of 1 (canonical_exterior_bad_point); two-layer workaround verified on S={0,1/3,1}, β=4/3")
  , ("strict normalized-maximum bound (weighted AM-GM)", "A", "PROVED eval_belyi_lt_one") ]

/-- The row record has six rows. -/
theorem betaAvoidingSmallRows_length : betaAvoidingSmallRows.length = 6 := rfl

#check exists_belyi_betaAvoiding_card_le_two
#check exists_belyi_betaAvoiding_three_of_lt
#check eval_belyi_lt_one
#check canonical_exterior_bad_point
#check exists_belyi_betaAvoiding_example_exterior
#check BelyiBetaAvoidingExteriorStatement
#check BelyiBetaAvoidingSmallStatement
#check betaAvoidingSmallRows_length

/-! ## Sign of Belyi values outside the unit interval -/

/-- **Sign at the right of 1:** for 'x > 1' and odd 'n', 'B_{m,n}(x) < 0'. -/
lemma eval_belyi_neg_of_one_lt {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hnodd : Odd n) {x : ℚ}
    (hx : 1 < x) : (belyiPolynomial ℚ m n).eval x < 0 := by
  rw [eval_belyiPolynomial]
  have hmq : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm
  have hnq : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
  have hc : 0 < ((m : ℚ) + n) ^ (m + n) / ((m : ℚ) ^ m * (n : ℚ) ^ n) :=
    div_pos (pow_pos (by positivity) _) (mul_pos (pow_pos hmq m) (pow_pos hnq n))
  have hxpow : 0 < x ^ m := pow_pos (by linarith) m
  have h1x : (1 - x) ^ n < 0 := by
    have h : (1 - x) = -(x - 1) := by ring
    rw [h, hnodd.neg_pow]
    have : 0 < (x - 1) ^ n := pow_pos (by linarith) n
    linarith
  exact mul_neg_of_pos_of_neg (mul_pos hc hxpow) h1x

/-- **Sign at the left of 0:** for 'x < 0' and odd 'm', 'B_{m,n}(x) < 0'. -/
lemma eval_belyi_neg_of_lt_zero {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmodd : Odd m) {x : ℚ}
    (hx : x < 0) : (belyiPolynomial ℚ m n).eval x < 0 := by
  rw [eval_belyiPolynomial]
  have hmq : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm
  have hnq : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
  have hc : 0 < ((m : ℚ) + n) ^ (m + n) / ((m : ℚ) ^ m * (n : ℚ) ^ n) :=
    div_pos (pow_pos (by positivity) _) (mul_pos (pow_pos hmq m) (pow_pos hnq n))
  have hxpow : x ^ m < 0 := by
    have h : x = -(-x) := by ring
    rw [h, hmodd.neg_pow]
    have : 0 < (-x) ^ m := pow_pos (by linarith) m
    linarith
  have h1x : 0 < (1 - x) ^ n := pow_pos (by linarith) n
  exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hc hxpow) h1x

/-- **Exterior case, parity-solvable form ('β > c').** If 'a < b < c < β' and
'(b-a)/(c-a) = m/(m+n)' with 'n' odd, the positive-slope construction
'q = B_{m,n} ∘ affineNorm a c' solves the target: 'β' maps to 'u > 1' and
'B_{m,n}(u) < 0' by the sign lemma, so 'q(β) ∉ {0,1}' automatically. -/
theorem exists_belyi_three_of_gt_of_odd {a b c β : ℚ}
    (hab : a < b) (hbc : b < c) (hcβ : c < β)
    {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (ht : (b - a) / (c - a) = (m : ℚ) / ((m : ℚ) + n)) (hnodd : Odd n) :
    ∃ q : ℚ[X], 0 < q.natDegree ∧
      (∀ s ∈ ({a, b, c} : Finset ℚ), q.eval s = 0 ∨ q.eval s = 1) ∧
      q.eval β ≠ 0 ∧ q.eval β ≠ 1 ∧
      (∀ z : ℂ, aeval z (derivative q) = 0 → (aeval z q = 0 ∨ aeval z q = 1)) := by
  classical
  have hca : 0 < c - a := by linarith
  have hca_ne : c - a ≠ 0 := hca.ne'
  have hu : 1 < (β - a) / (c - a) := by
    rw [one_lt_div hca]
    linarith
  have hmm : 0 < m := Nat.pos_of_ne_zero hm
  have hnn : 0 < n := Nat.pos_of_ne_zero hn
  refine ⟨(belyiPolynomial ℚ m n).comp (affineNorm a c), ?_, ?_, ?_, ?_, ?_⟩
  · exact affineBelyi_natDegree_pos hmm hnn (hab.trans hbc).ne
  · intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with h | h | h
    · left
      rw [h, eval_affineBelyi]
      have harg : (a - a) / (c - a) = 0 := by rw [sub_self, zero_div]
      rw [harg, eval_zero_belyiPolynomial hm n]
    · right
      rw [h, eval_affineBelyi]
      rw [show (b - a) / (c - a) = (m : ℚ) / ((m : ℚ) + n) from ht]
      exact eval_div_belyiPolynomial (K := ℚ) m n
    · left
      rw [h, eval_affineBelyi, div_self hca_ne, eval_one_belyiPolynomial m hn]
  · intro hz
    rw [eval_affineBelyi] at hz
    have hneg := eval_belyi_neg_of_one_lt hmm hnn hnodd hu
    linarith
  · intro ho
    rw [eval_affineBelyi] at ho
    have hneg := eval_belyi_neg_of_one_lt hmm hnn hnodd hu
    linarith
  · exact affineBelyi_critIn01 (by omega) (by omega) (hab.trans hbc).ne

/-- **Exterior case, parity-solvable form ('β < a').** If 'β < a < b < c' and
'(b-a)/(c-a) = m/(m+n)' with 'm' odd, the positive-slope construction solves the target:
'β' maps to 'u < 0' and 'B_{m,n}(u) < 0' by the sign lemma. -/
theorem exists_belyi_three_of_lt_of_odd {a b c β : ℚ}
    (hab : a < b) (hbc : b < c) (hβa : β < a)
    {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (ht : (b - a) / (c - a) = (m : ℚ) / ((m : ℚ) + n)) (hmodd : Odd m) :
    ∃ q : ℚ[X], 0 < q.natDegree ∧
      (∀ s ∈ ({a, b, c} : Finset ℚ), q.eval s = 0 ∨ q.eval s = 1) ∧
      q.eval β ≠ 0 ∧ q.eval β ≠ 1 ∧
      (∀ z : ℂ, aeval z (derivative q) = 0 → (aeval z q = 0 ∨ aeval z q = 1)) := by
  classical
  have hca : 0 < c - a := by linarith
  have hca_ne : c - a ≠ 0 := hca.ne'
  have hu : (β - a) / (c - a) < 0 :=
    div_neg_of_neg_of_pos (by linarith) hca
  have hmm : 0 < m := Nat.pos_of_ne_zero hm
  have hnn : 0 < n := Nat.pos_of_ne_zero hn
  refine ⟨(belyiPolynomial ℚ m n).comp (affineNorm a c), ?_, ?_, ?_, ?_, ?_⟩
  · exact affineBelyi_natDegree_pos hmm hnn (hab.trans hbc).ne
  · intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with h | h | h
    · left
      rw [h, eval_affineBelyi]
      have harg : (a - a) / (c - a) = 0 := by rw [sub_self, zero_div]
      rw [harg, eval_zero_belyiPolynomial hm n]
    · right
      rw [h, eval_affineBelyi]
      rw [show (b - a) / (c - a) = (m : ℚ) / ((m : ℚ) + n) from ht]
      exact eval_div_belyiPolynomial (K := ℚ) m n
    · left
      rw [h, eval_affineBelyi, div_self hca_ne, eval_one_belyiPolynomial m hn]
  · intro hz
    rw [eval_affineBelyi] at hz
    have hneg := eval_belyi_neg_of_lt_zero hmm hnn hmodd hu
    linarith
  · intro ho
    rw [eval_affineBelyi] at ho
    have hneg := eval_belyi_neg_of_lt_zero hmm hnn hmodd hu
    linarith
  · exact affineBelyi_critIn01 (by omega) (by omega) (hab.trans hbc).ne


end LeanFormal.IUT.XiFPaper.Mzk1BetaAvoidingBelyiSmallActual
end