import tmp.sheaf.xif.paper.Mzk1G1QHeightActual
import Mathlib.NumberTheory.Height.MvPolynomial
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.G1JHeightD3Actual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.G1QHeightActual
open MvPolynomial

variable {K : Type*} [Field K] [NumberField K]

/-!
# D3: the height comparison `h(j(lam)) = 6 h(lam) + O(1)` over number fields

Route section 6.3: the actual rational function
`j(lam) = 256 (1 - lam + lam^2)^3 / (lam^2 (1 - lam)^2)`
is a degree 6 morphism of P^1; its homogenization is controlled by explicit
Bezout relations.  We prove the resulting two-sided height comparison

`exists B, forall lam, |jHeight lam - 6 * lambdaHeight lam| <= B`

over every number field `K`.  The integer Bezout identities are proved by
`ring` with numeral coefficients ascribed to the polynomial ring over `K`;
the height step uses Mathlib's `Height.logHeight_eval_le'` and
`Height.logHeight_eval_ge'`.
-/

/-! ## Numeral-coefficient models -/

/-- Numerator coordinate of the degree 6 j-map, with numeral coefficients. -/
def jNumN : MvPolynomial (Fin 2) K :=
  (256 : MvPolynomial (Fin 2) K) * (MvPolynomial.X 0 ^ 2 - MvPolynomial.X 0 * MvPolynomial.X 1
    + MvPolynomial.X 1 ^ 2) ^ 3

/-- Denominator coordinate of the degree 6 j-map, with numeral coefficients. -/
def jDenN : MvPolynomial (Fin 2) K :=
  MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 2 * (MvPolynomial.X 1 - MvPolynomial.X 0) ^ 2

/-- Scaled Bezout coefficient 256 * q(0,0). -/
def Q00N : MvPolynomial (Fin 2) K :=
  (-3 : MvPolynomial (Fin 2) K) * (MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 2)
    + (3 : MvPolynomial (Fin 2) K) * (MvPolynomial.X 0 ^ 3 * MvPolynomial.X 1)
    + (1 : MvPolynomial (Fin 2) K) * (MvPolynomial.X 0 ^ 4 * MvPolynomial.X 1 ^ 0)

/-- Scaled Bezout coefficient 256 * q(0,1). -/
def Q01N : MvPolynomial (Fin 2) K :=
  (256 : MvPolynomial (Fin 2) K) * ((3 : MvPolynomial (Fin 2) K) * (MvPolynomial.X 0 ^ 0 * MvPolynomial.X 1 ^ 4)
    + (-6 : MvPolynomial (Fin 2) K) * (MvPolynomial.X 0 ^ 1 * MvPolynomial.X 1 ^ 3)
    + (11 : MvPolynomial (Fin 2) K) * (MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 2)
    + (-8 : MvPolynomial (Fin 2) K) * (MvPolynomial.X 0 ^ 3 * MvPolynomial.X 1 ^ 1)
    + (6 : MvPolynomial (Fin 2) K) * (MvPolynomial.X 0 ^ 4 * MvPolynomial.X 1 ^ 0))

/-- Scaled Bezout coefficient 256 * q(1,0). -/
def Q10N : MvPolynomial (Fin 2) K :=
  (1 : MvPolynomial (Fin 2) K) * (MvPolynomial.X 0 ^ 0 * MvPolynomial.X 1 ^ 4)
    + (3 : MvPolynomial (Fin 2) K) * (MvPolynomial.X 0 ^ 1 * MvPolynomial.X 1 ^ 3)
    + (-3 : MvPolynomial (Fin 2) K) * (MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 2)

/-- Scaled Bezout coefficient 256 * q(1,1). -/
def Q11N : MvPolynomial (Fin 2) K :=
  (256 : MvPolynomial (Fin 2) K) * ((6 : MvPolynomial (Fin 2) K) * (MvPolynomial.X 0 ^ 0 * MvPolynomial.X 1 ^ 4)
    + (-8 : MvPolynomial (Fin 2) K) * (MvPolynomial.X 0 ^ 1 * MvPolynomial.X 1 ^ 3)
    + (11 : MvPolynomial (Fin 2) K) * (MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 2)
    + (-6 : MvPolynomial (Fin 2) K) * (MvPolynomial.X 0 ^ 3 * MvPolynomial.X 1 ^ 1)
    + (3 : MvPolynomial (Fin 2) K) * (MvPolynomial.X 0 ^ 4 * MvPolynomial.X 1 ^ 0))

theorem jNumN_eq_jNum : (jNumN (K := K)) = jNum (K := K) := by
  have h : (256 : MvPolynomial (Fin 2) K) = MvPolynomial.C (256 : K) :=
    (map_natCast (algebraMap K (MvPolynomial (Fin 2) K)) 256).symm
  unfold jNumN jNum
  rw [h]

theorem jDenN_eq_jDen : (jDenN (K := K)) = jDen (K := K) := rfl

/-! ## Homogeneity -/

private lemma isHomogeneous_four_mul (a b : ℕ) (c : MvPolynomial (Fin 2) K)
    (hc : c.IsHomogeneous 0) (hab : a + b = 4) :
    (c * (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b)
      : MvPolynomial (Fin 2) K).IsHomogeneous 4 := by
  have h1 : (MvPolynomial.X 0 ^ a : MvPolynomial (Fin 2) K).IsHomogeneous a :=
    MvPolynomial.isHomogeneous_X_pow (σ := Fin 2) (R := K) 0 a
  have h2 : (MvPolynomial.X 1 ^ b : MvPolynomial (Fin 2) K).IsHomogeneous b :=
    MvPolynomial.isHomogeneous_X_pow (σ := Fin 2) (R := K) 1 b
  have h3 := hc.mul (h1.mul h2)
  simpa [hab] using h3

private lemma isHomogeneous_numeral_zero (n : ℕ) :
    ((n : MvPolynomial (Fin 2) K)).IsHomogeneous 0 := by
  have h : (n : MvPolynomial (Fin 2) K) = MvPolynomial.C ((n : ℕ) : K) := by
    rw [← MvPolynomial.algebraMap_eq]
    exact (map_natCast (algebraMap K (MvPolynomial (Fin 2) K)) n).symm
  rw [h]
  exact MvPolynomial.isHomogeneous_C (σ := Fin 2) (R := K) ((n : ℕ) : K)

set_option maxHeartbeats 800000 in
theorem Q00N_isHomogeneous : (Q00N (K := K)).IsHomogeneous 4 := by
  unfold Q00N
  have t1 := isHomogeneous_four_mul 2 2 (-(3 : MvPolynomial (Fin 2) K))
    (by simpa using (isHomogeneous_numeral_zero 3).neg) (by norm_num)
  have t2 := isHomogeneous_four_mul 3 1 (3 : MvPolynomial (Fin 2) K)
    (by simpa using isHomogeneous_numeral_zero 3) (by norm_num)
  have t3 := isHomogeneous_four_mul 4 0 (1 : MvPolynomial (Fin 2) K)
    (by simpa using isHomogeneous_numeral_zero 1) (by norm_num)
  simpa [pow_one, pow_zero, add_assoc] using (t1.add t2).add t3

set_option maxHeartbeats 800000 in
theorem Q01N_isHomogeneous : (Q01N (K := K)).IsHomogeneous 4 := by
  unfold Q01N
  have t1 := isHomogeneous_four_mul 0 4 (3 : MvPolynomial (Fin 2) K)
    (by simpa using isHomogeneous_numeral_zero 3) (by norm_num)
  have t2 := isHomogeneous_four_mul 1 3 (-(6 : MvPolynomial (Fin 2) K))
    (by simpa using (isHomogeneous_numeral_zero 6).neg) (by norm_num)
  have t3 := isHomogeneous_four_mul 2 2 (11 : MvPolynomial (Fin 2) K)
    (by simpa using isHomogeneous_numeral_zero 11) (by norm_num)
  have t4 := isHomogeneous_four_mul 3 1 (-(8 : MvPolynomial (Fin 2) K))
    (by simpa using (isHomogeneous_numeral_zero 8).neg) (by norm_num)
  have t5 := isHomogeneous_four_mul 4 0 (6 : MvPolynomial (Fin 2) K)
    (by simpa using isHomogeneous_numeral_zero 6) (by norm_num)
  have hsum : ((3 : MvPolynomial (Fin 2) K) * (MvPolynomial.X 0 ^ 0 * MvPolynomial.X 1 ^ 4)
      + (-(6 : MvPolynomial (Fin 2) K)) * (MvPolynomial.X 0 ^ 1 * MvPolynomial.X 1 ^ 3)
      + (11 : MvPolynomial (Fin 2) K) * (MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 2)
      + (-(8 : MvPolynomial (Fin 2) K)) * (MvPolynomial.X 0 ^ 3 * MvPolynomial.X 1 ^ 1)
      + (6 : MvPolynomial (Fin 2) K) * (MvPolynomial.X 0 ^ 4 * MvPolynomial.X 1 ^ 0)).IsHomogeneous 4 :=
    (by simpa [pow_one, pow_zero, add_assoc] using ((t1.add t2).add (t3.add t4)).add t5)
  simpa [pow_one, pow_zero, add_assoc] using (isHomogeneous_numeral_zero 256).mul hsum

set_option maxHeartbeats 800000 in
theorem Q10N_isHomogeneous : (Q10N (K := K)).IsHomogeneous 4 := by
  unfold Q10N
  have t1 := isHomogeneous_four_mul 0 4 (1 : MvPolynomial (Fin 2) K)
    (by simpa using isHomogeneous_numeral_zero 1) (by norm_num)
  have t2 := isHomogeneous_four_mul 1 3 (3 : MvPolynomial (Fin 2) K)
    (by simpa using isHomogeneous_numeral_zero 3) (by norm_num)
  have t3 := isHomogeneous_four_mul 2 2 (-(3 : MvPolynomial (Fin 2) K))
    (by simpa using (isHomogeneous_numeral_zero 3).neg) (by norm_num)
  simpa [pow_one, pow_zero, add_assoc] using (t1.add t2).add t3

set_option maxHeartbeats 800000 in
theorem Q11N_isHomogeneous : (Q11N (K := K)).IsHomogeneous 4 := by
  unfold Q11N
  have t1 := isHomogeneous_four_mul 0 4 (6 : MvPolynomial (Fin 2) K)
    (by simpa using isHomogeneous_numeral_zero 6) (by norm_num)
  have t2 := isHomogeneous_four_mul 1 3 (-(8 : MvPolynomial (Fin 2) K))
    (by simpa using (isHomogeneous_numeral_zero 8).neg) (by norm_num)
  have t3 := isHomogeneous_four_mul 2 2 (11 : MvPolynomial (Fin 2) K)
    (by simpa using isHomogeneous_numeral_zero 11) (by norm_num)
  have t4 := isHomogeneous_four_mul 3 1 (-(6 : MvPolynomial (Fin 2) K))
    (by simpa using (isHomogeneous_numeral_zero 6).neg) (by norm_num)
  have t5 := isHomogeneous_four_mul 4 0 (3 : MvPolynomial (Fin 2) K)
    (by simpa using isHomogeneous_numeral_zero 3) (by norm_num)
  have hsum : ((6 : MvPolynomial (Fin 2) K) * (MvPolynomial.X 0 ^ 0 * MvPolynomial.X 1 ^ 4)
      + (-(8 : MvPolynomial (Fin 2) K)) * (MvPolynomial.X 0 ^ 1 * MvPolynomial.X 1 ^ 3)
      + (11 : MvPolynomial (Fin 2) K) * (MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 2)
      + (-(6 : MvPolynomial (Fin 2) K)) * (MvPolynomial.X 0 ^ 3 * MvPolynomial.X 1 ^ 1)
      + (3 : MvPolynomial (Fin 2) K) * (MvPolynomial.X 0 ^ 4 * MvPolynomial.X 1 ^ 0)).IsHomogeneous 4 :=
    (by simpa [pow_one, pow_zero, add_assoc] using ((t1.add t2).add (t3.add t4)).add t5)
  simpa [pow_one, pow_zero, add_assoc] using (isHomogeneous_numeral_zero 256).mul hsum

theorem jNumN_isHomogeneous : (jNumN (K := K)).IsHomogeneous 6 := by
  rw [jNumN_eq_jNum]
  exact jNum_isHomogeneous (K := K)

theorem jDenN_isHomogeneous : (jDenN (K := K)).IsHomogeneous 6 := by
  rw [jDenN_eq_jDen]
  exact jDen_isHomogeneous (K := K)

/-- The Bezout coefficient family over K, degree 4. -/
def QK : Fin 2 × Fin 2 → MvPolynomial (Fin 2) K :=
  fun a => if a.1 = 0 then (if a.2 = 0 then Q00N (K := K) else Q01N (K := K))
    else (if a.2 = 0 then Q10N (K := K) else Q11N (K := K))

theorem QK_isHomogeneous : ∀ a, (QK (K := K) a).IsHomogeneous 4 := by
  intro a
  unfold QK
  by_cases h1 : a.1 = 0 <;> by_cases h2 : a.2 = 0 <;>
    simp [h1, h2, Q00N_isHomogeneous (K := K), Q01N_isHomogeneous (K := K),
      Q10N_isHomogeneous (K := K), Q11N_isHomogeneous (K := K)]

/-- The scaled coordinates of the j-map used for the lower height bound. -/
def pN : Fin 2 → MvPolynomial (Fin 2) K :=
  ![MvPolynomial.C ((256 : K)⁻¹) * jNumN (K := K),
    MvPolynomial.C ((256 : K)⁻¹) * jDenN (K := K)]

theorem pN_isHomogeneous : ∀ i : Fin 2, (pN (K := K) i).IsHomogeneous 6 := by
  intro i
  fin_cases i
  · simpa [pN] using (MvPolynomial.isHomogeneous_C (σ := Fin 2) (R := K) ((256 : K)⁻¹)).mul
      (jNumN_isHomogeneous (K := K))
  · simpa [pN] using (MvPolynomial.isHomogeneous_C (σ := Fin 2) (R := K) ((256 : K)⁻¹)).mul
      (jDenN_isHomogeneous (K := K))

/-! ## Kernel-checked Bezout identities over K -/

theorem jBezN_left :
    Q00N * jNumN + Q01N * jDenN = (256 : MvPolynomial (Fin 2) K) * MvPolynomial.X 0 ^ 10 := by
  unfold Q00N Q01N jNumN jDenN
  ring

theorem jBezN_right :
    Q10N * jNumN + Q11N * jDenN = (256 : MvPolynomial (Fin 2) K) * MvPolynomial.X 1 ^ 10 := by
  unfold Q10N Q11N jNumN jDenN
  ring

/-! ## The Bezout relation consumed by the height lower bound -/

theorem jBezN_relation_zero (x : Fin 2 → K) :
    ∑ j : Fin 2, (QK (K := K) (0, j)).eval x * (pN (K := K) j).eval x = (x 0) ^ (4 + 6) := by
  have h' : (Q00N (K := K)).eval x * (jNumN (K := K)).eval x
      + (Q01N (K := K)).eval x * (jDenN (K := K)).eval x = (256 : K) * (x 0) ^ 10 := by
    have hh := congrArg (MvPolynomial.eval x) (jBezN_left (K := K))
    simpa [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_pow,
      MvPolynomial.eval_X, MvPolynomial.eval_C] using hh
  have hp0 : (pN (K := K) 0).eval x = (256 : K)⁻¹ * (jNumN (K := K)).eval x := by
    simp [pN, MvPolynomial.eval_mul, MvPolynomial.eval_C]
  have hp1 : (pN (K := K) 1).eval x = (256 : K)⁻¹ * (jDenN (K := K)).eval x := by
    simp [pN, MvPolynomial.eval_mul, MvPolynomial.eval_C]
  have hQ0 : (QK (K := K) (0, 0)).eval x = (Q00N (K := K)).eval x := by simp [QK]
  have hQ1 : (QK (K := K) (0, 1)).eval x = (Q01N (K := K)).eval x := by simp [QK]
  rw [Fin.sum_univ_two, hQ0, hQ1, hp0, hp1]
  calc (Q00N (K := K)).eval x * ((256 : K)⁻¹ * (jNumN (K := K)).eval x)
      + (Q01N (K := K)).eval x * ((256 : K)⁻¹ * (jDenN (K := K)).eval x)
      = (256 : K)⁻¹ * ((Q00N (K := K)).eval x * (jNumN (K := K)).eval x
          + (Q01N (K := K)).eval x * (jDenN (K := K)).eval x) := by ring
    _ = (256 : K)⁻¹ * ((256 : K) * (x 0) ^ 10) := by rw [h']
    _ = (x 0) ^ (4 + 6) := by
      rw [← mul_assoc, inv_mul_cancel₀ (by norm_num : (256 : K) ≠ 0), one_mul]

theorem jBezN_relation_one (x : Fin 2 → K) :
    ∑ j : Fin 2, (QK (K := K) (1, j)).eval x * (pN (K := K) j).eval x = (x 1) ^ (4 + 6) := by
  have h' : (Q10N (K := K)).eval x * (jNumN (K := K)).eval x
      + (Q11N (K := K)).eval x * (jDenN (K := K)).eval x = (256 : K) * (x 1) ^ 10 := by
    have hh := congrArg (MvPolynomial.eval x) (jBezN_right (K := K))
    simpa [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_pow,
      MvPolynomial.eval_X, MvPolynomial.eval_C] using hh
  have hp0 : (pN (K := K) 0).eval x = (256 : K)⁻¹ * (jNumN (K := K)).eval x := by
    simp [pN, MvPolynomial.eval_mul, MvPolynomial.eval_C]
  have hp1 : (pN (K := K) 1).eval x = (256 : K)⁻¹ * (jDenN (K := K)).eval x := by
    simp [pN, MvPolynomial.eval_mul, MvPolynomial.eval_C]
  have hQ0 : (QK (K := K) (1, 0)).eval x = (Q10N (K := K)).eval x := by simp [QK]
  have hQ1 : (QK (K := K) (1, 1)).eval x = (Q11N (K := K)).eval x := by simp [QK]
  rw [Fin.sum_univ_two, hQ0, hQ1, hp0, hp1]
  calc (Q10N (K := K)).eval x * ((256 : K)⁻¹ * (jNumN (K := K)).eval x)
      + (Q11N (K := K)).eval x * ((256 : K)⁻¹ * (jDenN (K := K)).eval x)
      = (256 : K)⁻¹ * ((Q10N (K := K)).eval x * (jNumN (K := K)).eval x
          + (Q11N (K := K)).eval x * (jDenN (K := K)).eval x) := by ring
    _ = (256 : K)⁻¹ * ((256 : K) * (x 1) ^ 10) := by rw [h']
    _ = (x 1) ^ (4 + 6) := by
      rw [← mul_assoc, inv_mul_cancel₀ (by norm_num : (256 : K) ≠ 0), one_mul]

theorem jBezN_relation (x : Fin 2 → K) :
    ∀ k : Fin 2, ∑ j : Fin 2, (QK (K := K) (k, j)).eval x * (pN (K := K) j).eval x
      = (x k) ^ (4 + 6) := by
  intro k
  fin_cases k
  · exact jBezN_relation_zero x
  · exact jBezN_relation_one x

/-! ## Lower height bound and the D3 comparison -/

/-- Lower height bound: `6 h(lam) - C <= h(j(lam))`. -/
theorem logHeight_jHeight_ge :
    ∃ C : ℝ, ∀ lam : K, C + 6 * lambdaHeight lam ≤ jHeight lam := by
  obtain ⟨C, hC⟩ := Height.logHeight_eval_ge' (K := K) (M := 4) (N := 6)
    (q := QK (K := K)) QK_isHomogeneous
  refine ⟨C, fun lam => ?_⟩
  have hx := hC (p := pN (K := K)) (x := ![lam, 1]) (jBezN_relation ![lam, 1])
  have hleft : Height.logHeight (![lam, 1] : Fin 2 → K) = lambdaHeight lam :=
    (Height.logHeight₁_eq_logHeight lam).symm
  have hpfun : (fun j : Fin 2 => (pN (K := K) j).eval ![lam, 1])
      = (256 : K)⁻¹ • ![(jNumN (K := K)).eval ![lam, 1],
          (jDenN (K := K)).eval ![lam, 1]] := by
    funext j
    fin_cases j <;> simp [pN, Pi.smul_apply]
  have hscale : Height.logHeight ((256 : K)⁻¹ • ![(jNumN (K := K)).eval ![lam, 1],
        (jDenN (K := K)).eval ![lam, 1]])
      = Height.logHeight ![(jNumN (K := K)).eval ![lam, 1],
          (jDenN (K := K)).eval ![lam, 1]] :=
    Height.logHeight_smul_eq_logHeight _ (inv_ne_zero (by norm_num : (256 : K) ≠ 0))
  have hswap : Height.logHeight ![(jNumN (K := K)).eval ![lam, 1],
        (jDenN (K := K)).eval ![lam, 1]]
      = Height.logHeight ![((jNum (K := K)).eval ![lam, 1]),
          ((jDen (K := K)).eval ![lam, 1])] := by
    rw [jNumN_eq_jNum, jDenN_eq_jDen]
  have hright : Height.logHeight (fun j : Fin 2 => (pN (K := K) j).eval ![lam, 1]) = jHeight lam := by
    rw [hpfun, hscale, hswap]
    rw [(Height.logHeight₁_div_eq_logHeight ((jNum (K := K)).eval ![lam, 1])
      ((jDen (K := K)).eval ![lam, 1])).symm]
    rw [← legendreJ_eq_div (K := K) lam, jHeight]
  rw [hleft, hright] at hx
  exact hx

/-- **D3**: the two-sided height comparison `|h(j(lam)) - 6 h(lam)| <= B`
over every number field. -/
theorem jHeight_relation :
    ∃ B : ℝ, ∀ lam : K, |jHeight lam - 6 * lambdaHeight lam| ≤ B := by
  obtain ⟨Cu, hu⟩ := logHeight_jHeight_le (K := K)
  obtain ⟨Cl, hl⟩ := logHeight_jHeight_ge (K := K)
  refine ⟨max Cu (max 0 (-Cl)), fun lam => ?_⟩
  have h1 : jHeight lam ≤ Cu + 6 * lambdaHeight lam := hu lam
  have h2 : Cl + 6 * lambdaHeight lam ≤ jHeight lam := hl lam
  rw [abs_le]
  constructor
  · have hlow : 6 * lambdaHeight lam - jHeight lam ≤ -Cl := by linarith
    have hmax : -Cl ≤ max Cu (max 0 (-Cl)) :=
      le_trans (le_max_right 0 (-Cl)) (le_max_right Cu (max 0 (-Cl)))
    linarith
  · have hup : jHeight lam - 6 * lambdaHeight lam ≤ Cu := by linarith
    have hmax : Cu ≤ max Cu (max 0 (-Cl)) := le_max_left Cu (max 0 (-Cl))
    linarith

#print axioms jNumN_eq_jNum
#print axioms Q00N_isHomogeneous
#print axioms QK_isHomogeneous
#print axioms pN_isHomogeneous
#print axioms jBezN_left
#print axioms jBezN_right
#print axioms jBezN_relation
#print axioms logHeight_jHeight_ge
#print axioms jHeight_relation

end LeanFormal.IUT.XiFPaper.G1JHeightD3Actual
end