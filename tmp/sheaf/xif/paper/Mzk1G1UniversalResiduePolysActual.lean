import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.ZMod.Basic

/-!
# Universal residue polynomials for route 7.2, step 2

For a prime p, a modulus exponent N and a degree bound d, this file builds the
concrete finite family of monic degree-d polynomials over Z_p whose d lower
coefficients are the canonical integer representatives of residue classes in
ZMod (p^N).  The family is the image of the finite type Fin d -> ZMod (p^N), hence
finite, and each member is monic of degree exactly d.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1G1UniversalResiduePolysActual

open Polynomial

variable (p : ℕ) [Fact p.Prime]

/-- The canonical lift of a residue class c : ZMod (p^N): its representative
0 ≤ c.val < p^N regarded as a p-adic integer.

Mathlib has no PadicInt.ofInt in the present version, so we use the natural-number
cast, which is the same canonical integer representative. -/
noncomputable def residueCoeffLift (N : ℕ) (c : ZMod (p ^ N)) : ℤ_[p] :=
  ((c.val : ℕ) : ℤ_[p])

/-- The lower-degree part sum_{i < d} lift (c i) * X^i of the universal residue
polynomial.  For d = 0 this is the zero polynomial. -/
noncomputable def residueMonicPolyLower (N d : ℕ) (c : Fin d → ZMod (p ^ N)) :
    Polynomial ℤ_[p] :=
  ∑ i : Fin d, monomial (i : ℕ) (residueCoeffLift p N (c i))

/-- The monic polynomial of degree d

X^d + sum_{i < d} lift (c i) * X^i

determined by the d residue classes c modulo p^N.  For d = 0 this is the
constant polynomial 1. -/
noncomputable def residueMonicPoly (N d : ℕ) (c : Fin d → ZMod (p ^ N)) :
    Polynomial ℤ_[p] :=
  X ^ d + residueMonicPolyLower p N d c

/-- The lower-degree part really has degree < d.  For d = 0 it is the zero
polynomial, whose degree is bot; this is why the statement is phrased with degree
rather than natDegree. -/
theorem degree_residueMonicPolyLower_lt (N d : ℕ) (c : Fin d → ZMod (p ^ N)) :
    (residueMonicPolyLower p N d c).degree < (d : WithBot ℕ) := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    simp [residueMonicPolyLower]
  · refine lt_of_le_of_lt
      (degree_sum_le (Finset.univ : Finset (Fin d))
        (fun i : Fin d => monomial (i : ℕ) (residueCoeffLift p N (c i)))) ?_
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe d)).mpr ?_
    intro i _
    exact lt_of_le_of_lt (degree_monomial_le (i : ℕ) (residueCoeffLift p N (c i)))
      (WithBot.coe_lt_coe.mpr i.isLt)

/-- Each residueMonicPoly is monic. -/
theorem residueMonicPoly_monic (N d : ℕ) (c : Fin d → ZMod (p ^ N)) :
    (residueMonicPoly p N d c).Monic := by
  rw [residueMonicPoly]
  exact monic_X_pow_add (p := residueMonicPolyLower p N d c) (n := d)
    (degree_residueMonicPolyLower_lt p N d c)

/-- Each residueMonicPoly has natDegree exactly d (so degree exactly d). -/
theorem residueMonicPoly_natDegree (N d : ℕ) (c : Fin d → ZMod (p ^ N)) :
    (residueMonicPoly p N d c).natDegree = d := by
  rw [residueMonicPoly]
  have h : (residueMonicPolyLower p N d c).degree <
      (X ^ d : Polynomial ℤ_[p]).degree := by
    simpa using degree_residueMonicPolyLower_lt p N d c
  rw [natDegree_add_eq_left_of_degree_lt h, natDegree_X_pow]

/-- In degree 0 the construction is the constant polynomial 1 (the empty lower
sum vanishes), so no separate definition is needed for the constant case. -/
theorem residueMonicPoly_zero (N : ℕ) (c : Fin 0 → ZMod (p ^ N)) :
    residueMonicPoly p N 0 c = 1 := by
  simp [residueMonicPoly, residueMonicPolyLower]

/-- The universal residue family is finite: it is the range of a map on the finite
type Fin d -> ZMod (p^N). -/
theorem residueMonicPoly_finite (N d : ℕ) :
    (Set.range (residueMonicPoly p N d)).Finite := by
  haveI : NeZero (p ^ N) := ⟨pow_ne_zero N (Fact.out : p.Prime).ne_zero⟩
  exact Set.finite_range (residueMonicPoly p N d)


/-- The coefficient in degree i < d is exactly the lifted residue class c i. -/
theorem residueMonicPoly_coeff_of_lt (N d : ℕ) (c : Fin d → ZMod (p ^ N))
    {i : ℕ} (hi : i < d) :
    (residueMonicPoly p N d c).coeff i = residueCoeffLift p N (c ⟨i, hi⟩) := by
  have hlt : i ≠ d := Nat.ne_of_lt hi
  have hsum : (residueMonicPolyLower p N d c).coeff i =
      residueCoeffLift p N (c ⟨i, hi⟩) := by
    rw [residueMonicPolyLower, finsetSum_coeff]
    have hsingle : (∑ j : Fin d,
        (if (j : ℕ) = i then residueCoeffLift p N (c j) else (0 : ℤ_[p]))) =
        residueCoeffLift p N (c ⟨i, hi⟩) := by
      simpa [Fin.ext_iff] using
        (Finset.sum_ite_eq' (Finset.univ : Finset (Fin d)) (⟨i, hi⟩ : Fin d)
          (fun j : Fin d => residueCoeffLift p N (c j)))
    simpa only [coeff_monomial] using hsingle
  rw [residueMonicPoly, Polynomial.coeff_add, Polynomial.coeff_X_pow,
    if_neg hlt, zero_add, hsum]

/-- The leading coefficient in degree d is 1. -/
theorem residueMonicPoly_coeff_self (N d : ℕ) (c : Fin d → ZMod (p ^ N)) :
    (residueMonicPoly p N d c).coeff d = 1 := by
  have hzero : (residueMonicPolyLower p N d c).coeff d = 0 := by
    rw [residueMonicPolyLower, finsetSum_coeff]
    apply Finset.sum_eq_zero
    intro j _
    rw [coeff_monomial]
    exact if_neg (Nat.ne_of_lt j.isLt)
  rw [residueMonicPoly, Polynomial.coeff_add, Polynomial.coeff_X_pow_self,
    hzero, add_zero]

/-- Coefficients in degree i > d vanish. -/
theorem residueMonicPoly_coeff_of_gt (N d : ℕ) (c : Fin d → ZMod (p ^ N))
    {i : ℕ} (hi : d < i) :
    (residueMonicPoly p N d c).coeff i = 0 := by
  have hzero : (residueMonicPolyLower p N d c).coeff i = 0 := by
    rw [residueMonicPolyLower, finsetSum_coeff]
    apply Finset.sum_eq_zero
    intro j _
    rw [coeff_monomial]
    exact if_neg (Nat.ne_of_lt (lt_trans j.isLt hi))
  rw [residueMonicPoly, Polynomial.coeff_add, Polynomial.coeff_X_pow,
    if_neg (Nat.ne_of_gt hi), hzero, zero_add]

/-- Complete coefficient description: the lower d coefficients are the canonical
lifts of the residue classes, the degree-d coefficient is 1, and all higher
coefficients vanish. -/
theorem residueMonicPoly_coeff_bound (N d : ℕ) (c : Fin d → ZMod (p ^ N)) (i : ℕ) :
    (residueMonicPoly p N d c).coeff i =
      if h : i < d then residueCoeffLift p N (c ⟨i, h⟩)
      else if i = d then 1 else 0 := by
  by_cases h : i < d
  · rw [dif_pos h]
    exact residueMonicPoly_coeff_of_lt p N d c h
  · rw [dif_neg h]
    by_cases hd : i = d
    · subst hd
      simp [residueMonicPoly_coeff_self]
    · rw [if_neg hd]
      exact residueMonicPoly_coeff_of_gt p N d c
        (lt_of_le_of_ne (Nat.le_of_not_lt h) (Ne.symm hd))

#print axioms residueCoeffLift
#print axioms residueMonicPolyLower
#print axioms residueMonicPoly
#print axioms degree_residueMonicPolyLower_lt
#print axioms residueMonicPoly_monic
#print axioms residueMonicPoly_natDegree
#print axioms residueMonicPoly_zero
#print axioms residueMonicPoly_coeff_of_lt
#print axioms residueMonicPoly_coeff_self
#print axioms residueMonicPoly_coeff_of_gt
#print axioms residueMonicPoly_coeff_bound
#print axioms residueMonicPoly_finite

end LeanFormal.IUT.XiFPaper.Mzk1G1UniversalResiduePolysActual
