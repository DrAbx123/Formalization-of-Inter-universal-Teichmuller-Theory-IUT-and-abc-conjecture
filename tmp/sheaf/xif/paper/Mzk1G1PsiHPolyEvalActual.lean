import tmp.sheaf.xif.paper.Mzk1G1PsiHPolyActual
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Tactic

noncomputable section
open AlgebraicGeometry CategoryTheory Polynomial

namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyEvalActual

open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyActual

variable (h : Polynomial ℚ)

/-! ## Auxiliary lemmas about Polynomial.reflect and Polynomial.reverse -/

/-- `reflect` distributes over finite sums of polynomials. -/
private lemma reflect_sum {A : Type*} [Semiring A] (N : ℕ) {ι : Type*}
    (s : Finset ι) (g : ι → Polynomial A) :
    (∑ i ∈ s, g i).reflect N = ∑ i ∈ s, (g i).reflect N := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Polynomial.reflect_add, ih]

/-- Sum formula for `reflect`: if `natDegree f ≤ N`, then `f.reflect N` is the sum
`∑ i ∈ f.support, C (f.coeff i) * X ^ (N - i)`. -/
private lemma reflect_eq_sum_C_mul_X_pow {A : Type*} [Semiring A] (N : ℕ)
    (f : Polynomial A) (hN : f.natDegree ≤ N) :
    f.reflect N = ∑ i ∈ f.support, Polynomial.C (f.coeff i) * Polynomial.X ^ (N - i) := by
  conv_lhs => rw [Polynomial.as_sum_support_C_mul_X_pow f]
  rw [reflect_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [Polynomial.reflect_C_mul_X_pow,
    Polynomial.revAt_le (le_trans (Polynomial.le_natDegree_of_mem_supp i hi) hN)]

/-- local copy of the bridge hRev = reverse (for nonzero h). -/
theorem hRev_eq_reverse_local (hh : h ≠ 0) : hRev h = h.reverse := by
  unfold hRev
  show (∑ i ∈ h.support, Polynomial.C (h.coeff i) * Polynomial.X ^ (h.natDegree - i)) =
    h.reflect h.natDegree
  exact (reflect_eq_sum_C_mul_X_pow h.natDegree h le_rfl).symm

/-! ## The unit lambda of R = Away X, and its inverse -/

/-- The unit lambda = algebraMap ℚ[X] R X in R = ℚ[X][1/X]. -/
private noncomputable def uLambda : (Localization.Away (Polynomial.X : Polynomial ℚ))ˣ :=
  (IsLocalization.Away.algebraMap_isUnit
    (S := Localization.Away (Polynomial.X : Polynomial ℚ))
    (x := (Polynomial.X : Polynomial ℚ))).unit

private theorem uLambda_val :
    ((uLambda : (Localization.Away (Polynomial.X : Polynomial ℚ))ˣ) :
      Localization.Away (Polynomial.X : Polynomial ℚ)) =
      algebraMap (Polynomial ℚ) (Localization.Away (Polynomial.X : Polynomial ℚ))
        (Polynomial.X : Polynomial ℚ) :=
  IsUnit.unit_spec _

/-- `IsLocalization.Away.invSelf X` is the value of the inverse of the unit `uLambda`. -/
private theorem invSelf_eq_inv_uLambda :
    IsLocalization.Away.invSelf (x := (Polynomial.X : Polynomial ℚ)) =
      (((uLambda)⁻¹ : (Localization.Away (Polynomial.X : Polynomial ℚ))ˣ) :
        Localization.Away (Polynomial.X : Polynomial ℚ)) := by
  have h1 : ((uLambda : (Localization.Away (Polynomial.X : Polynomial ℚ))ˣ) :
      Localization.Away (Polynomial.X : Polynomial ℚ)) *
      IsLocalization.Away.invSelf (x := (Polynomial.X : Polynomial ℚ)) = 1 := by
    rw [uLambda_val, IsLocalization.Away.mul_invSelf]
  have h2 : ((uLambda : (Localization.Away (Polynomial.X : Polynomial ℚ))ˣ) :
      Localization.Away (Polynomial.X : Polynomial ℚ)) *
      (((uLambda)⁻¹ : (Localization.Away (Polynomial.X : Polynomial ℚ))ˣ) :
        Localization.Away (Polynomial.X : Polynomial ℚ)) = 1 :=
    Units.mul_inv uLambda
  have hEq : (((uLambda)⁻¹ : (Localization.Away (Polynomial.X : Polynomial ℚ))ˣ) :
        Localization.Away (Polynomial.X : Polynomial ℚ)) *
      (((uLambda : (Localization.Away (Polynomial.X : Polynomial ℚ))ˣ) :
          Localization.Away (Polynomial.X : Polynomial ℚ)) *
        IsLocalization.Away.invSelf (x := (Polynomial.X : Polynomial ℚ))) =
      (((uLambda)⁻¹ : (Localization.Away (Polynomial.X : Polynomial ℚ))ˣ) :
          Localization.Away (Polynomial.X : Polynomial ℚ)) *
        (((uLambda : (Localization.Away (Polynomial.X : Polynomial ℚ))ˣ) :
            Localization.Away (Polynomial.X : Polynomial ℚ)) *
          (((uLambda)⁻¹ : (Localization.Away (Polynomial.X : Polynomial ℚ))ˣ) :
            Localization.Away (Polynomial.X : Polynomial ℚ))) := by
    rw [h1, h2]
  rw [← mul_assoc, Units.inv_mul, one_mul, ← mul_assoc, Units.inv_mul, one_mul] at hEq
  exact hEq

/-- `⅟ (↑uLambda⁻¹) = ↑uLambda`: the inverse of the inverse of the unit lambda. -/
private theorem invOf_inv_uLambda_val :
    ⅟((((uLambda)⁻¹ : (Localization.Away (Polynomial.X : Polynomial ℚ))ˣ) :
        Localization.Away (Polynomial.X : Polynomial ℚ))) =
      ((uLambda : (Localization.Away (Polynomial.X : Polynomial ℚ))ˣ) :
        Localization.Away (Polynomial.X : Polynomial ℚ)) := by
  apply invOf_eq_right_inv
  exact Units.inv_mul uLambda

/-- The polynomial-ring map out of ℚ[X] sending X to the image of X is `algebraMap`. -/
private theorem eval₂_algebraMap_X_eq_algebraMap (p : Polynomial ℚ) :
    Polynomial.eval₂ (algebraMap ℚ (Localization.Away (Polynomial.X : Polynomial ℚ)))
        (algebraMap (Polynomial ℚ) (Localization.Away (Polynomial.X : Polynomial ℚ))
          (Polynomial.X : Polynomial ℚ)) p =
      algebraMap (Polynomial ℚ) (Localization.Away (Polynomial.X : Polynomial ℚ)) p :=
  Polynomial.eval₂_algebraMap_X p
    (IsScalarTower.toAlgHom ℚ (Polynomial ℚ)
      (Localization.Away (Polynomial.X : Polynomial ℚ)))

/-- the unit lambda in R = Away X, and the identity h(lambda⁻¹) = lambda^{-d} hRev(lambda). -/
theorem evalAt_invSelf_h (hh : h ≠ 0) :
    Mzk1G1ProjectiveLineTransitionActual.evalAt
        (R := Localization.Away (Polynomial.X : Polynomial ℚ))
        (IsLocalization.Away.invSelf (x := (Polynomial.X : Polynomial ℚ))) h =
      (IsLocalization.Away.invSelf (x := (Polynomial.X : Polynomial ℚ))) ^ h.natDegree *
        algebraMap (Polynomial ℚ) (Localization.Away (Polynomial.X : Polynomial ℚ)) (hRev h) := by
  have hrev : hRev h = h.reverse := hRev_eq_reverse_local h hh
  have hmain := Polynomial.eval₂_reverse_mul_pow
    (R := ℚ) (S := Localization.Away (Polynomial.X : Polynomial ℚ))
    (algebraMap ℚ (Localization.Away (Polynomial.X : Polynomial ℚ)))
    (((uLambda)⁻¹ : (Localization.Away (Polynomial.X : Polynomial ℚ))ˣ) :
      Localization.Away (Polynomial.X : Polynomial ℚ)) h
  rw [invOf_inv_uLambda_val] at hmain
  have hrev_eval :
      Polynomial.eval₂ (algebraMap ℚ (Localization.Away (Polynomial.X : Polynomial ℚ)))
        ((uLambda : (Localization.Away (Polynomial.X : Polynomial ℚ))ˣ) :
          Localization.Away (Polynomial.X : Polynomial ℚ)) (Polynomial.reverse h) =
        algebraMap (Polynomial ℚ) (Localization.Away (Polynomial.X : Polynomial ℚ)) (hRev h) := by
    rw [uLambda_val, eval₂_algebraMap_X_eq_algebraMap (Polynomial.reverse h), ← hrev]
  rw [hrev_eval] at hmain
  rw [← invSelf_eq_inv_uLambda] at hmain
  rw [mul_comm (algebraMap (Polynomial ℚ)
    (Localization.Away (Polynomial.X : Polynomial ℚ)) (hRev h))] at hmain
  exact hmain.symm

#print axioms hRev_eq_reverse_local
#print axioms evalAt_invSelf_h
end LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyEvalActual
