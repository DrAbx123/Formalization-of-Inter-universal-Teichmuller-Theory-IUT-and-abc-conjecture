import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1ProtectedToZeroMapActual
open Polynomial

variable {K : Type*} [Field K] [DecidableEq K]

/-- The concrete polynomial `g(x) = ∏_{t∈T} (x - t)` sending all protected
points `T` to the ordinary value `0`. -/
def protectedToZeroPolynomial (T : Finset K) : K[X] :=
  ∏ t ∈ T, (Polynomial.X - Polynomial.C t)

/-- Every protected point is sent to `0`. -/
theorem eval_protectedToZero_of_mem {T : Finset K} {t : K} (ht : t ∈ T) :
    Polynomial.eval t (protectedToZeroPolynomial T) = 0 := by
  unfold protectedToZeroPolynomial
  rw [Polynomial.eval_prod]
  have hfac : ∀ s : K, Polynomial.eval t (Polynomial.X - Polynomial.C s) = t - s := by
    intro s
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  simp_rw [hfac]
  exact Finset.prod_eq_zero ht (by simp)

/-- Derivative at a protected point: `g'(t) = ∏_{s≠t}(t-s)`. -/
theorem eval_derivative_protectedToZero {T : Finset K} {t : K} (ht : t ∈ T) :
    Polynomial.eval t (Polynomial.derivative (protectedToZeroPolynomial T)) =
      ∏ s ∈ T.erase t, (t - s) := by
  have hmem : t ∈ T.val :=
    (Finset.mem_val).mpr ht
  have h := Polynomial.eval_multiset_prod_X_sub_C_derivative (S := T.val) (r := t) hmem
  simpa [protectedToZeroPolynomial, Finset.prod_eq_multiset_prod, Multiset.map] using h

/-- The derivative is nonzero at every protected point, so the `0`-fiber has
only simple (unramified) roots. -/
theorem eval_derivative_protectedToZero_ne_zero {T : Finset K} {t : K} (ht : t ∈ T) :
    Polynomial.eval t (Polynomial.derivative (protectedToZeroPolynomial T)) ≠ 0 := by
  rw [eval_derivative_protectedToZero ht]
  apply Finset.prod_ne_zero_iff.mpr
  intro s hs
  exact sub_ne_zero.mpr (Ne.symm (Finset.mem_erase.mp hs).1)

#print axioms eval_protectedToZero_of_mem
#print axioms eval_derivative_protectedToZero
#print axioms eval_derivative_protectedToZero_ne_zero
end LeanFormal.IUT.XiFPaper.Mzk1G1ProtectedToZeroMapActual