import LeanFormal.IUT.ABCBridge.Galois.EllipticDivisionPolynomialEvaluation
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Data.Finsupp.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open Polynomial
open scoped BigOperators

namespace Probe1412

variable {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]
variable (W : WeierstrassCurve.Affine F) [W.IsElliptic]

lemma exists_nonsingular_of_x (x : F) : ∃ y : F, W.Nonsingular x y := by
  classical
  let q : F[X] := X ^ 2 + C (W.a₁ * x + W.a₃) * X -
    C (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)
  have hqdeg : q.degree = 2 := by
    change (X ^ 2 + C (W.a₁ * x + W.a₃) * X -
      C (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) : F[X]).degree = 2
    compute_degree!
  have hdeg : q.degree ≠ 0 := by rw [hqdeg]; norm_num
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root q hdeg
  refine ⟨y, ?_⟩
  apply (WeierstrassCurve.Affine.equation_iff_nonsingular (W := W)).mp
  rw [WeierstrassCurve.Affine.equation_iff']
  have hy' : y ^ 2 + (W.a₁ * x + W.a₃) * y -
      (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = 0 := by
    simpa only [q, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Polynomial.IsRoot.def] using hy
  linear_combination hy'

noncomputable def pointOfX (x : F) : W.Point :=
  WeierstrassCurve.Affine.Point.some x
    (Classical.choose (exists_nonsingular_of_x W x))
    (Classical.choose_spec (exists_nonsingular_of_x W x))

noncomputable def psiDivisor (n : ℤ) : W.Point →₀ ℤ :=
  (∑ x ∈ (W.preΨ n).roots.toFinset,
    ((W.preΨ n).rootMultiplicity x : ℤ) •
      (Finsupp.single (pointOfX W x) (1 : ℤ) +
        Finsupp.single (-(pointOfX W x)) (1 : ℤ))) -
    (2 * (W.preΨ n).natDegree : ℤ) • Finsupp.single (0 : W.Point) (1 : ℤ)

example (n : ℤ) : (psiDivisor W n).sum (fun _ m => m) =
    (∑ x ∈ (W.preΨ n).roots.toFinset,
      ((W.preΨ n).rootMultiplicity x : ℤ) * 2) -
      2 * (W.preΨ n).natDegree := by
  rw [psiDivisor]
  rw [Finsupp.sum_sub_index]
  · congr 1
    · rw [← Finsupp.sum_finsetSum_index]
      · apply Finset.sum_congr rfl
        intro x hx
        rw [Finsupp.sum_smul_index]
        · rw [Finsupp.sum_add_index]
          · simp
          · intro a b c; ring
        · intro a; ring
      · intro a; ring
      · intro a b c; ring
    · rw [Finsupp.sum_smul_index]
      · simp
      · intro a; ring
  · intro a; ring
  · intro a b c; ring

end Probe1412