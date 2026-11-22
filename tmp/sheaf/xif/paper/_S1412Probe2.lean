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

lemma pointOfX_ne_zero (x : F) : pointOfX W x ≠ 0 := by
  rw [pointOfX]
  exact WeierstrassCurve.Affine.Point.some_ne_zero _

lemma pointOfX_nonsingular (x : F) :
    W.Nonsingular x (Classical.choose (exists_nonsingular_of_x W x)) :=
  Classical.choose_spec (exists_nonsingular_of_x W x)

example (x : F) : (pointOfX W x).xRep = ![x, 1] := by
  rw [pointOfX, WeierstrassCurve.Affine.Point.xRep_some]

end Probe1412