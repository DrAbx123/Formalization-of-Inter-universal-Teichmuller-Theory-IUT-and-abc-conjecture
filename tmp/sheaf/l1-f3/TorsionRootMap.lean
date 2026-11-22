import LeanFormal.IUT.Foundations.Geometry.EllipticTorsion
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic

/-!
# L1-F3 F3.a-proof: finite vertical fibers on a Weierstrass curve

For a fixed x on a Weierstrass curve over a field, the Weierstrass equation is
a monic quadratic in y. Hence the set of y satisfying the equation is finite.
This is the finite-fiber half of the torsion-finiteness route and is proved
unconditionally (no characteristic restriction).
-/

open LeanFormal.IUT
open WeierstrassCurve
open Polynomial

namespace LeanFormal.IUT.L1F3.TorsionRootMap

universe u

variable {K : Type u} [Field K]

/-- The finite vertical fiber of the affine Weierstrass equation at fixed x. -/
theorem equation_y_finite (W : WeierstrassCurve K) (x : K) :
    Set.Finite {y : K | W.toAffine.Equation x y} := by
  classical
  let q : K[X] := C (W.a₁ * x + W.a₃) * X -
    C (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)
  have hq : q.degree < (2 : WithBot ℕ) := by
    dsimp [q]
    compute_degree!
  let p : K[X] := X ^ 2 + q
  have hp : p ≠ 0 := (monic_X_pow_add hq).ne_zero
  have hset : {y : K | W.toAffine.Equation x y} = {y : K | p.IsRoot y} := by
    ext y
    simp only [Set.mem_setOf_eq]
    have hp_eval : p.eval y =
        y ^ 2 + (W.a₁ * x + W.a₃) * y -
          (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) := by
      simp [p, q]
      ring
    unfold Polynomial.IsRoot
    rw [hp_eval]
    constructor
    · intro h
      rw [WeierstrassCurve.Affine.equation_iff'] at h
      ring_nf at h ⊢
      exact h
    · intro h
      rw [WeierstrassCurve.Affine.equation_iff']
      ring_nf at h ⊢
      exact h
  rw [hset]
  exact Polynomial.finite_setOf_isRoot hp

/-- Finite vertical fibers over the algebraic closure for the actual source
curve. -/
theorem source_equation_y_finite (X : PuncturedEllipticCurve K)
    (x : AlgebraicClosure K) :
    Set.Finite {y : AlgebraicClosure K |
      (X.curve.toAffine.baseChange (AlgebraicClosure K)).Equation x y} :=
  equation_y_finite (X.curve.toAffine.baseChange (AlgebraicClosure K)) x

end LeanFormal.IUT.L1F3.TorsionRootMap
