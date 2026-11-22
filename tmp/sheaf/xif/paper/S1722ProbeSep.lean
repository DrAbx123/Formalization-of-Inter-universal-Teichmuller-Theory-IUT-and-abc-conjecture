import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Tactic

noncomputable section
open Polynomial

namespace ProbeSep

def P : ℚ[X] :=
  C 463856467968 * X ^ 3 + C 3973952045056 * X ^ 2 +
    C 1991485440000 * X + C 6153500390625

def P' : ℚ[X] :=
  C 1391569403904 * X ^ 2 + C 7947904090112 * X + C 1991485440000

def A : ℚ[X] :=
  C (92045312/3327590340912772265625 : ℚ) * X +
    C (47671697641/269534817613934553515625 : ℚ)

def B : ℚ[X] :=
  C (-92045312/9982771022738316796875 : ℚ) * X ^ 2 +
    C (-22987702883/269534817613934553515625 : ℚ) * X +
    C (-2468003/55631877699504960000 : ℚ)

theorem Bezout_eval {K : Type*} [Field K] [Algebra ℚ K] [CharZero K] (x : K) :
    aeval x A * aeval x P + aeval x B * aeval x P' = 1 := by
  unfold A B P P'
  simp only [aeval_add, aeval_mul, aeval_X, aeval_C, map_pow, map_ofNat]
  simp only [show ∀ q : ℚ, algebraMap ℚ K q = (q : K) from fun q => by
    rw [← map_ratCast (algebraMap ℚ K) q]; rfl]
  ring_nf

theorem Bezout_poly : A * P + B * P' = 1 := by
  have h := Bezout_eval (K := RatFunc ℚ) (RatFunc.X : RatFunc ℚ)
  have hX : (IsScalarTower.toAlgHom ℚ ℚ[X] (RatFunc ℚ)) X = RatFunc.X := by
    change algebraMap ℚ[X] (RatFunc ℚ) X = RatFunc.X
    exact RatFunc.algebraMap_X
  have hmap : ∀ p : ℚ[X],
      Polynomial.eval₂ (algebraMap ℚ (RatFunc ℚ)) (RatFunc.X) p =
        algebraMap ℚ[X] (RatFunc ℚ) p := by
    intro p
    rw [← hX,
      Polynomial.eval₂_algebraMap_X p
        (IsScalarTower.toAlgHom ℚ ℚ[X] (RatFunc ℚ))]
    rfl
  apply IsFractionRing.injective ℚ[X] (RatFunc ℚ)
  simpa [Polynomial.aeval_def, hmap] using h

theorem P_derivative : derivative P = P' := by
  unfold P P'
  simp only [derivative_add, derivative_mul, derivative_pow, derivative_C, derivative_X]
  norm_num
  simp only [← mul_assoc, ← C_mul]
  norm_num

theorem P_separable : P.Separable := by
  rw [separable_def']
  refine ⟨A, B, ?_⟩
  rw [P_derivative]
  exact Bezout_poly

end ProbeSep
