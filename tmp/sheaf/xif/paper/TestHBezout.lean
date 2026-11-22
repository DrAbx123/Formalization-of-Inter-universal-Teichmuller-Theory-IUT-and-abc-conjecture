import Mathlib
import Mathlib.Tactic
noncomputable section
open Polynomial

def H : ℚ[X] := C 463856467968 * X ^ 6 + C 3973952045056 * X ^ 4 + C 1991485440000 * X ^ 2 + C 6153500390625
def H' : ℚ[X] := C 2783138807808 * X ^ 5 + C 15895808180224 * X ^ 3 + C 3982970880000 * X
def Ac : ℚ[X] := C (-82812438839296/8254503789426745701416015625 : ℚ) * X ^ 4 +
      C (-404422570115072/13645200141705436771728515625 : ℚ) * X ^ 2 +
      C (1/6153500390625 : ℚ)
def Bc : ℚ[X] := C (41406219419648/24763511368280237104248046875 : ℚ) * X ^ 5 +
      C (132559251488768/13645200141705436771728515625 : ℚ) * X ^ 3 +
      C (-19117874179/539069635227869107031250 : ℚ) * X

theorem bezout_eval {K : Type*} [Field K] [Algebra ℚ K] [CharZero K] (x : K) :
    aeval x Ac * aeval x H + aeval x Bc * aeval x H' = 1 := by
  unfold Ac Bc H H'
  simp only [aeval_add, aeval_mul, aeval_X, aeval_C, map_pow, map_ofNat]
  simp only [show ∀ q : ℚ, algebraMap ℚ K q = (q : K) from fun q => by
    rw [← map_ratCast (algebraMap ℚ K) q]; rfl]
  ring_nf

example : Ac * H + Bc * H' = 1 := by
  have h := bezout_eval (K := RatFunc ℚ) (RatFunc.X : RatFunc ℚ)
  have hX : (IsScalarTower.toAlgHom ℚ ℚ[X] (RatFunc ℚ)) X = RatFunc.X := by
    change algebraMap ℚ[X] (RatFunc ℚ) X = RatFunc.X
    exact RatFunc.algebraMap_X
  have hmap : ∀ p : ℚ[X], Polynomial.eval₂ (algebraMap ℚ (RatFunc ℚ)) (RatFunc.X) p =
      algebraMap ℚ[X] (RatFunc ℚ) p := by
    intro p
    rw [← hX, Polynomial.eval₂_algebraMap_X p (IsScalarTower.toAlgHom ℚ ℚ[X] (RatFunc ℚ))]
    rfl
  apply IsFractionRing.injective ℚ[X] (RatFunc ℚ)
  simpa [Polynomial.aeval_def, hmap] using h
