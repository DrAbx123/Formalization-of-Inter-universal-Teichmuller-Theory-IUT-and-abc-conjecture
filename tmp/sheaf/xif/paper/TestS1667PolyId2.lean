import Mathlib
import Mathlib.Tactic

noncomputable section
open Polynomial

def Gp : ℚ[X] := C (1 : ℚ) * X ^ 3 + C (61/64 : ℚ) * X ^ 2 - C (125/64 : ℚ) * X
def Ap : ℚ[X] := C (-3145728/33958225 : ℚ) * X ^ 2 + C (-2876416/6237225 : ℚ) * X + C (-14425/55442 : ℚ)
def Pp : ℚ[X] := C 463856467968 * X ^ 3 + C 3973952045056 * X ^ 2 + C 1991485440000 * X + C 6153500390625
def Q2 : ℚ[X] := C (-(12524124635136 : ℚ)/7308065619830630462724000000) * X ^ 3 +
  C (-(79751150567424 : ℚ)/7308065619830630462724000000) * X ^ 2 +
  C (-(170840063183104 : ℚ)/7308065619830630462724000000) * X +
  C ((659223575628975 : ℚ)/7308065619830630462724000000)

example {K : Type*} [Field K] [Algebra ℚ K] [CharZero K] (t : K) :
    aeval (aeval t Ap) Gp - t = (aeval t Pp) * (aeval t Q2) := by
  unfold Gp Ap Pp Q2
  simp only [aeval_add, aeval_sub, aeval_mul, aeval_X, aeval_C, map_pow, map_ofNat]
  simp only [show ∀ q : ℚ, algebraMap ℚ K q = (q : K) from fun q => by
    rw [← map_ratCast (algebraMap ℚ K) q]; rfl]
  ring_nf
