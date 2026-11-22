import Mathlib
import Mathlib.Tactic

noncomputable section
open Polynomial

def Fp : ℚ[X] := C 768 * X ^ 3 + C 2176 * X ^ 2 + C 400 * X + C 625
def Ap : ℚ[X] := C (-3145728/33958225 : ℚ) * X ^ 2 + C (-2876416/6237225 : ℚ) * X + C (-14425/55442 : ℚ)
def Pp : ℚ[X] := C 463856467968 * X ^ 3 + C 3973952045056 * X ^ 2 + C 1991485440000 * X + C 6153500390625
def Q1 : ℚ[X] := C (-(12524124635136 : ℚ)/9515710442487800081671875) * X ^ 3 +
  C (-(79751150567424 : ℚ)/9515710442487800081671875) * X ^ 2 +
  C ((83360885866496 : ℚ)/9515710442487800081671875) * X +
  C ((1012427556339675 : ℚ)/9515710442487800081671875)

example {K : Type*} [Field K] [Algebra ℚ K] [CharZero K] (t : K) :
    aeval (aeval t Ap) Fp = (aeval t Pp) * (aeval t Q1) := by
  unfold Fp Ap Pp Q1
  simp only [aeval_add, aeval_mul, aeval_X, aeval_C, map_pow, map_ofNat]
  simp only [show ∀ q : ℚ, algebraMap ℚ K q = (q : K) from fun q => by
    rw [← map_ratCast (algebraMap ℚ K) q]; rfl]
  ring_nf
  simp only [← Rat.cast_mul, ← Rat.cast_add, ← Rat.cast_sub, ← Rat.cast_pow, ← Rat.cast_div,
    ← Rat.cast_ofNat, ← Rat.cast_natCast, ← Rat.cast_intCast]
  norm_num
