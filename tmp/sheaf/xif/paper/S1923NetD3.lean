import tmp.sheaf.xif.paper.S1923NetD2
import Mathlib.Algebra.Polynomial.Eval.Defs

set_option maxHeartbeats 1000000

universe u
namespace S1923Net
open IsEllipticNet
open scoped nonZeroDivisors
open Polynomial

variable {R : Type u} [CommRing R] (b c d : R)

lemma normEDS_rel_even (m : ℤ) :
    IsEllipticNet.rel (normEDS b c d) (m + 1) (m - 1) 1 0 = 0 := by
  rw [IsEllipticNet.rel_even, normEDS_two, normEDS_one, one_pow, mul_one]
  have h := normEDS_even (b := b) (c := c) (d := d) m
  linear_combination h

lemma normEDS_rel_odd (m : ℤ) :
    IsEllipticNet.rel (normEDS b c d) (m + 1) m 1 0 = 0 := by
  rw [IsEllipticNet.rel_odd, normEDS_one, one_pow, mul_one]
  have h := normEDS_odd (b := b) (c := c) (d := d) m
  linear_combination h

theorem IsEllipticNet.normEDS : IsEllipticNet (normEDS b c d) := by
  let Wp : ℤ → R[X] := _root_.normEDS (X : R[X]) (C c) (C d)
  have hp : IsEllipticNet Wp := by
    dsimp only [Wp]
    exact IsEllipticNet.of_even_odd _ (by simp) (X_mem_nonZeroDivisors_poly R)
      (normEDS_rel_even (b := (X : R[X])) (c := C c) (d := C d))
      (normEDS_rel_odd (b := (X : R[X])) (c := C c) (d := C d))
  have hc : IsEllipticNet (fun n => evalRingHom b (Wp n)) :=
    S1923Net.IsEllipticNet.comp hp (evalRingHom b)
  rw [show (fun n => evalRingHom b (Wp n)) = fun n => normEDS b c d n by
    funext n
    simp [Wp, map_normEDS]] at hc
  exact hc

end S1923Net
