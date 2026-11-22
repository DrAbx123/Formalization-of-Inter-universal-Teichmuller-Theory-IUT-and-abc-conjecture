import Mathlib

noncomputable section
set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2568FreshmanActual

instance : Fact (Nat.Prime 613) := ⟨by norm_num⟩

theorem aeval_pow_613 {A : Type*} [CommRing A] [Algebra (ZMod 613) A] [CharP A 613]
    (x : A) (P : (ZMod 613)[X]) :
    (aeval x P) ^ 613 = aeval (x ^ 613) P := by
  rw [aeval_eq_sum_range x, aeval_eq_sum_range (x ^ 613)]
  simp_rw [Algebra.smul_def]
  rw [sum_pow_char]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_pow]
  have hcoeff : (algebraMap (ZMod 613) A (P.coeff i)) ^ 613 =
      algebraMap (ZMod 613) A (P.coeff i) := by
    conv_lhs => rw [← map_pow]
    congr 1
    exact ZMod.pow_card (P.coeff i)
  rw [hcoeff]
  congr 1
  rw [← pow_mul, ← pow_mul, Nat.mul_comm]

#print axioms aeval_pow_613

end LeanFormal.IUT.XiFPaper.S2568FreshmanActual
end