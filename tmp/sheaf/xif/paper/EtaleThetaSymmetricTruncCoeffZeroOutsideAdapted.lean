import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing

namespace LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncCoeffZeroOutsideAdapted

universe u

noncomputable def thetaTermEx (K : Type u) [Field K] (n : Int) :
    HahnSeries HalfInt (HahnSeries Int K) :=
  HahnSeries.single (thetaQExponent n)
    (HahnSeries.single (thetaUExponent n) ((-1 : K) ^ n))

noncomputable def thetaPairTerm (K : Type u) [Field K] (n : Int) :
    HahnSeries HalfInt (HahnSeries Int K) :=
  thetaTermEx K n + thetaTermEx K (-n - 1)

theorem thetaPairTerm_coeff_ne (K : Type u) [Field K] (n : Int) (e : HalfInt)
    (h : thetaQExponent n ≠ e) :
    (thetaPairTerm K n).coeff e = 0 := by
  unfold thetaPairTerm thetaTermEx
  rw [thetaQExponent_neg_succ]
  simp [thetaTermEx, HahnSeries.coeff_add, HahnSeries.coeff_single, h]

noncomputable def etaleThetaSymmetricTrunc (K : Type u) [Field K] (N : Nat) :
    HahnSeries HalfInt (HahnSeries Int K) :=
  Finset.sum (Finset.range (N + 1)) (fun k : Nat =>
    thetaPairTerm K (k : Int))

/-- Coefficients outside the symmetric theta exponents vanish. -/
theorem etaleThetaSymmetricTrunc_coeff_eq_zero_of_not_image
    (K : Type u) [Field K] (N : Nat) (e : HalfInt)
    (h : forall n : Nat, n <= N -> thetaQExponent (n : Int) ≠ e) :
    (etaleThetaSymmetricTrunc K N).coeff e = 0 := by
  rw [etaleThetaSymmetricTrunc, HahnSeries.coeff_sum]
  apply Finset.sum_eq_zero
  intro k hk
  have hk' : (k : Nat) <= N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  exact thetaPairTerm_coeff_ne K (k : Int) e (h k hk')

#check etaleThetaSymmetricTrunc_coeff_eq_zero_of_not_image

end LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncCoeffZeroOutsideAdapted
