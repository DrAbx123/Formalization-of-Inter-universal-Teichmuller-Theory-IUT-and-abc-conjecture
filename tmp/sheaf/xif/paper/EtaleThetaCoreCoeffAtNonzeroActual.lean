import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing

namespace LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffAtNonzeroActual

universe u

noncomputable def thetaTermEx (K : Type u) [Field K] (n : Int) :
    HahnSeries HalfInt (HahnSeries Int K) :=
  HahnSeries.single (thetaQExponent n)
    (HahnSeries.single (thetaUExponent n) ((-1 : K) ^ n))

noncomputable def thetaPairTerm (K : Type u) [Field K] (n : Int) :
    HahnSeries HalfInt (HahnSeries Int K) :=
  thetaTermEx K n + thetaTermEx K (-n - 1)

noncomputable def thetaCoeffAt (K : Type u) [Field K] (n : Int) :
    HahnSeries Int K :=
  (thetaPairTerm K n).coeff (thetaQExponent n)

theorem thetaCoeffAt_eq (K : Type u) [Field K] (n : Int) :
    thetaCoeffAt K n =
      HahnSeries.single (thetaUExponent n) ((-1 : K) ^ n) +
        HahnSeries.single (thetaUExponent (-n - 1)) ((-1 : K) ^ (-n - 1)) := by
  unfold thetaCoeffAt thetaPairTerm thetaTermEx
  rw [thetaQExponent_neg_succ]
  simp [HahnSeries.coeff_add, HahnSeries.coeff_single]

theorem thetaCoeffAt_ne_zero (K : Type u) [Field K] (n : Int) :
    thetaCoeffAt K n ≠ 0 := by
  intro h
  have hc := congrArg (fun s : HahnSeries Int K => s.coeff (thetaUExponent n)) h
  rw [thetaCoeffAt_eq K n] at hc
  have hne : thetaUExponent n ≠ thetaUExponent (-n - 1) := by
    unfold thetaUExponent
    omega
  simp [HahnSeries.coeff_add, HahnSeries.coeff_single, hne] at hc
  exact (zpow_ne_zero n (by norm_num : (-1 : K) ≠ 0)) hc

#check thetaCoeffAt_ne_zero

end LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffAtNonzeroActual
