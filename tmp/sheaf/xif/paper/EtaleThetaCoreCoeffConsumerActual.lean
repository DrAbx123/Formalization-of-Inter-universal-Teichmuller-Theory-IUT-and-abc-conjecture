import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing

namespace LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffConsumerActual

universe u

noncomputable def thetaTermEx (K : Type u) [Field K] (n : Int) :
    HahnSeries HalfInt (HahnSeries Int K) :=
  HahnSeries.single (thetaQExponent n)
    (HahnSeries.single (thetaUExponent n) ((-1 : K) ^ n))

noncomputable def thetaPairTerm (K : Type u) [Field K] (n : Int) :
    HahnSeries HalfInt (HahnSeries Int K) :=
  thetaTermEx K n + thetaTermEx K (-n - 1)

theorem thetaPairTerm_coeff (K : Type u) [Field K] (n : Int) :
    (thetaPairTerm K n).coeff (thetaQExponent n) =
      HahnSeries.single (thetaUExponent n) ((-1 : K) ^ n) +
        HahnSeries.single (thetaUExponent (-n - 1)) ((-1 : K) ^ (-n - 1)) := by
  unfold thetaPairTerm thetaTermEx
  rw [thetaQExponent_neg_succ]
  simp [HahnSeries.coeff_add, HahnSeries.coeff_single]

/-- Core theta coefficient sequence consumed by theta product/Theta-pilot. -/
noncomputable def thetaCoeffAt (K : Type u) [Field K] (n : Int) :
    HahnSeries Int K :=
  (thetaPairTerm K n).coeff (thetaQExponent n)

theorem thetaCoeffAt_eq (K : Type u) [Field K] (n : Int) :
    thetaCoeffAt K n =
      HahnSeries.single (thetaUExponent n) ((-1 : K) ^ n) +
        HahnSeries.single (thetaUExponent (-n - 1)) ((-1 : K) ^ (-n - 1)) :=
  thetaPairTerm_coeff K n

theorem thetaCoeffAt_pair (K : Type u) [Field K] (n : Int) :
    thetaCoeffAt K (-n - 1) = thetaCoeffAt K n := by
  unfold thetaCoeffAt thetaPairTerm thetaTermEx
  rw [thetaQExponent_neg_succ]
  rw [show (-(-n - 1) - 1 : Int) = n by ring]
  rw [add_comm]

#check thetaCoeffAt_eq
#check thetaCoeffAt_pair

end LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffConsumerActual
