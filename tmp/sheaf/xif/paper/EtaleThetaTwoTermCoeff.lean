import Mathlib

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaTwoTermCoeff

universe u

abbrev HalfInt : Type := Rat

def thetaQExponent (n : Int) : HalfInt := (n : Rat) * ((n : Rat) + 1) / 2

def thetaUExponent (n : Int) : Int := 2 * n + 1

theorem thetaQExponent_neg_succ (n : Int) :
    thetaQExponent (-n - 1) = thetaQExponent n := by
  unfold thetaQExponent
  rw [show (-n - 1 : Int) = -(n + 1) by ring]
  push_cast
  ring

/-- The two theta terms that share the q_X-exponent n(n+1)/2. -/
noncomputable def twoTermTheta (K : Type u) [Field K] (n : Int) :
    HahnSeries HalfInt (HahnSeries Int K) :=
  HahnSeries.single (thetaQExponent n)
      (HahnSeries.single (thetaUExponent n) ((-1 : K) ^ n)) +
    HahnSeries.single (thetaQExponent (-n - 1))
      (HahnSeries.single (thetaUExponent (-n - 1)) ((-1 : K) ^ (-n - 1)))

/-- Coefficient pairing of the two theta terms at exponent n(n+1)/2. -/
theorem twoTermTheta_coeff (K : Type u) [Field K] (n : Int) :
    (twoTermTheta K n).coeff (thetaQExponent n) =
      HahnSeries.single (thetaUExponent n) ((-1 : K) ^ n) +
        HahnSeries.single (thetaUExponent (-n - 1)) ((-1 : K) ^ (-n - 1)) := by
  unfold twoTermTheta
  rw [thetaQExponent_neg_succ]
  simp [HahnSeries.coeff_add, HahnSeries.coeff_single]

#check twoTermTheta_coeff

end LeanFormal.IUT.XiFPaper.EtaleThetaTwoTermCoeff
