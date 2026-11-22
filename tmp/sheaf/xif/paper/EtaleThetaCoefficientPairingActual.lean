import Mathlib

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaCoefficientPairingActual

universe u

abbrev HalfInt : Type := Rat

def thetaQExponent (n : Int) : HalfInt := (n : Rat) * ((n : Rat) + 1) / 2

def thetaUExponent (n : Int) : Int := 2 * n + 1

theorem thetaQExponent_pair (n : Int) :
    thetaQExponent (-n - 1) = thetaQExponent n := by
  unfold thetaQExponent
  rw [show (-n - 1 : Int) = -(n + 1) by ring]
  push_cast
  ring

theorem thetaUExponent_pair (n : Int) :
    thetaUExponent (-n - 1) = -thetaUExponent n := by
  unfold thetaUExponent
  ring

/-- The two theta terms sharing q-exponent n(n+1)/2. -/
noncomputable def thetaPair (K : Type u) [Field K] (n : Int) :
    HahnSeries HalfInt (HahnSeries Int K) :=
  HahnSeries.single (thetaQExponent n)
      (HahnSeries.single (thetaUExponent n) ((-1 : K) ^ n)) +
    HahnSeries.single (thetaQExponent (-n - 1))
      (HahnSeries.single (thetaUExponent (-n - 1)) ((-1 : K) ^ (-n - 1)))

/-- Exact coefficient pairing for the two theta terms. -/
theorem thetaPair_coeff (K : Type u) [Field K] (n : Int) :
    (thetaPair K n).coeff (thetaQExponent n) =
      HahnSeries.single (thetaUExponent n) ((-1 : K) ^ n) +
        HahnSeries.single (-thetaUExponent n) ((-1 : K) ^ (-n - 1)) := by
  unfold thetaPair
  rw [thetaQExponent_pair, thetaUExponent_pair]
  simp [HahnSeries.coeff_add, HahnSeries.coeff_single]

#check thetaPair_coeff

end LeanFormal.IUT.XiFPaper.EtaleThetaCoefficientPairingActual
