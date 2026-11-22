import Mathlib

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaCoefficientPairingStatementActual

universe u

abbrev HalfInt : Type := Rat

def thetaQExponent (n : Int) : HalfInt := (n : Rat) * ((n : Rat) + 1) / 2

def thetaUExponent (n : Int) : Int := 2 * n + 1

noncomputable def thetaTermPair (K : Type u) [Field K] (n : Int) :
    HahnSeries HalfInt (HahnSeries Int K) :=
  HahnSeries.single (thetaQExponent n)
      (HahnSeries.single (thetaUExponent n) ((-1 : K) ^ n)) +
    HahnSeries.single (thetaQExponent (-n - 1))
      (HahnSeries.single (thetaUExponent (-n - 1)) ((-1 : K) ^ (-n - 1)))

/-- Exact coefficient-pairing statement for a single theta pair. -/
def EtaleThetaCoefficientPairingStatement (K : Type u) [Field K] : Prop :=
  forall n : Int,
    (thetaTermPair K n).coeff (thetaQExponent n) =
      HahnSeries.single (thetaUExponent n) ((-1 : K) ^ n) +
        HahnSeries.single (thetaUExponent (-n - 1)) ((-1 : K) ^ (-n - 1))

theorem etaleThetaCoefficientPairingStatement_actual
    (K : Type u) [Field K] :
    EtaleThetaCoefficientPairingStatement K := by
  intro n
  unfold thetaTermPair
  have hq : thetaQExponent (-n - 1) = thetaQExponent n := by
    unfold thetaQExponent
    rw [show (-n - 1 : Int) = -(n + 1) by ring]
    push_cast
    ring
  rw [hq]
  simp [HahnSeries.coeff_add, HahnSeries.coeff_single]

#check EtaleThetaCoefficientPairingStatement
#check etaleThetaCoefficientPairingStatement_actual

end LeanFormal.IUT.XiFPaper.EtaleThetaCoefficientPairingStatementActual
