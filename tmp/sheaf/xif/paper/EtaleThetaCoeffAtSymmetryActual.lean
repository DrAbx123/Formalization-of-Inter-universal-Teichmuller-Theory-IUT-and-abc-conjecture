import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing

namespace LeanFormal.IUT.XiFPaper.EtaleThetaCoeffAtSymmetryActual

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

theorem thetaCoeffAt_pair (K : Type u) [Field K] (n : Int) :
    thetaCoeffAt K (-n - 1) = thetaCoeffAt K n := by
  unfold thetaCoeffAt thetaPairTerm thetaTermEx
  rw [thetaQExponent_neg_succ]
  rw [show (-(-n - 1) - 1 : Int) = n by ring]
  rw [add_comm]

theorem thetaCoeffAt_symm (K : Type u) [Field K] (n : Int) :
    thetaCoeffAt K n = thetaCoeffAt K (-n - 1) :=
  (thetaCoeffAt_pair K n).symm

#check thetaCoeffAt_pair
#check thetaCoeffAt_symm

end LeanFormal.IUT.XiFPaper.EtaleThetaCoeffAtSymmetryActual
