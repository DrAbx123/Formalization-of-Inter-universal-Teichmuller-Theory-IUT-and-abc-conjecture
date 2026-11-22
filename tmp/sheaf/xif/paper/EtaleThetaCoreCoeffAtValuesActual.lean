import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing

namespace LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffAtValuesActual

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

theorem thetaCoeffAt_zero (K : Type u) [Field K] :
    thetaCoeffAt K 0 =
      HahnSeries.single (thetaUExponent 0) (1 : K) +
        HahnSeries.single (thetaUExponent (-1)) (-1 : K) := by
  simp [thetaCoeffAt, thetaPairTerm, thetaTermEx, thetaQExponent, thetaUExponent]
  norm_num

theorem thetaCoeffAt_one (K : Type u) [Field K] :
    thetaCoeffAt K 1 =
      HahnSeries.single (thetaUExponent 1) (-1 : K) +
        HahnSeries.single (thetaUExponent (-2)) (1 : K) := by
  simp [thetaCoeffAt, thetaPairTerm, thetaTermEx, thetaQExponent, thetaUExponent]
  norm_num

#check thetaCoeffAt_zero
#check thetaCoeffAt_one

end LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffAtValuesActual
