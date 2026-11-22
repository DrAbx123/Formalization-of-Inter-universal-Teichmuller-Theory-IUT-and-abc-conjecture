import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing

namespace LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffAtEvalActual

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

theorem thetaUExponent_ne_neg (n : Int) :
    thetaUExponent n ≠ thetaUExponent (-n - 1) := by
  unfold thetaUExponent
  omega

theorem thetaCoeffAt_coeff_u (K : Type u) [Field K] (n : Int) :
    (thetaCoeffAt K n).coeff (thetaUExponent n) = (-1 : K) ^ n := by
  rw [thetaCoeffAt_eq]
  simp [HahnSeries.coeff_add, HahnSeries.coeff_single, thetaUExponent_ne_neg n]

theorem thetaCoeffAt_coeff_neg_u (K : Type u) [Field K] (n : Int) :
    (thetaCoeffAt K n).coeff (-thetaUExponent n) = (-1 : K) ^ (-n - 1) := by
  rw [thetaCoeffAt_eq]
  have hne : thetaUExponent n ≠ -thetaUExponent n := by
    unfold thetaUExponent
    omega
  have hneg : thetaUExponent (-n - 1) = -thetaUExponent n := by
    unfold thetaUExponent
    ring
  have hne' : -thetaUExponent n ≠ thetaUExponent n := by
    unfold thetaUExponent
    omega
  rw [hneg]
  simp [HahnSeries.coeff_add, HahnSeries.coeff_single, hne, hne']

#check thetaCoeffAt_coeff_u
#check thetaCoeffAt_coeff_neg_u

end LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffAtEvalActual
