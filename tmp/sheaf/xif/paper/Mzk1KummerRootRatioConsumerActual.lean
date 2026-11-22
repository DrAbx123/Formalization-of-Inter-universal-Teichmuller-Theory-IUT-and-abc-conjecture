/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.IUTII.Kummer.KummerRootRatio

/-! # Kummer root-ratio: consumer laws (natural-scalar ratios) -/

namespace LeanFormal.IUT

namespace KummerRootRatioData

variable {G M U : Type*} [Group G] [CommGroup M] [CommGroup U]
  {value : M}

/-- Scalar multiplication of the ratio index acts by powers of the ratio unit. -/
theorem ratioUnit_natCast
    (D : KummerRootRatioData G M U value)
    (injective_ratioMap : Function.Injective D.ratioMap)
    (g : D.subgroup) (n : Nat) (q : ℚ) :
    D.ratioUnit g ((n : ℚ) * q) = (D.ratioUnit g q) ^ n := by
  induction n with
  | zero =>
      simpa using D.ratioUnit_zero injective_ratioMap g
  | succ k ih =>
      have hcast : ((k + 1 : Nat) : ℚ) * q = (k : ℚ) * q + q := by
        push_cast
        ring
      rw [hcast, D.ratioUnit_add injective_ratioMap g, ih, pow_succ]

/-- The ratio of the reversed index is the inverse ratio unit. -/
theorem ratioUnit_natCast_mul_neg
    (D : KummerRootRatioData G M U value)
    (injective_ratioMap : Function.Injective D.ratioMap)
    (g : D.subgroup) (n : Nat) (q : ℚ) :
    D.ratioUnit g ((n : ℚ) * q) * D.ratioUnit g (-((n : ℚ) * q)) = 1 :=
  by
  have hzero : D.ratioUnit g 0 = 1 := D.ratioUnit_zero injective_ratioMap g
  have hadd := D.ratioUnit_add injective_ratioMap g (-((n : ℚ) * q)) ((n : ℚ) * q)
  rw [neg_add_cancel] at hadd
  rw [hzero] at hadd
  rw [mul_comm] at hadd
  exact hadd.symm

end KummerRootRatioData

end LeanFormal.IUT
