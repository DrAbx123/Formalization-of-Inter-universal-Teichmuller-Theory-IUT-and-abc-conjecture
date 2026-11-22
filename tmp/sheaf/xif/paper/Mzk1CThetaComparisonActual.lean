import LeanFormal.IUT.Foundations.Theta.OddThetaShift
import LeanFormal.IUT.Foundations.Theta.OddThetaNormalization

/-!
# Route 3 C-Theta: actual multiplicative-shift theta ratio and mu2l phases

This file works with the actual analytic odd theta series
`LeanFormal.IUT.Foundations.Theta.oddTheta` and its proved EtTh Proposition
1.4(ii) shift law, `oddTheta_shift`. It proves only the constructible
multiplicative-shift analog of the auxiliary ratio (C7):

  theta(r^a U) * theta(r^(-a) U) = (r^(-(a^2)))^2 * theta(U)^2.

It also records the elementary fact that independent mu2l phase factors die
after taking a 2l-th power. It does NOT construct a line bundle, a theta
section on the elliptic curve, or the general point translation
theta(Z + P); those remain exact gaps (see coord/ROUTE3-CTHETA.md).
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1CThetaComparisonActual

open LeanFormal.IUT.Foundations.Theta

variable {L : Type*} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]

/-- Signs at opposite integer shifts multiply to one. -/
theorem oddThetaSign_mul_neg (a : Int) :
    oddThetaSign (L := L) a * oddThetaSign (L := L) (-a) = 1 := by
  rw [oddThetaSign_eq_pow, oddThetaSign_eq_pow,
    ← zpow_add₀ (by norm_num : (-1 : L) ≠ 0)]
  rw [show a + -a = 0 by ring]
  norm_num

/-- Shift-product identity with the sign factor kept explicit. -/
theorem oddTheta_shiftProductSigned
    (q r U : L) (hr : r ^ 2 = q) (hr0 : r ≠ 0) (hU : U ≠ 0)
    (hq : ‖q‖ < 1) (a : Int) :
    oddTheta q (r ^ a * U) * oddTheta q (r ^ (-a) * U) =
      (oddThetaSign (L := L) a * oddThetaSign (L := L) (-a)) *
        (r ^ (-(a ^ 2))) ^ 2 * (oddTheta q U) ^ 2 := by
  rw [oddTheta_shift q r U hr hr0 hU hq a,
    oddTheta_shift q r U hr hr0 hU hq (-a)]
  rw [show (-a) ^ 2 = a ^ 2 by ring]
  rw [show 2 * (-a) = -(2 * a) by ring]
  simp only [neg_neg]
  have hpow : U ^ (-(2 * a)) * U ^ (2 * a) = 1 := by
    rw [← zpow_add₀ hU]
    rw [show -(2 * a) + 2 * a = 0 by ring]
    simp
  calc
    (oddThetaSign (L := L) a * r ^ (-(a ^ 2)) * U ^ (-(2 * a)) *
        oddTheta q U) *
      (oddThetaSign (L := L) (-a) * r ^ (-(a ^ 2)) * U ^ (2 * a) *
        oddTheta q U) =
    (oddThetaSign (L := L) a * oddThetaSign (L := L) (-a)) *
      (r ^ (-(a ^ 2)) * r ^ (-(a ^ 2))) *
      (U ^ (-(2 * a)) * U ^ (2 * a)) *
      (oddTheta q U * oddTheta q U) := by ring
    _ = (oddThetaSign (L := L) a * oddThetaSign (L := L) (-a)) *
          (r ^ (-(a ^ 2))) ^ 2 * (oddTheta q U) ^ 2 := by
      rw [hpow]; ring

/-- The actual odd-theta shift-product identity at opposite integer shifts.
This is the multiplicatively shifted version of (C7); the factor
(r^(-(a^2)))^2 is independent of U, and the U-period factors cancel exactly. -/
theorem oddTheta_shiftProduct
    (q r U : L) (hr : r ^ 2 = q) (hr0 : r ≠ 0) (hU : U ≠ 0)
    (hq : ‖q‖ < 1) (a : Int) :
    oddTheta q (r ^ a * U) * oddTheta q (r ^ (-a) * U) =
      (r ^ (-(a ^ 2))) ^ 2 * (oddTheta q U) ^ 2 := by
  rw [oddTheta_shiftProductSigned q r U hr hr0 hU hq a,
    oddThetaSign_mul_neg (L := L) a]
  ring

/-- Ratio form of the same identity, conditional on nonvanishing at U. -/
theorem oddTheta_shiftRatio
    (q r U : L) (hr : r ^ 2 = q) (hr0 : r ≠ 0) (hU : U ≠ 0)
    (hq : ‖q‖ < 1) (hTheta : oddTheta q U ≠ 0) (a : Int) :
    oddTheta q (r ^ a * U) * oddTheta q (r ^ (-a) * U) /
        (oddTheta q U) ^ 2 = (r ^ (-(a ^ 2))) ^ 2 := by
  rw [oddTheta_shiftProduct q r U hr hr0 hU hq a]
  field_simp [hTheta]

/-- Independent mu2l phase factors: if each phase has order dividing 2l, then
the product of arbitrary e_i-th powers is killed by the 2l-th power. This is
the elementary reason a 2l-th power is phase-independent; it does not assert
that this is the correct target normalization. -/
theorem independent_mu2l_phase_pow_twoL
    {M : Type*} [CommMonoid M] {ι : Type*} [Fintype ι]
    (l : Nat) (zeta : ι -> M) (hzeta : ∀ i, zeta i ^ (2 * l) = 1)
    (e : ι -> Nat) :
    (∏ i, zeta i ^ e i) ^ (2 * l) = 1 := by
  rw [← Finset.prod_pow]
  refine Finset.prod_eq_one ?_
  intro i _
  rw [← pow_mul, mul_comm (e i) (2 * l), pow_mul, hzeta i, one_pow]

#print axioms oddTheta_shiftProduct
#print axioms oddTheta_shiftRatio
#print axioms independent_mu2l_phase_pow_twoL

end LeanFormal.IUT.XiFPaper.Mzk1CThetaComparisonActual
