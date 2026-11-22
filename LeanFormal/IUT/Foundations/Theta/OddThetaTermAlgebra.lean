import LeanFormal.IUT.Foundations.Theta.OddTheta

set_option linter.unusedSectionVars false
noncomputable section

/-!
# Pure term algebra for the theta shift law

This scratch file isolates the sign/exponent/term identities used by the theta shift
law `Theta(q, r^a U) = (-1)^a r^(-a^2) U^(-2a) Theta(q, U)` for `r^2 = q`.
It is deliberately independent of `tsum`, summability and reindexing: every
statement here is a pointwise algebraic identity about `oddThetaTerm`, so the
analytic shift-law proof can consume it without touching the convergence layer.

All declarations are stated for the frozen `OddTheta` setup
(`NormedField L` + ultrametric + complete) so that `oddThetaSign`,
`oddThetaExponent` and `oddThetaTerm` are exactly the production definitions;
the proofs themselves only use field/zpow algebra.
-/

namespace LeanFormal.IUT.Foundations.Theta

universe u

variable {L : Type u} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]

/-! ## 1. Parity of the exponent numerator -/

/-- `2` divides `n * (n + 1)` for every integer `n`. -/
theorem two_dvd_mul_succ_self (n : ℤ) : (2 : ℤ) ∣ n * (n + 1) := by
  rcases Int.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact ⟨k * (2 * k + 1), by rw [hk]; ring⟩
  · exact ⟨(2 * k + 1) * (k + 1), by rw [hk]; ring⟩

/-- The defining identity `2 * n(n+1)/2 = n(n+1)` for the integer theta exponent. -/
theorem two_mul_oddThetaExponent_coe (n : ℤ) :
    2 * (oddThetaExponent n : ℤ) = n * (n + 1) := by
  rw [oddThetaExponent_coe, Int.mul_ediv_cancel']
  exact two_dvd_mul_succ_self n

/-- The cocycle identity for the quadratic exponent under the index shift `n -> n + a`. -/
theorem two_mul_oddThetaExponent_add (n a : ℤ) :
    2 * (oddThetaExponent (n + a) : ℤ) =
      2 * (oddThetaExponent n : ℤ) + a * (2 * n + a + 1) := by
  rw [two_mul_oddThetaExponent_coe, two_mul_oddThetaExponent_coe]
  ring

/-! ## 2. The sign factor `(-1)^n` -/

/-- The sign factor squares to one. -/
theorem oddThetaSign_sq (a : ℤ) :
    oddThetaSign (L := L) a * oddThetaSign a = 1 := by
  rw [oddThetaSign_eq_pow, ← zpow_add₀ (by norm_num : (-1 : L) ≠ 0)]
  rw [show a + a = 2 * a by ring, zpow_mul]
  norm_num

/-- Splitting the sign under a shift: `(-1)^n = (-1)^(n+a) * (-1)^a`. -/
theorem oddThetaSign_eq_shift (n a : ℤ) :
    oddThetaSign (L := L) n = oddThetaSign (n + a) * oddThetaSign a := by
  calc oddThetaSign (L := L) n = oddThetaSign n * 1 := (mul_one _).symm
    _ = oddThetaSign n * (oddThetaSign a * oddThetaSign a) := by rw [oddThetaSign_sq]
    _ = (oddThetaSign n * oddThetaSign a) * oddThetaSign a := by ring
    _ = oddThetaSign (n + a) * oddThetaSign a := by rw [← oddThetaSign_add n a]

/-! ## 3. Converting `q`-powers to `r`-powers (`r^2 = q`) -/

/-- For `r^2 = q`, a natural `q`-power is the corresponding even `r`-power. -/
theorem q_pow_eq_root_zpow (q r : L) (hr : r ^ 2 = q) (k : ℕ) :
    q ^ k = r ^ (2 * (k : ℤ)) := by
  rw [← hr, ← pow_mul]
  conv_lhs => rw [← zpow_natCast]
  congr 1

/-! ## 4. The pointwise term identity of the theta shift law -/

/-- The shift coefficient `(-1)^a * r^(-a^2) * U^(-2a)` appearing in the shift law. -/
def oddThetaShiftCoefficient (r U : L) (a : ℤ) : L :=
  oddThetaSign (L := L) a * r ^ (-(a ^ 2)) * U ^ (-(2 * a))

/-- **Pure term identity of the theta shift law.** For `r^2 = q`, `r ≠ 0` and
`U ≠ 0`,
`oddThetaTerm q (r^a * U) n = (-1)^a * r^(-a^2) * U^(-2a) * oddThetaTerm q U (n + a)`.
This is the pointwise algebraic input for `oddTheta(q, r^a U) = ... * oddTheta(q, U)`;
no summability or `tsum` is used. -/
theorem oddThetaTerm_shift (q r U : L) (hr : r ^ 2 = q) (hr0 : r ≠ 0)
    (hU : U ≠ 0) (a n : ℤ) :
    oddThetaTerm q (r ^ a * U) n =
      oddThetaShiftCoefficient r U a * oddThetaTerm q U (n + a) := by
  have hcombineR : ∀ x y : ℤ, r ^ x * r ^ y = r ^ (x + y) := by
    intro x y
    rw [← zpow_add₀ hr0]
  have hcombineU : U ^ (-(2 * a)) * U ^ (2 * (n + a) + 1) = U ^ (2 * n + 1) := by
    rw [← zpow_add₀ hU]
    congr 1
    ring
  have hexp : 2 * (oddThetaExponent n : ℤ) + a * (2 * n + 1)
      = -(a ^ 2) + 2 * (oddThetaExponent (n + a) : ℤ) := by
    have h := two_mul_oddThetaExponent_add n a
    linarith
  have hUn : (r ^ a * U) ^ (2 * n + 1) =
      r ^ (a * (2 * n + 1)) * U ^ (2 * n + 1) := by
    rw [mul_zpow, zpow_mul]
  calc oddThetaTerm q (r ^ a * U) n
      = oddThetaSign n * r ^ (2 * (oddThetaExponent n : ℤ)) *
          (r ^ (a * (2 * n + 1)) * U ^ (2 * n + 1)) := by
        rw [oddThetaTerm, hUn, q_pow_eq_root_zpow q r hr (oddThetaExponent n)]
    _ = (oddThetaSign (n + a) * oddThetaSign a) *
          r ^ (2 * (oddThetaExponent n : ℤ)) *
          (r ^ (a * (2 * n + 1)) * U ^ (2 * n + 1)) := by
        rw [oddThetaSign_eq_shift n a]
    _ = oddThetaSign a * oddThetaSign (n + a) *
          r ^ (2 * (oddThetaExponent n : ℤ) + a * (2 * n + 1)) *
          U ^ (2 * n + 1) := by
        rw [← hcombineR]
        ring
    _ = oddThetaSign a * oddThetaSign (n + a) *
          r ^ (-(a ^ 2) + 2 * (oddThetaExponent (n + a) : ℤ)) *
          U ^ (2 * n + 1) := by
        rw [hexp]
    _ = oddThetaSign a * r ^ (-(a ^ 2)) * U ^ (-(2 * a)) *
          (oddThetaSign (n + a) *
            r ^ (2 * (oddThetaExponent (n + a) : ℤ)) *
            U ^ (2 * (n + a) + 1)) := by
        rw [← hcombineR (-(a ^ 2)) (2 * (oddThetaExponent (n + a) : ℤ)),
          ← hcombineU]
        ring
    _ = oddThetaShiftCoefficient r U a * oddThetaTerm q U (n + a) := by
        rw [oddThetaShiftCoefficient, oddThetaTerm,
          q_pow_eq_root_zpow q r hr (oddThetaExponent (n + a))]

/-- The shift identity in the inverse orientation, convenient when one starts
from a shifted index: `oddThetaTerm q U (n + a)` recovers the unshifted term. -/
theorem oddThetaTerm_shift_inv (q r U : L) (hr : r ^ 2 = q) (hr0 : r ≠ 0)
    (hU : U ≠ 0) (a n : ℤ) :
    oddThetaTerm q U (n + a) =
      (oddThetaShiftCoefficient r U a)⁻¹ * oddThetaTerm q (r ^ a * U) n := by
  have h := oddThetaTerm_shift q r U hr hr0 hU a n
  have hcoeff : oddThetaShiftCoefficient r U a ≠ 0 := by
    unfold oddThetaShiftCoefficient
    have hsign : oddThetaSign (L := L) a ≠ 0 := by
      rw [oddThetaSign_eq_pow]
      exact zpow_ne_zero _ (by norm_num : (-1 : L) ≠ 0)
    exact mul_ne_zero (mul_ne_zero hsign (zpow_ne_zero _ hr0)) (zpow_ne_zero _ hU)
  rw [h, ← mul_assoc, inv_mul_cancel₀ hcoeff, one_mul]

end LeanFormal.IUT.Foundations.Theta