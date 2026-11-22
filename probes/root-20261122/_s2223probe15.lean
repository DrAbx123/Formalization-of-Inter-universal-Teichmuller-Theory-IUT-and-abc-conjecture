
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Int.GCD

noncomputable section

namespace S2223Probe

variable {K : Type*} [Field K]

theorem lthRoot_of_coprime_zpow (l : Nat) (q : K) (hq : q ≠ 0) (x : Kˣ) (m : ℤ)
    (hx : (x : K) ^ l = q ^ m) (hcop : Nat.Coprime l m.natAbs) :
    ∃ s : K, s ^ l = q := by
  have hgcd : Int.gcd (l : ℤ) m = 1 := by
    rw [Int.gcd_def]
    have h : Nat.gcd l m.natAbs = 1 := hcop.gcd_eq_one
    simpa [Int.natAbs_natCast] using h
  let a : ℤ := Int.gcdA (l : ℤ) m
  let b : ℤ := Int.gcdB (l : ℤ) m
  have hbez : (1 : ℤ) = (l : ℤ) * a + m * b := by
    have h := Int.gcd_eq_gcd_ab (l : ℤ) m
    rw [hgcd] at h
    simpa [a, b] using h
  have hx' : (x : K) ^ (l : ℤ) = q ^ m := by
    rw [zpow_natCast]
    exact hx
  refine ⟨q ^ a * (x : K) ^ b, ?_⟩
  rw [mul_pow]
  have h1 : (q ^ a) ^ l = q ^ (a * (l : ℤ)) := by
    rw [← zpow_natCast, ← zpow_mul]
  have h2 : ((x : K) ^ b) ^ l = q ^ (m * b) := by
    rw [← zpow_natCast, ← zpow_mul]
    rw [show b * (l : ℤ) = (l : ℤ) * b by ring]
    rw [zpow_mul, hx']
    rw [← zpow_mul]
  rw [h1, h2, ← zpow_add₀ hq]
  rw [show a * (l : ℤ) + m * b = 1 by linarith [hbez]]
  rw [zpow_one]

end S2223Probe
end
