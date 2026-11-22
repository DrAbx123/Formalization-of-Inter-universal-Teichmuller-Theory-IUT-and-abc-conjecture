import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic

/-!
# Explicit residue modulus `N(d)` (route 7.2)

For a prime `p` and naturals `d`, `B`, the explicit modulus
`N = d * (B + 2) + 2` makes `(n + 1) * p ^ (1 - N)` small enough that its
`n`-th root is below `p ^ (-B)`, for every `1 ≤ n ≤ d`.

The proof reduces the `ℝ` `rpow` statement to the integer power comparison
`(n + 1) * p ^ (1 - N) < (p ^ (-B)) ^ n` by raising both sides to the power
`1/n` (monotonicity `Real.rpow_lt_rpow`), and closes the latter with
`n + 1 ≤ p ^ n` and `N > n + 1 + B * n`.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1G1UniversalNExplicitActual

private lemma succ_le_prime_pow {p : ℕ} (hp : p.Prime) (n : ℕ) : n + 1 ≤ p ^ n :=
  (Nat.succ_le_of_lt n.lt_two_pow_self).trans (Nat.pow_le_pow_left hp.two_le n)

private lemma rpow_natCast_mul_inv {x : ℝ} (hx : 0 ≤ x) {n : ℕ} (hn : n ≠ 0) :
    (x ^ ((n : ℝ))) ^ ((n : ℝ)⁻¹) = x := by
  rw [← Real.rpow_mul hx, mul_inv_cancel₀ (by exact_mod_cast hn), Real.rpow_one]

private lemma zpow_int_eq_rpow_nat_mul {p : ℝ} (hp : 0 < p) (B n : ℕ) :
    p ^ (-(B * n : ℤ)) = (p ^ (-(B : ℤ))) ^ ((n : ℝ)) := by
  rw [← Real.rpow_intCast p (-(B : ℤ))]
  rw [← Real.rpow_mul (le_of_lt hp)]
  rw [← Real.rpow_intCast p (-(B * n : ℤ))]
  apply congrArg (fun e : ℝ => (p : ℝ) ^ e)
  push_cast
  ring

/-- Route 7.2 explicit residue modulus: `N = d * (B + 2) + 2` works. -/
theorem exists_residueModulus (p d B : Nat) [Fact p.Prime] :
    ∃ N : Nat, 0 < N ∧ ∀ n : Nat, 0 < n → n ≤ d →
      ((n + 1 : Nat) * (p : ℝ) ^ (1 - (N : ℤ))) ^ ((n : ℝ)⁻¹) < (p : ℝ) ^ (-(B : ℤ)) := by
  refine ⟨d * (B + 2) + 2, Nat.succ_pos (d * (B + 2) + 1), ?_⟩
  intro n hn0 hnle
  set N : Nat := d * (B + 2) + 2 with hN
  have hp_prime : p.Prime := Fact.out
  have hp2 : 2 ≤ p := hp_prime.two_le
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp_prime.one_lt
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp_prime.pos
  have hpne : (p : ℝ) ≠ 0 := ne_of_gt hppos
  have hpnonneg : (0 : ℝ) ≤ (p : ℝ) := le_of_lt hppos
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hz : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos.mpr hnR
  have hnne : n ≠ 0 := ne_of_gt hn0
  -- `n + 1 ≤ p ^ n`
  have hle_nat : n + 1 ≤ p ^ n := succ_le_prime_pow hp_prime n
  have hle1 : ((n + 1 : Nat) : ℝ) ≤ (p : ℝ) ^ (n : ℤ) := by
    rw [zpow_natCast]
    exact_mod_cast hle_nat
  -- `N` dominates `n + 1 + B * n`
  have hNgt : n + 1 + B * n < N := by
    rw [hN]
    have h1 : n + 1 + B * n ≤ d + 1 + B * d :=
      Nat.add_le_add (Nat.add_le_add hnle le_rfl) (Nat.mul_le_mul_left B hnle)
    have h2 : d + 1 + B * d < d * (B + 2) + 2 := by
      rw [Nat.mul_add d B 2, Nat.mul_comm d B, Nat.mul_two]
      omega
    exact lt_of_le_of_lt h1 h2
  -- exponent comparison in `ℤ`
  have hexp : (n : ℤ) + (1 - (N : ℤ)) < -(B * n : ℤ) := by
    have hcast : ((n + 1 + B * n : ℕ) : ℤ) < (N : ℤ) := by exact_mod_cast hNgt
    push_cast at hcast
    linarith
  -- the key product bound
  have hA_nonneg : (0 : ℝ) ≤ ((n + 1 : Nat) : ℝ) * (p : ℝ) ^ (1 - (N : ℤ)) :=
    mul_nonneg (by positivity) (le_of_lt (zpow_pos hppos _))
  have hmul : ((n + 1 : Nat) : ℝ) * (p : ℝ) ^ (1 - (N : ℤ))
      ≤ (p : ℝ) ^ (n : ℤ) * (p : ℝ) ^ (1 - (N : ℤ)) :=
    mul_le_mul_of_nonneg_right hle1 (le_of_lt (zpow_pos hppos _))
  have hzadd : (p : ℝ) ^ (n : ℤ) * (p : ℝ) ^ (1 - (N : ℤ))
      = (p : ℝ) ^ ((n : ℤ) + (1 - (N : ℤ))) :=
    (zpow_add₀ hpne (n : ℤ) (1 - (N : ℤ))).symm
  have hlt : (p : ℝ) ^ ((n : ℤ) + (1 - (N : ℤ))) < (p : ℝ) ^ (-(B * n : ℤ)) :=
    zpow_lt_zpow_right₀ hp1 hexp
  have hA_lt : ((n + 1 : Nat) : ℝ) * (p : ℝ) ^ (1 - (N : ℤ))
      < ((p : ℝ) ^ (-(B : ℤ))) ^ ((n : ℝ)) :=
    calc
      ((n + 1 : Nat) : ℝ) * (p : ℝ) ^ (1 - (N : ℤ))
          ≤ (p : ℝ) ^ (n : ℤ) * (p : ℝ) ^ (1 - (N : ℤ)) := hmul
      _ = (p : ℝ) ^ ((n : ℤ) + (1 - (N : ℤ))) := hzadd
      _ < (p : ℝ) ^ (-(B * n : ℤ)) := hlt
      _ = ((p : ℝ) ^ (-(B : ℤ))) ^ ((n : ℝ)) := zpow_int_eq_rpow_nat_mul hppos B n
  calc
    ((n + 1 : Nat) * (p : ℝ) ^ (1 - (N : ℤ))) ^ ((n : ℝ)⁻¹)
        < (((p : ℝ) ^ (-(B : ℤ))) ^ ((n : ℝ))) ^ ((n : ℝ)⁻¹) :=
          Real.rpow_lt_rpow hA_nonneg hA_lt hz
    _ = (p : ℝ) ^ (-(B : ℤ)) :=
          rpow_natCast_mul_inv (le_of_lt (zpow_pos hppos (-(B : ℤ)))) hnne

end LeanFormal.IUT.XiFPaper.Mzk1G1UniversalNExplicitActual

#print axioms LeanFormal.IUT.XiFPaper.Mzk1G1UniversalNExplicitActual.exists_residueModulus
