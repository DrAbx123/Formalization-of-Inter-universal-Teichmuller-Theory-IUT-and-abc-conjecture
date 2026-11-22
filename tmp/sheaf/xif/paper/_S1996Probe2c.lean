import Mathlib.NumberTheory.Padics.PadicNumbers

local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

example (b : ℚ_[5]) : b ^ 2 ≠ 5 := by
  intro hb
  have hv := congrArg Padic.valuation hb
  rw [Padic.valuation_pow] at hv
  rw [Padic.valuation_ofNat] at hv
  rw [padicValNat_self] at hv
  norm_num at hv
  omega
