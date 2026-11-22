/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic
/-! # Split out the p-part of the torsion order -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1TorsionSplitActual
/-- Write `T = p^m * T0` with `p ∤ T0`; if `T ∣ q^A*(q-1)`, `q = p^f` and `p ∤ (q-1)`,
then `T0 ∣ q-1` and `m ≤ f*A`. -/
theorem torsion_split
    {p T q A : Nat} (hp : p.Prime) (hTpos : 0 < T)
    (hdvd : T ∣ q ^ A * (q - 1))
    (hcop : Nat.Coprime p (q - 1))
    {f : Nat} (hq : q = p ^ f) :
    ∃ m T0 : Nat, T = p ^ m * T0 ∧ Nat.Coprime p T0 ∧
      T0 ∣ q - 1 ∧ m ≤ f * A := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let m := padicValNat p T
  let T0 := T / p ^ m
  have hmpos : m ≤ padicValNat p T := le_rfl
  have hpdvd : p ^ m ∣ T := pow_padicValNat_dvd
  have hT0eq : T = p ^ m * T0 := by
    dsimp [T0]
    exact (Nat.mul_div_cancel' hpdvd).symm
  have hT0dvdT : T0 ∣ T := ⟨p ^ m, by rw [hT0eq, mul_comm]⟩
  have hT0dvd : T0 ∣ q ^ A * (q - 1) := hT0dvdT.trans hdvd
  have hval0 : padicValNat p T0 = 0 := by
    dsimp [T0]
    rw [padicValNat.div_pow hpdvd]
    dsimp [m]
    rw [Nat.sub_self]
  have hnotp : ¬ p ∣ T0 := by
    rcases (padicValNat.eq_zero_iff).mp hval0 with h1 | h0 | hnd
    · exact False.elim (hp.ne_one h1)
    · have hT0zero : T0 = 0 := h0
      have : T = 0 := by rw [hT0eq, hT0zero, mul_zero]
      omega
    · exact hnd
  have hcopT0 : Nat.Coprime T0 (p ^ (f * A)) :=
    hp.coprime_pow_of_not_dvd hnotp
  have hqpow : q ^ A = p ^ (f * A) := by
    rw [hq, ← pow_mul]
  have hT0dvdq1 : T0 ∣ q - 1 := by
    have hT0dvdp : T0 ∣ p ^ (f * A) * (q - 1) := by
      rwa [← hqpow]
    exact hcopT0.dvd_of_dvd_mul_left hT0dvdp
  have hmle : m ≤ f * A := by
    have hpmdvd : p ^ m ∣ p ^ (f * A) := by
      have h1 : p ^ m ∣ p ^ (f * A) * (q - 1) := by
        rw [← hqpow]
        exact hpdvd.trans hdvd
      exact (hcop.pow_left m).dvd_of_dvd_mul_right h1
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hpmdvd
  exact ⟨m, T0, hT0eq, hp.coprime_iff_not_dvd.mpr hnotp, hT0dvdq1, hmle⟩
end LeanFormal.IUT.XiFPaper.Mzk1TorsionSplitActual
end