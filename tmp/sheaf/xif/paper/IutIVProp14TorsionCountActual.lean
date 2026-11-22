/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic
import Mathlib.GroupTheory.PGroup

/-! # IUT IV Prop 1.4 §3.4: torsion count from congruence quotient -/

noncomputable section
namespace LeanFormal.IUT.LocalFieldLogarithm
theorem torsion_card_eq_of_congruenceCard
    {T C Gamma : Type*} [Group T] [Group C] [AddCommGroup Gamma]
    [Finite T] [Finite C] [Finite Gamma]
    {p q e f s h : Nat} [Fact p.Prime]
    (hdecomp : Nat.card C = Nat.card T * Nat.card Gamma)
    (hC : Nat.card C = (q - 1) * p ^ (f * (e * s - 1)))
    (hGamma : Nat.card Gamma = p ^ h)
    (hq : q = p ^ f)
    (hcop : Nat.Coprime p (q - 1)) :
    ∃ m, Nat.card T = (q - 1) * p ^ m ∧
      h + m = f * (e * s - 1) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hCΓ : Nat.card C = Nat.card T * p ^ h := by rw [hdecomp, hGamma]
  have hEq : Nat.card T * p ^ h = (q - 1) * p ^ (f * (e * s - 1)) := by
    rw [← hCΓ, hC, hq]
  have hdvd : p ^ h ∣ (q - 1) * p ^ (f * (e * s - 1)) := by
    rw [← hEq]
    exact dvd_mul_left (p ^ h) (Nat.card T)
  have hcop' : Nat.Coprime (p ^ h) (q - 1) := by
    simpa using Nat.Coprime.pow h 1 hcop
  have hdvd2 : p ^ h ∣ p ^ (f * (e * s - 1)) := hcop'.dvd_of_dvd_mul_left hdvd
  have hle : h ≤ f * (e * s - 1) :=
    (Nat.pow_dvd_pow_iff_le_right hp1).mp hdvd2
  refine ⟨f * (e * s - 1) - h, ?_, ?_⟩
  · have hpow : p ^ (f * (e * s - 1)) =
        p ^ (f * (e * s - 1) - h) * p ^ h := by
      rw [pow_sub_mul_pow _ hle]
    have hcancel : Nat.card T * p ^ h =
        ((q - 1) * p ^ (f * (e * s - 1) - h)) * p ^ h := by
      rw [hEq, hpow, mul_assoc]
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hp h) hcancel
  · exact Nat.add_sub_of_le hle
end LeanFormal.IUT.LocalFieldLogarithm
