/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellSharpBounds
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellIntegerQuotient
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellIndexResidueFormula
import tmp.sheaf.xif.paper.IutIVProp14GroupCountInterfaceActual
import Mathlib.GroupTheory.PGroup
import Mathlib.Tactic

/-! # IUT IV Prop 1.4: actual Gamma is a finite p-group -/

noncomputable section
namespace LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open scoped NNReal NormedField
variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
variable [IsUltrametricDist K] [ProperSpace K]
variable {p : Nat} [Fact p.Prime] [localNormedAlgebra : NormedAlgebra (Padic p) K]
include localNormedAlgebra
theorem integralLogShell_pow_smul_mem_integers
    (z : integralLogShell (K := K) (p := p)) :
    ∃ k : Nat, (p ^ k : Nat) • (z : K) ∈ (Integers K : Set K) := by
  rcases z.property with ⟨u, hu⟩
  obtain ⟨b, hb⟩ := exists_unitLog_range_subset_pow_inv_smul (K := K) (p := p)
  obtain ⟨y, hy, hlog⟩ := Set.mem_smul_set.mp (hb (Set.mem_range_self u))
  refine ⟨b + logShellScaleExponentFactor (p := p), ?_⟩
  have hz : (z : K) = (logShellScale p : K)⁻¹ * unitLog (K := K) u := hu.symm
  have hfac : (logShellScale p : K) = (p : K) ^ logShellScaleExponentFactor (p := p) := by
    rw [logShellScale_eq_prime_pow_factor]
    push_cast
    ring
  rw [hz, ← hlog, hfac]
  rw [nsmul_eq_mul]
  simp only [smul_eq_mul]
  push_cast
  have hp : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  let f := logShellScaleExponentFactor (p := p)
  have h1 : (↑p : K) ^ ((b + f : Nat) : ℤ) * (↑p : K) ^ (-(f : ℤ)) =
      (↑p : K) ^ (b : ℤ) := by
    rw [← zpow_add₀ hp]
    congr 1
    norm_num [Nat.cast_add]
  have hinv : ((↑p : K) ^ logShellScaleExponentFactor (p := p))⁻¹ =
      (↑p : K) ^ (-(f : ℤ)) := by
    rw [zpow_neg, zpow_natCast]
  rw [hinv]
  have h2 : (↑p : K) ^ (b : ℤ) * (↑p : K) ^ (-(b : ℤ)) = 1 := by
    rw [← zpow_add₀ hp]
    simp
  have hcalc :
      (↑p : K) ^ (b + f) *
          ((↑p : K) ^ (-(f : ℤ)) * ((↑p : K) ^ (-(b : ℤ)) * y)) = y := by
    rw [← zpow_natCast]
    calc
      (↑p : K) ^ ((b + f : Nat) : ℤ) *
          ((↑p : K) ^ (-(f : ℤ)) * ((↑p : K) ^ (-(b : ℤ)) * y))
          = ((↑p : K) ^ ((b + f : Nat) : ℤ) * (↑p : K) ^ (-(f : ℤ))) *
              ((↑p : K) ^ (-(b : ℤ)) * y) := by ring
      _ = (↑p : K) ^ (b : ℤ) * ((↑p : K) ^ (-(b : ℤ)) * y) := by rw [h1]
      _ = ((↑p : K) ^ (b : ℤ) * (↑p : K) ^ (-(b : ℤ))) * y := by ring
      _ = 1 * y := by rw [h2]
      _ = y := by rw [one_mul]
  rw [hcalc]
  exact hy

theorem isPGroup_logShellIntegerQuotient :
    IsPGroup p (Multiplicative (LogShellIntegerQuotient (K := K) (p := p))) := by
  intro g
  let gamma : LogShellIntegerQuotient (K := K) (p := p) := g.toAdd
  have hg : (Multiplicative.ofAdd gamma) = g := rfl
  rw [← hg]
  induction gamma using Quotient.inductionOn with
  | h z =>
    obtain ⟨k, hk⟩ := integralLogShell_pow_smul_mem_integers (K := K) (p := p) z
    refine ⟨k, ?_⟩
    change ((Multiplicative.ofAdd (Quot.mk (QuotientAddGroup.leftRel
      (logShellIntegerSubgroup (K := K) (p := p))) z) :
        Multiplicative (LogShellIntegerQuotient (K := K) (p := p))) ^ (p ^ k)) =
        Multiplicative.ofAdd (0 : LogShellIntegerQuotient (K := K) (p := p))
    rw [← ofAdd_nsmul]
    congr 1
    change QuotientAddGroup.mk ((p ^ k) • z) = 0
    have hmem : ((p ^ k) • z : integralLogShell (K := K) (p := p)) ∈
        logShellIntegerSubgroup (K := K) (p := p) := by
      rw [mem_logShellIntegerSubgroup_iff]
      simpa [nsmul_eq_mul] using hk
    rw [QuotientAddGroup.eq_zero_iff]
    exact hmem

theorem card_gamma_eq_pow_actual :
    ∃ h : Nat, Nat.card (LogShellIntegerQuotient (K := K) (p := p)) = p ^ h := by
  letI := finite_logShellIntegerQuotient (K := K) (p := p)
  exact card_gamma_eq_pow (K := K) (p := p)
    (isPGroup_logShellIntegerQuotient (K := K) (p := p))
end LeanFormal.IUT.LocalFieldLogarithm
