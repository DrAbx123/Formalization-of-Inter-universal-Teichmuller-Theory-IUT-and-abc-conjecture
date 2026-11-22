/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1GeneralLogShellNormCriterionActual
import tmp.sheaf.xif.paper.Mzk1CongruenceUnitsEquivActual
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellSharpBounds
import Mathlib.Tactic
/-! # General congruence units equivalence via the uniformizer norm criterion -/
noncomputable section
namespace LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open scoped NNReal NormedField
variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
variable [IsUltrametricDist K] [ProperSpace K]
variable {p : Nat} [Fact p.Prime] [localNormedAlgebra : NormedAlgebra (Padic p) K]
variable [FiniteDimensional (Padic p) K]
variable [hDVR : IsDiscreteValuationRing (Integers K)]
include localNormedAlgebra hDVR
/-- `addVal` of `logShellScale p` is `s * eK`. -/
theorem addVal_logShellScale :
    IsDiscreteValuationRing.addVal (Integers K)
        ((logShellScale p : Nat) : Integers K) =
      ((logShellScaleExponentFactor (p := p) *
        logShellRamificationExponent (K := K) (p := p) : Nat) : ℕ∞) := by
  rw [logShellScale_eq_prime_pow_factor, Nat.cast_pow]
  rw [IsDiscreteValuationRing.addVal_pow]
  have hpval : IsDiscreteValuationRing.addVal (Integers K) ((p : Nat) : Integers K) =
      (logShellRamificationExponent (K := K) (p := p) : ℕ∞) := by
    simpa [ramifiedPrimeAddVal] using addVal_prime_eq_ramificationExponent (K := K) (p := p)
  rw [hpval, nsmul_eq_mul, ← Nat.cast_mul]
/-- Target of the general primary equivalence. -/
def CongruenceUnitsPrimaryEquivTarget : Prop :=
  Nonempty (((Integers K)ˣ ⧸ logShellCongruenceUnits (K := K) (p := p)) ≃*
    (Integers K ⧸ Ideal.span {((logShellScale p : Nat) : Integers K)})ˣ)
/-- Conditional equivalence: surjective unit map with the correct kernel gives the target. -/
theorem congruenceUnits_equiv_primary_general_of_kernel
    (f : (Integers K)ˣ →*
      (Integers K ⧸ Ideal.span {((logShellScale p : Nat) : Integers K)})ˣ)
    (hsurj : Function.Surjective f)
    (hker : f.ker = logShellCongruenceUnits (K := K) (p := p)) :
    CongruenceUnitsPrimaryEquivTarget (K := K) (p := p) := by
  have hker1 : f.ker = logShellCongruenceUnitsPow (K := K) (p := p) 1 := by
    rw [logShellCongruenceUnitsPow_one]
    exact hker
  refine ⟨?e⟩
  exact (QuotientGroup.quotientMulEquivOfEq
      (logShellCongruenceUnitsPow_one (K := K) (p := p)).symm).trans
    ((QuotientGroup.quotientMulEquivOfEq hker1.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hsurj))
/-- Unconditional general primary equivalence: all p, actual uniformizer pi. -/
theorem congruenceUnits_equiv_primary_general
    (π : Integers K) (hπ : Irreducible π) :
    CongruenceUnitsPrimaryEquivTarget (K := K) (p := p) := by
  classical
  let I : Ideal (Integers K) :=
    Ideal.span {((logShellScale p : Nat) : Integers K)}
  have hIne : I ≠ ⊤ := by
    intro htop
    have hunit : IsUnit ((logShellScale p : Nat) : Integers K) :=
      Ideal.span_singleton_eq_top.mp htop
    have hz := IsDiscreteValuationRing.addVal_eq_zero_of_unit hunit.unit
    rw [IsUnit.unit_spec hunit, addVal_logShellScale (K := K) (p := p)] at hz
    have hpos : ((logShellScaleExponentFactor (p := p) *
        logShellRamificationExponent (K := K) (p := p) : Nat) : ℕ∞) ≠ 0 := by
      exact_mod_cast Nat.mul_ne_zero
        (logShellScaleExponentFactor_pos (p := p)).ne'
        (logShellRamificationExponent_pos (K := K) (p := p)).ne'
    exact hpos hz
  haveI : Nontrivial (Integers K ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hIne
  letI : IsLocalRing (Integers K ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  letI : IsLocalHom (Ideal.Quotient.mk I) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let f : (Integers K)ˣ →* (Integers K ⧸ I)ˣ := Units.map (Ideal.Quotient.mk I)
  have hsurj : Function.Surjective f :=
    IsLocalRing.surjective_units_map_of_local_ringHom (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective inferInstance
  have hker : f.ker = logShellCongruenceUnits (K := K) (p := p) := by
    ext u
    rw [MonoidHom.mem_ker]
    have hmk : f u = 1 ↔ ((u : Integers K) - 1) ∈ I := by
      constructor
      · intro h
        exact (Ideal.Quotient.mk_eq_one_iff_sub_mem (u : Integers K)).mp
          (congrArg Units.val h)
      · intro h
        apply Units.ext
        change (Ideal.Quotient.mk I) (u : Integers K) = 1
        exact (Ideal.Quotient.mk_eq_one_iff_sub_mem (u : Integers K)).mpr h
    have hmemI : ((u : Integers K) - 1) ∈ I ↔
        IsDiscreteValuationRing.addVal (Integers K) ((logShellScale p : Nat) : Integers K) ≤
          IsDiscreteValuationRing.addVal (Integers K) ((u : Integers K) - 1) := by
      rw [show I = Ideal.span {((logShellScale p : Nat) : Integers K)} from rfl,
        Ideal.mem_span_singleton]
      exact (IsDiscreteValuationRing.addVal_le_iff_dvd).symm
    have hnorm := norm_le_norm_logShellScale_iff (K := K) (p := p) π hπ
      ((u : Integers K) - 1)
    have hunit : u ∈ logShellCongruenceUnits (K := K) (p := p) ↔
        ‖(((u : Integers K) : K) - 1)‖ ≤
          ‖(((logShellScale p : Nat)) : K)‖ := by
      unfold logShellCongruenceUnits
      rw [mem_principalUnitsAtClosedRadius_iff]
    rw [hmk, hmemI, addVal_logShellScale (K := K) (p := p)]
    exact (hunit.trans hnorm).symm
  exact congruenceUnits_equiv_primary_general_of_kernel (K := K) (p := p) f hsurj hker
end LeanFormal.IUT.LocalFieldLogarithm
end