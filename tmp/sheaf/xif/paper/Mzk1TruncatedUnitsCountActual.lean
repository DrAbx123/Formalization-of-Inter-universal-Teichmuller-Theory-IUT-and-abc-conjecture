/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1TruncatedUnitsCardActual
import tmp.sheaf.xif.paper.Mzk1LocalRingUnitsCardActual
import LeanFormal.IUT.Foundations.LocalFields.IntegralTraceDualTensorInclusion
import LeanFormal.IUT.IUTIV.Estimates.DifferentDegreeUpperBound
import Mathlib.Tactic
/-! # Units of `O/m^N`: (q-1) q^(N-1), via local-ring complement -/
noncomputable section
namespace LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.IntegralTraceDualTensorInclusion
open LeanFormal.IUT.IUTIV.Estimates
open scoped NNReal NormedField
variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
variable [IsUltrametricDist K] [ProperSpace K]
variable {p : Nat} [Fact p.Prime] [localNormedAlgebra : NormedAlgebra (Padic p) K]
variable [FiniteDimensional (Padic p) K]
include localNormedAlgebra
theorem cardQuot_maximalIdeal_eq_residueCard :
    Submodule.cardQuot (IsLocalRing.maximalIdeal (Integers K)) =
      logShellResidueCard (K := K) := by
  rw [Submodule.cardQuot_apply, logShellResidueCard, logShellResidueField]
  rfl
/-- Units of the truncated quotient: `(q-1) q^(N-1)`. -/
theorem card_units_quotient_maximalIdeal_pow (N : Nat) (hN : 1 ≤ N) :
    Nat.card (((Integers K) ⧸ (IsLocalRing.maximalIdeal (Integers K)) ^ N)ˣ) =
      (logShellResidueCard (K := K) - 1) *
        logShellResidueCard (K := K) ^ (N - 1) := by
  classical
  let R := Integers K
  let m : Ideal R := IsLocalRing.maximalIdeal R
  letI : IsDiscreteValuationRing R := integersIsDiscreteValuationRing (p := p) (L := K)
  letI : IsDedekindDomain R := integersIsDedekindDomain (p := p) (L := K)
  letI : IsNoetherianRing R := inferInstance
  haveI : Finite (R ⧸ m) := finite_logShellResidueField (K := K) (p := p)
  letI : Finite (R ⧸ m ^ N) :=
    Ideal.finite_quotient_pow (IsNoetherian.noetherian m) N
  have hmNtop : m ^ N ≠ ⊤ :=
    ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top
      (Ideal.pow_le_self (by omega : N ≠ 0))
  letI : Nontrivial (R ⧸ m ^ N) := Ideal.Quotient.nontrivial_iff.mpr hmNtop
  letI : IsLocalRing (R ⧸ m ^ N) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (m ^ N)) Ideal.Quotient.mk_surjective
  change Nat.card (R ⧸ m ^ N)ˣ =
    (logShellResidueCard (K := K) - 1) * logShellResidueCard (K := K) ^ (N - 1)
  let mQ : Ideal (R ⧸ m ^ N) := m.map (Ideal.Quotient.mk (m ^ N))
  have hmQ : mQ = IsLocalRing.maximalIdeal (R ⧸ m ^ N) :=
    IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have htotal : Nat.card (R ⧸ m ^ N) = logShellResidueCard (K := K) ^ N := by
    rw [← Submodule.cardQuot_apply]
    rw [cardQuot_maximalIdeal_pow (K := K) (p := p)]
    rw [cardQuot_maximalIdeal_eq_residueCard (K := K) (p := p)]
  have hmul := Submodule.card_quotient_mul_card_quotient (M := R) m (m ^ N)
    (Ideal.pow_le_self (by omega : N ≠ 0))
  have hq : Nat.card (R ⧸ m) = logShellResidueCard (K := K) := by
    rw [← Submodule.cardQuot_apply]
    exact cardQuot_maximalIdeal_eq_residueCard (K := K) (p := p)
  have hpow : logShellResidueCard (K := K) ^ N =
      logShellResidueCard (K := K) ^ (N - 1) * logShellResidueCard (K := K) := by
    rw [show N = (N - 1) + 1 by omega]
    exact pow_succ (logShellResidueCard (K := K)) (N - 1)
  have hcardmap : Nat.card mQ = Nat.card (Submodule.map (Submodule.mkQ (m ^ N)) m) := by
    apply Nat.card_congr
    apply Equiv.setCongr
    ext x
    rw [show mQ = Ideal.map (Ideal.Quotient.mk (m ^ N)) m from rfl]
    rw [Ideal.map_eq_submodule_map (Ideal.Quotient.mk (m ^ N)) m]
    rfl
  have hmul' : Nat.card mQ * Nat.card (R ⧸ m) = Nat.card (R ⧸ m ^ N) := by
    rw [hcardmap]
    exact hmul
  have hmQcard : Nat.card mQ = logShellResidueCard (K := K) ^ (N - 1) := by
    have hqpos : 0 < logShellResidueCard (K := K) := logShellResidueCard_pos (K := K) (p := p)
    have hEq : Nat.card mQ * logShellResidueCard (K := K) =
        logShellResidueCard (K := K) ^ (N - 1) * logShellResidueCard (K := K) := by
      rw [← hq, hmul', htotal]
      exact hpow
    exact Nat.eq_of_mul_eq_mul_right hqpos hEq
  have hunits := natCard_units_eq_card_sub_maximalIdeal (R ⧸ m ^ N)
  rw [← hmQ] at hunits
  rw [hunits, htotal, hmQcard]
  rw [hpow]
  rw [mul_comm (logShellResidueCard (K := K) ^ (N - 1)) (logShellResidueCard (K := K))]
  rw [Nat.sub_mul, one_mul]
/-- Primary units card, conditional on the span identification `(p^s) = m^(eK*s)`. -/
theorem truncatedUnitsCardPrimary_of_span_eq
    (hN : 1 ≤ logShellRamificationExponent (K := K) (p := p) *
      logShellScaleExponentFactor (p := p))
    (hspan : Ideal.span {((logShellScale p : Nat) : Integers K)} =
      (IsLocalRing.maximalIdeal (Integers K)) ^
        (logShellRamificationExponent (K := K) (p := p) *
          logShellScaleExponentFactor (p := p))) :
    TruncatedUnitsCardPrimary (K := K) (p := p) := by
  unfold TruncatedUnitsCardPrimary
  rw [hspan]
  exact card_units_quotient_maximalIdeal_pow (K := K) (p := p)
    (logShellRamificationExponent (K := K) (p := p) *
      logShellScaleExponentFactor (p := p)) hN
end LeanFormal.IUT.LocalFieldLogarithm
end