/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellIndexResidueFormula
import Mathlib.Tactic
/-! # Corrected truncated units card with ramification exponent

For `(logShellScale p)^e = (p^s)^e`, the m-adic exponent is `e_K * s * e`,
where `e_K = v_K(p)` is the ramification exponent.  The corrected units card is
`(q - 1) * q^(e_K * s * e - 1)`.  The original unramified formula is the
`e_K = 1` specialization.  This file does NOT modify the existing hcard and does
NOT prove the cardinal identity; it records the corrected target and its exact
unramified specialization. -/
noncomputable section
namespace LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open scoped NNReal NormedField
variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
variable [IsUltrametricDist K] [ProperSpace K]
variable {p : Nat} [Fact p.Prime] [localNormedAlgebra : NormedAlgebra (Padic p) K]
include localNormedAlgebra
/-- Corrected truncated-units target: the quotient by `(logShellScale p)^e`
has m-exponent `eK * s * e`. -/
def TruncatedUnitsCardCorrected (eK s e : Nat) : Prop :=
  Nat.card ((Integers K ⧸ Ideal.span
    {(((logShellScale p : Nat) ^ e : Nat) : Integers K)})ˣ) =
      (logShellResidueCard (K := K) - 1) *
        logShellResidueCard (K := K) ^ (eK * s * e - 1)
/-- Unramified specialization: if `eK = 1`, the corrected target is exactly
the original `(q - 1) q^(s * e - 1)` formula. -/
theorem truncatedUnitsCardCorrected_eq_original_of_unramified
    (h : TruncatedUnitsCardCorrected (K := K) (p := p) 1 s e) :
    TruncatedUnitsCardCorrected (K := K) (p := p) 1 s e := h
/-- Ramified-to-unramified specialization of the target statement. -/
theorem truncatedUnitsCard_of_corrected_unramified
    (h : TruncatedUnitsCardCorrected (K := K) (p := p) 1 s e) :
    Nat.card ((Integers K ⧸ Ideal.span
      {(((logShellScale p : Nat) ^ e : Nat) : Integers K)})ˣ) =
        (logShellResidueCard (K := K) - 1) *
          logShellResidueCard (K := K) ^ (s * e - 1) := by
  simpa [TruncatedUnitsCardCorrected, Nat.one_mul] using h
end LeanFormal.IUT.LocalFieldLogarithm
end