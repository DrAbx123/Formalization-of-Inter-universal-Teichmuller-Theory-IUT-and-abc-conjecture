/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1TruncatedUnitsCardActual
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open scoped NNReal NormedField
variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
variable [IsUltrametricDist K] [ProperSpace K]
variable {p : Nat} [Fact p.Prime] [localNormedAlgebra : NormedAlgebra (Padic p) K]
include localNormedAlgebra
/-- Primary task-127 target: s-congruence group is kernel of unit reduction modulo p^s O. -/
noncomputable def congruenceUnits_equiv_primary
    (f : (Integers K)ˣ →*
      (Integers K ⧸ Ideal.span
        {((logShellScale p : Nat) : Integers K)})ˣ)
    (hsurj : Function.Surjective f)
    (hker : f.ker = logShellCongruenceUnits (K := K) (p := p)) :
    ((Integers K)ˣ ⧸ logShellCongruenceUnits (K := K) (p := p)) ≃*
      (Integers K ⧸ Ideal.span
        {((logShellScale p : Nat) : Integers K)})ˣ :=
  (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hsurj)
/-- Secondary general-e target using power-radius kernel. -/
noncomputable def congruenceUnits_equiv_pow
    (e : Nat)
    (f : (Integers K)ˣ →*
      (Integers K ⧸ Ideal.span
        {(((logShellScale p : Nat) ^ e : Nat) : Integers K)})ˣ)
    (hsurj : Function.Surjective f)
    (hker : f.ker = logShellCongruenceUnitsPow (K := K) (p := p) e) :
    ((Integers K)ˣ ⧸ logShellCongruenceUnitsPow (K := K) (p := p) e) ≃*
      (Integers K ⧸ Ideal.span
        {(((logShellScale p : Nat) ^ e : Nat) : Integers K)})ˣ :=
  (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hsurj)
end LeanFormal.IUT.LocalFieldLogarithm
