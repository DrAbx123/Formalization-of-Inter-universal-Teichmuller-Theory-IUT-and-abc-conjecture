/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1CongruenceUnitsEquivActual
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellSharpBounds
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open scoped NNReal NormedField
variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
variable [IsUltrametricDist K] [ProperSpace K]
variable {p : Nat} [Fact p.Prime] [localNormedAlgebra : NormedAlgebra (Padic p) K]
include localNormedAlgebra
noncomputable def congruenceUnits_equiv_primary_odd
    (hp2 : p ≠ 2) (hpi : Irreducible (p : Integers K)) :
    ((Integers K)ˣ ⧸ logShellCongruenceUnits (K := K) (p := p)) ≃*
      (logShellResidueField (K := K))ˣ := by
  let f : (Integers K)ˣ →* (logShellResidueField (K := K))ˣ :=
    integralUnitToLogShellResidueUnits (K := K)
  have hsurj : Function.Surjective f :=
    integralUnitToLogShellResidueUnits_surjective (K := K)
  have hker : f.ker = logShellCongruenceUnits (K := K) (p := p) :=
    integralUnitToLogShellResidueUnits_ker_eq (K := K) (p := p) hp2 hpi
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hsurj)
/-- Consumer: residue-field congruence equivalence transported to O/(p). -/
noncomputable def congruenceUnits_equiv_primary_odd_quot
    (hp2 : p ≠ 2) (hpi : Irreducible (p : Integers K)) :
    ((Integers K)ˣ ⧸ logShellCongruenceUnits (K := K) (p := p)) ≃*
      (Integers K ⧸ Ideal.span {((p : Nat) : Integers K)})ˣ := by
  letI : IsDiscreteValuationRing (Integers K) :=
    isDiscreteValuationRingIntegers (K := K) (p := p)
  exact (congruenceUnits_equiv_primary_odd (K := K) (p := p) hp2 hpi).trans
    (Units.mapEquiv (Ideal.quotEquivOfEq hpi.maximalIdeal_eq).toMulEquiv)
end LeanFormal.IUT.LocalFieldLogarithm
