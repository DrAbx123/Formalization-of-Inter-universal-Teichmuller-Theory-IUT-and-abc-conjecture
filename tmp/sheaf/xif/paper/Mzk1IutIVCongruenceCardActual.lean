/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.IutIVProp14GroupCountActual
import tmp.sheaf.xif.paper.Mzk1TruncatedUnitsPrimaryActual
import tmp.sheaf.xif.paper.Mzk1CongruenceUnitsEquivGeneralActual
import LeanFormal.IUT.Foundations.LocalFields.IntegralTraceDualTensorInclusion
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellSharpBounds
import Mathlib.Tactic
/-! # Connect primary units count + congruence equivalence to Prop 1.4 input -/
noncomputable section
namespace LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.IntegralTraceDualTensorInclusion
open scoped NNReal NormedField
variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
variable [IsUltrametricDist K] [ProperSpace K]
variable {p : Nat} [Fact p.Prime] [localNormedAlgebra : NormedAlgebra (Padic p) K]
variable [FiniteDimensional (Padic p) K]
include localNormedAlgebra
/-- Congruence quotient card from the primary units count and the units equivalence. -/
theorem congruenceQuotient_card_actual
    (e : Nat) (he : e = logShellRamificationExponent (K := K) (p := p))
    (eEquiv : ((Integers K)ˣ ⧸ logShellCongruenceUnits (K := K) (p := p)) ≃*
      (Integers K ⧸ Ideal.span {((logShellScale p : Nat) : Integers K)})ˣ) :
    Nat.card ((Integers K)ˣ ⧸ logShellCongruenceUnits (K := K) (p := p)) =
      logShellResidueCard (K := K) ^
          (e * logShellScaleExponentFactor (p := p) - 1) *
        (logShellResidueCard (K := K) - 1) := by
  have hcard := Nat.card_congr eEquiv.toEquiv
  rw [hcard]
  have hp := truncatedUnitsCardPrimary (K := K) (p := p)
  unfold TruncatedUnitsCardPrimary at hp
  rw [hp]
  rw [he]
  rw [Nat.mul_comm (logShellResidueCard (K := K) - 1)
    (logShellResidueCard (K := K) ^
      (logShellRamificationExponent (K := K) (p := p) *
        logShellScaleExponentFactor (p := p) - 1))]
/-- The full Prop 1.4 cardinal input, conditional on the congruence units
equivalence and the inertia-degree identity `q = p^f`. -/
theorem congruenceQuotientCardinalityInput_of_equiv
    {e f : Nat}
    (he : e = logShellRamificationExponent (K := K) (p := p))
    (hf : logShellResidueCard (K := K) = p ^ f)
    (eEquiv : ((Integers K)ˣ ⧸ logShellCongruenceUnits (K := K) (p := p)) ≃*
      (Integers K ⧸ Ideal.span {((logShellScale p : Nat) : Integers K)})ˣ) :
    CongruenceQuotientCardinalityInput (K := K) (p := p) e f where
  one_le_e := by
    rw [he]
    exact Nat.succ_le_of_lt (logShellRamificationExponent_pos (K := K) (p := p))
  residueCard_eq_prime_pow := hf
  congruenceQuotient_card := congruenceQuotient_card_actual (K := K) (p := p) e he eEquiv

/-- Existence form: the residue-card equality `q = p^f` is the existing
`logShellResidueCard_eq_prime_pow`; only the units equivalence remains. -/
theorem congruenceQuotientCardinalityInput_exists_of_equiv
    (e : Nat)
    (he : e = logShellRamificationExponent (K := K) (p := p))
    (eEquiv : ((Integers K)ˣ ⧸ logShellCongruenceUnits (K := K) (p := p)) ≃*
      (Integers K ⧸ Ideal.span {((logShellScale p : Nat) : Integers K)})ˣ) :
    ∃ f : Nat, CongruenceQuotientCardinalityInput (K := K) (p := p) e f := by
  obtain ⟨f, _hfpos, hq⟩ := logShellResidueCard_eq_prime_pow (K := K) (p := p)
  exact ⟨f, congruenceQuotientCardinalityInput_of_equiv (K := K) (p := p)
    he hq eEquiv⟩

theorem logShellQFECardinalityHypothesis_exists_of_equiv
    (e : Nat)
    (he : e = logShellRamificationExponent (K := K) (p := p))
    (eEquiv : ((Integers K)ˣ ⧸ logShellCongruenceUnits (K := K) (p := p)) ≃*
      (Integers K ⧸ Ideal.span {((logShellScale p : Nat) : Integers K)})ˣ) :
    ∃ f : Nat, LogShellQFECardinalityHypothesis (K := K) (p := p) e f := by
  obtain ⟨f, hf⟩ := congruenceQuotientCardinalityInput_exists_of_equiv (K := K) (p := p)
    e he eEquiv
  exact ⟨f, logShellQFECardinalityHypothesis_actual (K := K) (p := p) hf⟩

/-- Unconditional Prop 1.4 cardinal input, using the general eEquiv. -/
theorem congruenceQuotientCardinalityInput_exists_actual
    (e : Nat) (he : e = logShellRamificationExponent (K := K) (p := p)) :
    ∃ f : Nat, CongruenceQuotientCardinalityInput (K := K) (p := p) e f := by
  letI : IsDiscreteValuationRing (Integers K) :=
    isDiscreteValuationRingIntegers (K := K) (p := p)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (Integers K)
  obtain ⟨eEquiv⟩ := congruenceUnits_equiv_primary_general (K := K) (p := p) π hπ
  obtain ⟨f, _hfpos, hq⟩ := logShellResidueCard_eq_prime_pow (K := K) (p := p)
  exact ⟨f, congruenceQuotientCardinalityInput_of_equiv (K := K) (p := p)
    he hq eEquiv⟩

theorem logShellQFECardinalityHypothesis_exists_actual
    (e : Nat) (he : e = logShellRamificationExponent (K := K) (p := p)) :
    ∃ f : Nat, LogShellQFECardinalityHypothesis (K := K) (p := p) e f := by
  obtain ⟨f, hf⟩ := congruenceQuotientCardinalityInput_exists_actual (K := K) (p := p) e he
  exact ⟨f, logShellQFECardinalityHypothesis_actual (K := K) (p := p) hf⟩

/-- Specialized to the actual ramification exponent `e = eK`. -/
theorem logShellQFECardinalityHypothesis_exists_ramification :
    ∃ f : Nat, LogShellQFECardinalityHypothesis (K := K) (p := p)
      (logShellRamificationExponent (K := K) (p := p)) f :=
  logShellQFECardinalityHypothesis_exists_actual (K := K) (p := p) _ rfl

/-- Cor 3.12 local index corollary: the QFE index formula at `e = eK`. -/
theorem exists_logShellIntegerIndex_eq_residueCard :
    ∃ f : Nat, logShellIntegerIndex (K := K) (p := p) =
      logShellResidueCard (K := K) ^
          (logShellRamificationExponent (K := K) (p := p) *
            logShellScaleExponentFactor (p := p) - 1) *
        (logShellResidueCard (K := K) - 1) /
      Nat.card (CommGroup.torsion (Integers K)ˣ) := by
  obtain ⟨f, h⟩ := logShellQFECardinalityHypothesis_exists_ramification (K := K) (p := p)
  exact ⟨f, logShellIntegerIndex_eq_residueCard_pow_mul_sub_one_div_torsion_of_qfe
    (K := K) (p := p) h⟩

/-- If the torsion-unit order is the full residue-unit count `q-1`, the QFE index
is the pure residue power required by Cor 3.12 condition (1). -/
theorem logShellIntegerIndex_eq_residueCard_pow_of_torsion_eq_sub_one
    (hT : Nat.card (CommGroup.torsion (Integers K)ˣ) =
      logShellResidueCard (K := K) - 1) :
    logShellIntegerIndex (K := K) (p := p) =
      logShellResidueCard (K := K) ^
        (logShellRamificationExponent (K := K) (p := p) *
          logShellScaleExponentFactor (p := p) - 1) := by
  obtain ⟨f, hqfe⟩ := logShellQFECardinalityHypothesis_exists_ramification (K := K) (p := p)
  have hqpos : 0 < logShellResidueCard (K := K) - 1 :=
    Nat.sub_pos_of_lt (one_lt_logShellResidueCard (K := K) (p := p))
  rw [logShellIntegerIndex_eq_residueCard_pow_mul_div_of_torsion_dvd_sub_one
    (K := K) (p := p) hqfe]
  · rw [hT, Nat.div_self hqpos, mul_one]
  · exact ⟨1, by rw [hT, mul_one]⟩
end LeanFormal.IUT.LocalFieldLogarithm
end