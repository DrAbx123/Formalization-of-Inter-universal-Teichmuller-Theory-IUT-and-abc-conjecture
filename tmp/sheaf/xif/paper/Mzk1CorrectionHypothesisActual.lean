/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1IutIVCongruenceCardActual
import tmp.sheaf.xif.paper.Mzk1TruncatedUnitsPrimaryActual
import Mathlib.Tactic
/-! # Correction form of the residue-power hypothesis from the QFE quotient -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1CorrectionHypothesisActual
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open scoped NNReal NormedField
variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
variable [IsUltrametricDist K] [ProperSpace K]
variable {p : Nat} [Fact p.Prime] [localNormedAlgebra : NormedAlgebra (Padic p) K]
variable [FiniteDimensional (Padic p) K]
include localNormedAlgebra
/-- From the QFE quotient card and `#T ∣ q-1`, the correction hypothesis with
`a = eK*s-1` and `c = (q-1)/#T` holds. -/
theorem correctionHypothesis_of_div
    (hdiv : Nat.card (CommGroup.torsion (Integers K)ˣ) ∣
      logShellResidueCard (K := K) - 1) :
    LogShellResiduePowerCardCorrectionHypothesis (K := K) (p := p)
      (logShellRamificationExponent (K := K) (p := p) *
        logShellScaleExponentFactor (p := p) - 1)
      ((logShellResidueCard (K := K) - 1) /
        Nat.card (CommGroup.torsion (Integers K)ˣ)) := by
  classical
  letI : IsDiscreteValuationRing (Integers K) :=
    isDiscreteValuationRingIntegers (K := K) (p := p)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (Integers K)
  obtain ⟨eEquiv⟩ := congruenceUnits_equiv_primary_general (K := K) (p := p) π hπ
  have hquot : Nat.card ((Integers K)ˣ ⧸ logShellCongruenceUnits (K := K) (p := p)) =
      Nat.card ((Integers K ⧸ Ideal.span {((logShellScale p : Nat) : Integers K)})ˣ) :=
    Nat.card_congr eEquiv.toEquiv
  have hunits := truncatedUnitsCardPrimary (K := K) (p := p)
  unfold TruncatedUnitsCardPrimary at hunits
  have hTpos : 0 < Nat.card (CommGroup.torsion (Integers K)ˣ) := by
    letI := finite_integralUnitTorsion (K := K) (p := p)
    exact Nat.card_pos
  have hdivmul : Nat.card (CommGroup.torsion (Integers K)ˣ) *
      ((logShellResidueCard (K := K) - 1) /
        Nat.card (CommGroup.torsion (Integers K)ˣ)) =
      logShellResidueCard (K := K) - 1 := by
    rw [Nat.mul_comm]
    exact Nat.div_mul_cancel hdiv
  unfold LogShellResiduePowerCardCorrectionHypothesis
  rw [hquot, hunits]
  rw [Nat.mul_assoc, hdivmul, Nat.mul_comm]
end LeanFormal.IUT.XiFPaper.Mzk1CorrectionHypothesisActual
end