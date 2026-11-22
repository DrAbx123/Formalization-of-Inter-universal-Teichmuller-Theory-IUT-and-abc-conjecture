/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1IutIVCongruenceCardActual
import tmp.sheaf.xif.paper.Mzk1TruncatedUnitsPrimaryActual
import Mathlib.Tactic
/-! # Connect the actual log-shell index to the QFE quotient division -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1IndexQFEConnectionActual
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open scoped NNReal NormedField
variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
variable [IsUltrametricDist K] [ProperSpace K]
variable {p : Nat} [Fact p.Prime] [localNormedAlgebra : NormedAlgebra (Padic p) K]
variable [FiniteDimensional (Padic p) K]
include localNormedAlgebra
/-- Actual QFE quotient cardinal, unconditional. -/
theorem qfe_quotient_card_actual :
    Nat.card ((Integers K)ˣ ⧸ logShellCongruenceUnits (K := K) (p := p)) =
      logShellResidueCard (K := K) ^
          (logShellRamificationExponent (K := K) (p := p) *
            logShellScaleExponentFactor (p := p) - 1) *
        (logShellResidueCard (K := K) - 1) := by
  classical
  letI : IsDiscreteValuationRing (Integers K) :=
    isDiscreteValuationRingIntegers (K := K) (p := p)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (Integers K)
  obtain ⟨eEquiv⟩ := congruenceUnits_equiv_primary_general (K := K) (p := p) π hπ
  have hcard := Nat.card_congr eEquiv.toEquiv
  have hunits := truncatedUnitsCardPrimary (K := K) (p := p)
  unfold TruncatedUnitsCardPrimary at hunits
  rw [hcard, hunits, Nat.mul_comm]
/-- The actual index is the quotient divided by the torsion order. -/
theorem index_eq_qfe_quotient_div
    (hquot : Nat.card ((Integers K)ˣ ⧸ logShellCongruenceUnits (K := K) (p := p)) =
      logShellResidueCard (K := K) ^
          (logShellRamificationExponent (K := K) (p := p) *
            logShellScaleExponentFactor (p := p) - 1) *
        (logShellResidueCard (K := K) - 1))
    (hTpos : 0 < Nat.card (CommGroup.torsion (Integers K)ˣ)) :
    logShellIntegerIndex (K := K) (p := p) =
      logShellResidueCard (K := K) ^
          (logShellRamificationExponent (K := K) (p := p) *
            logShellScaleExponentFactor (p := p) - 1) *
        (logShellResidueCard (K := K) - 1) /
      Nat.card (CommGroup.torsion (Integers K)ˣ) := by
  have hdecomp :=
    logShellCongruenceQuotient_card_eq_torsion_mul_logShellIntegerIndex (K := K) (p := p)
  have h1 : Nat.card (CommGroup.torsion (Integers K)ˣ) *
      logShellIntegerIndex (K := K) (p := p) =
      logShellResidueCard (K := K) ^
          (logShellRamificationExponent (K := K) (p := p) *
            logShellScaleExponentFactor (p := p) - 1) *
        (logShellResidueCard (K := K) - 1) := by
    rw [← hdecomp, hquot]
  calc logShellIntegerIndex (K := K) (p := p)
      = Nat.card (CommGroup.torsion (Integers K)ˣ) *
          logShellIntegerIndex (K := K) (p := p) /
        Nat.card (CommGroup.torsion (Integers K)ˣ) :=
          (Nat.mul_div_right _ hTpos).symm
    _ = _ := by rw [h1]
end LeanFormal.IUT.XiFPaper.Mzk1IndexQFEConnectionActual
end