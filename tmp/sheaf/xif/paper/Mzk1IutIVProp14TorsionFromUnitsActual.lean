/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1IutIVProp14CongruenceCardInterfaceActual
import tmp.sheaf.xif.paper.Mzk1IutIVProp14TorsionActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open scoped NNReal NormedField
theorem torsion_card_eq_actual_of_unitsEquiv
    {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
    [IsUltrametricDist K] [ProperSpace K]
    {p : Nat} [Fact p.Prime] [NormedAlgebra (Padic p) K]
    {e f s : Nat}
    (eEquiv : ((Integers K)ˣ ⧸ logShellCongruenceUnits (K := K) (p := p)) ≃*
      (Integers K ⧸ Ideal.span
        {(((logShellScale p : ℕ) ^ e : ℕ) : Integers K)})ˣ)
    (hcard : Nat.card ((Integers K ⧸ Ideal.span
        {(((logShellScale p : ℕ) ^ e : ℕ) : Integers K)})ˣ) =
      (logShellResidueCard (K := K) - 1) *
        logShellResidueCard (K := K) ^ (e * s - 1))
    (hs : logShellScaleExponentFactor (p := p) = s)
    (hq : logShellResidueCard (K := K) = p ^ f)
    (hcop : Nat.Coprime p (logShellResidueCard (K := K) - 1)) :
    ∃ h m : Nat,
      Nat.card (LogShellIntegerQuotient (K := K) (p := p)) = p ^ h ∧
      Nat.card (CommGroup.torsion (Integers K)ˣ) =
        (logShellResidueCard (K := K) - 1) * p ^ m ∧
      h + m = f * (e * s - 1) := by
  have hC : Nat.card ((Integers K)ˣ ⧸ logShellCongruenceUnits (K := K) (p := p)) =
      (logShellResidueCard (K := K) - 1) * p ^ (f * (e * s - 1)) := by
    have h := card_logShellCongruenceQuotient_of_unitsEquiv
      (K := K) (p := p) e eEquiv (by simpa [hs] using hcard)
    rw [h, hs, hq, pow_mul]
  exact torsion_card_eq_actual_of_congruenceCard hC hq hcop
end LeanFormal.IUT.LocalFieldLogarithm
