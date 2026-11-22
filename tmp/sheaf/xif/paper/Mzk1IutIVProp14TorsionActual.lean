/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.IutIVProp14TorsionCountActual
import tmp.sheaf.xif.paper.IutIVProp14GammaPGroupActual
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellIntegerQuotient
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellIndexResidueFormula
import Mathlib.Tactic

/-! # IUT IV Prop 1.4: torsion actual from Gamma actual + #C input -/

noncomputable section
namespace LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open scoped NNReal NormedField
variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
variable [IsUltrametricDist K] [ProperSpace K]
variable {p : Nat} [Fact p.Prime] [localNormedAlgebra : NormedAlgebra (Padic p) K]
include localNormedAlgebra
theorem torsion_card_eq_actual_of_congruenceCard
    {e f s : Nat}
    (hC : Nat.card ((Integers K)ˣ ⧸ logShellCongruenceUnits (K := K) (p := p)) =
      (logShellResidueCard (K := K) - 1) * p ^ (f * (e * s - 1)))
    (hq : logShellResidueCard (K := K) = p ^ f)
    (hcop : Nat.Coprime p (logShellResidueCard (K := K) - 1)) :
    ∃ h m : Nat,
      Nat.card (LogShellIntegerQuotient (K := K) (p := p)) = p ^ h ∧
      Nat.card (CommGroup.torsion (Integers K)ˣ) =
        (logShellResidueCard (K := K) - 1) * p ^ m ∧
      h + m = f * (e * s - 1) := by
  letI := finite_integralUnitTorsion (K := K) (p := p)
  letI := finite_logShellCongruenceQuotient (K := K) (p := p)
  letI := finite_logShellIntegerQuotient (K := K) (p := p)
  obtain ⟨h, hGamma⟩ := card_gamma_eq_pow_actual (K := K) (p := p)
  have hdecomp :
      Nat.card ((Integers K)ˣ ⧸ logShellCongruenceUnits (K := K) (p := p)) =
        Nat.card (CommGroup.torsion (Integers K)ˣ) *
          Nat.card (LogShellIntegerQuotient (K := K) (p := p)) := by
    rw [card_logShellCongruenceQuotient]
    rfl
  obtain ⟨m, hT, hm⟩ := torsion_card_eq_of_congruenceCard
    (T := CommGroup.torsion (Integers K)ˣ)
    (C := (Integers K)ˣ ⧸ logShellCongruenceUnits (K := K) (p := p))
    (Gamma := LogShellIntegerQuotient (K := K) (p := p))
    hdecomp hC hGamma hq hcop
  exact ⟨h, m, hGamma, hT, hm⟩
end LeanFormal.IUT.LocalFieldLogarithm
