/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellHaarIndex
import Mathlib.Tactic

/-! # IUT IV Prop 1.4: logShellIntegerIndex = Nat.card Gamma, p^h form -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1IutIVProp14IndexCardActual
open LeanFormal.IUT.LocalFieldLogarithm
variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
variable [IsUltrametricDist K] [ProperSpace K] [MeasurableSpace K] [BorelSpace K]
variable {p : Nat} [Fact p.Prime] [NormedAlgebra ℚ_[p] K]

theorem logShellIntegerIndex_eq_natCard :
    logShellIntegerIndex (K := K) (p := p) =
      Nat.card (LogShellIntegerQuotient (K := K) (p := p)) := rfl

theorem logShellIntegerIndex_eq_pow_of_card_eq {h : Nat}
    (hh : Nat.card (LogShellIntegerQuotient (K := K) (p := p)) = p ^ h) :
    logShellIntegerIndex (K := K) (p := p) = p ^ h := by
  rw [logShellIntegerIndex_eq_natCard, hh]

end LeanFormal.IUT.XiFPaper.Mzk1IutIVProp14IndexCardActual
