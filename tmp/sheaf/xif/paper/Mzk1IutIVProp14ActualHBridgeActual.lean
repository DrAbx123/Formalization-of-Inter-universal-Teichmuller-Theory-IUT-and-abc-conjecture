/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.IutIVProp14GammaPGroupActual
import tmp.sheaf.xif.paper.Mzk1IutIVProp14GroupCountBridgeActual
import Mathlib.Tactic

/-! # IUT IV Prop 1.4: actual h from #Gamma=p^h, volume ratio -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1IutIVProp14ActualHBridgeActual
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.IutIVProp14VolumeActual
variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
variable [IsUltrametricDist K] [ProperSpace K]
variable {p : Nat} [Fact p.Prime] [NormedAlgebra (Padic p) K]

noncomputable def actualGammaH : Nat :=
  Classical.choose (card_gamma_eq_pow_actual (K := K) (p := p))

theorem actualGammaH_spec :
    Nat.card (LogShellIntegerQuotient (K := K) (p := p)) = p ^ actualGammaH (K := K) (p := p) :=
  Classical.choose_spec (card_gamma_eq_pow_actual (K := K) (p := p))

theorem volume_ratio_eq_pow_actualH
    (hp : (0 : ℝ) < (p : ℝ)) (d s f m : ℕ) (μO μΛ μL : ℝ)
    (hexp : actualGammaH (K := K) (p := p) + f + m = s * d)
    (hμΛ : μΛ = (p : ℝ) ^ actualGammaH (K := K) (p := p) * μO)
    (hL : μL = (p : ℝ) ^ (-(s * d : ℤ)) * μΛ) :
    μL = (p : ℝ) ^ (-(f + m : ℤ)) * μO :=
  volume_ratio_eq_pow (p := (p : ℝ)) hp d s (actualGammaH (K := K) (p := p)) f m μO μΛ μL hexp hμΛ hL

end LeanFormal.IUT.XiFPaper.Mzk1IutIVProp14ActualHBridgeActual
