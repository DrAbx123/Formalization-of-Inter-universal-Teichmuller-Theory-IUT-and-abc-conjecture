/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.IutIVProp14VolumeActual
import tmp.sheaf.xif.paper.IutIVProp14GroupCountInterfaceActual
import Mathlib.Tactic

/-! # IUT IV Prop 1.4: h from #Gamma=p^h, volume ratio bridge -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1IutIVProp14GroupCountBridgeActual
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.IutIVProp14VolumeActual

theorem exists_h_card_gamma
    (K : Type*) [NormedField K] [CharZero K] [CompleteSpace K]
    [IsUltrametricDist K] [ProperSpace K]
    (p : Nat) [Fact p.Prime] [NormedAlgebra ℚ_[p] K]
    (Γ : Type*) [AddCommGroup Γ] [Finite Γ]
    (hΓ : IsPGroup p (Multiplicative Γ)) :
    ∃ h : Nat, Nat.card Γ = p ^ h :=
  card_gamma_eq_pow (K := K) (p := p) hΓ

theorem volume_ratio_eq_pow_of_groupCount
    (p : ℝ) (hp : (0 : ℝ) < p)
    (d s h f m : ℕ) (μO μΛ μL : ℝ)
    (hexp : h + f + m = s * d)
    (hμΛ : μΛ = p ^ h * μO)
    (hL : μL = p ^ (-(s * d : ℤ)) * μΛ) :
    μL = p ^ (-(f + m : ℤ)) * μO :=
  volume_ratio_eq_pow (p := p) hp d s h f m μO μΛ μL hexp hμΛ hL

end LeanFormal.IUT.XiFPaper.Mzk1IutIVProp14GroupCountBridgeActual
