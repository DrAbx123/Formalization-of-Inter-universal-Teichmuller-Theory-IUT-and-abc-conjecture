/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1IutIVProp14ActualHBridgeActual
import tmp.sheaf.xif.paper.IutIVProp14VolumeActual
import Mathlib.Tactic

/-! # IUT IV Prop 1.4(ii): P14ii from actual h -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1IutIVProp14P14iiActualActual
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.IutIVProp14VolumeActual
open LeanFormal.IUT.XiFPaper.Mzk1IutIVProp14ActualHBridgeActual
variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
variable [IsUltrametricDist K] [ProperSpace K]
variable {p : Nat} [Fact p.Prime] [NormedAlgebra (Padic p) K]

theorem p14ii_logVolume_actual
    (hp : (1 : ℝ) < (p : ℝ)) (d e f m s : ℕ)
    (he : 1 ≤ e) (hf : 1 ≤ f) (hd : d = e * f)
    (μL μO μΛ : ℝ) (hμL : 0 < μL) (hμO : 0 < μO)
    (hexp : actualGammaH (K := K) (p := p) + f + m = s * d)
    (hμΛ : μΛ = (p : ℝ) ^ actualGammaH (K := K) (p := p) * μO)
    (hL : μL = (p : ℝ) ^ (-(s * d : ℤ)) * μΛ) :
    (Real.log μL - Real.log μO) / (d : ℝ) =
      -(((f + m : ℝ) / (e * f : ℝ)) * Real.log (p : ℝ)) := by
  have hratio : μL = (p : ℝ) ^ (-(f + m : ℤ)) * μO :=
    volume_ratio_eq_pow_actualH (K := K) (p := p) (by linarith : (0 : ℝ) < (p : ℝ)) d s f m μO μΛ μL hexp hμΛ hL
  exact p14ii_logVolume_cond (p := (p : ℝ)) hp d e f m he hf hd μL μO hμL hμO hratio

end LeanFormal.IUT.XiFPaper.Mzk1IutIVProp14P14iiActualActual
