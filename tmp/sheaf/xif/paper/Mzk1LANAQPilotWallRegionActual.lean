/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.lana.iut.Iut.Wall.QPilotRegion
import tmp.sheaf.lana.iut.Iut.Wall.Pilots
import tmp.sheaf.lana.iut.Iut.Wall.Checks

/-!
# Mzk1LANAQPilotWallRegionActual — explicit q-pilot region/scale data for the numerical wall

A490 q-pilot contribution: explicit region and scale definitions for the q-pilot
side of `Iut.Wall.NumericalWall` (LANA port), together with the volume lemmas:

* `qPilotWallRegion := qRegion D` (the constructed `{q_v O_v}` region of
  `Iut/Wall/QPilotRegion.lean`, label 1 placement);
* `qPilotScale := D.qPilot.absLogQ = -D.qPilot.lhs` (the explicit `|log q|` scale);
* `logVol_qPilotWallRegion : logVol(qPilotWallRegion) = -qPilotScale` and the
  componentwise volume formula `globalVol(qRegion i) = -logQ/(2ℓ)` (e = 1);
* `qPilotWallRegion_first` (first capsule coincides with `LGP·O`) and the
  adelic property, packaged as `QPilotRegionWallData`;
* the `NumericalWall` shadow form with the q-pilot class written in the explicit
  scale `-qPilotScale` (`numericalWall_iff_rss_qPilotScale`).

Single file; no modification of LANA sources. No incomplete proof. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.Mzk1LANAQPilotWallRegionActual

open NumberField MeasureTheory
open scoped Pointwise
open Iut
open Iut.Wall

universe u

variable (D : InitialThetaData.{u})

/-- The explicit q-pilot region of the numerical wall: the constructed `{q_v O_v}`
region (label 1 placement, IUT III Cor 3.12 q-pilot side). -/
def qPilotWallRegion : Region D := qRegion D

/-- The explicit q-pilot scale `|log q| = D.qPilot.absLogQ`. -/
def qPilotScale : Real := D.qPilot.absLogQ

/-- The q-pilot scale is the negative of the q-pilot lhs `log(q)`. -/
theorem qPilotScale_eq_neg_lhs : qPilotScale D = -(concreteVariantData D).qPilot.lhs := by
  unfold qPilotScale
  have h1 := pilot_qVal D
  have h2 := pilot_qVal_eq_neg_lhs D
  have hq : (concreteVariantData D).qPilot = D.qPilot := rfl
  rw [hq]
  linarith

/-- Equivalently, the q-pilot lhs of the concrete variant data is `-qPilotScale`. -/
theorem qPilot_lhs_eq_neg_scale :
    (concreteVariantData D).qPilot.lhs = -qPilotScale D := by
  rw [qPilotScale_eq_neg_lhs]
  ring

/-- The constructed q-pilot region is adelic. -/
theorem isAdelic_qPilotWallRegion : IsAdelic D (qPilotWallRegion D) := by
  unfold qPilotWallRegion
  exact isAdelic_qRegion D

/-- Explicit log-volume of the constructed q-pilot region: `-|log q|`. -/
theorem logVol_qPilotWallRegion :
    logVol D (qPilotWallRegion D) = -qPilotScale D := by
  unfold qPilotWallRegion qPilotScale
  rw [logVol_qRegion]
  have hq : (concreteVariantData D).qPilot = D.qPilot := rfl
  rw [hq]
  have h := pilot_qVal D
  have h2 := pilot_qVal_eq_neg_lhs D
  linarith

/-- Componentwise volume of the q-pilot region: at capsule `i` the global log-volume
is `-logQ/(2ℓ)` (the `e = 1` specialization of `globalVol_pow_integral`). -/
theorem globalVol_qPilotWallRegion_component (i : Fin (nC D)) :
    (LocalTheory.vol D.placeSect (nC D)).globalVol (qPilotWallRegion D i) =
      -(D.qPilot.logQ / (2 * (D.ℓ : Real))) := by
  have h := globalVol_pow_integral D (fun _ => 1) (labOne D) i
  simpa [qPilotWallRegion, qRegion] using h

/-- First-capsule identification: the q-pilot region coincides with `LGP·O` in the
first capsule. -/
theorem qPilotWallRegion_first :
    qPilotWallRegion D ⟨0, nC_pos D⟩ = lgp D (integralRegion D) ⟨0, nC_pos D⟩ := by
  unfold qPilotWallRegion
  exact qRegion_first D

/-- Explicit q-pilot region/scale data of the numerical wall. -/
structure QPilotRegionWallData where
  region : Region D
  adelic : IsAdelic D region
  logVol_eq_lhs : logVol D region = (concreteVariantData D).qPilot.lhs
  logVol_eq_scale : logVol D region = -qPilotScale D
  first_capsule : region ⟨0, nC_pos D⟩ = lgp D (integralRegion D) ⟨0, nC_pos D⟩

/-- The constructed q-pilot wall data. -/
def qPilotRegionWallData : QPilotRegionWallData D where
  region := qPilotWallRegion D
  adelic := isAdelic_qPilotWallRegion D
  logVol_eq_lhs := by
    unfold qPilotWallRegion
    exact logVol_qRegion D
  logVol_eq_scale := logVol_qPilotWallRegion D
  first_capsule := qPilotWallRegion_first D

/-- The numerical-wall shadow form with the q-pilot class written in the explicit
scale `-qPilotScale`. -/
theorem numericalWall_iff_rss_qPilotScale :
    NumericalWall D ↔ ∃ (U : Region D) (hU : IsAdelic D U),
      InHullOfImage D U ∧ Rss.mk D U hU = (rssEquiv D).symm (-qPilotScale D) := by
  rw [numericalWall_iff_rss]
  constructor
  · rintro ⟨U, hU, hI, h⟩
    exact ⟨U, hU, hI, by rw [h, qPilot_lhs_eq_neg_scale]⟩
  · rintro ⟨U, hU, hI, h⟩
    exact ⟨U, hU, hI, by rwa [← qPilot_lhs_eq_neg_scale] at h⟩

#check logVol_qPilotWallRegion
#check qPilotRegionWallData
#check numericalWall_iff_rss_qPilotScale

end LeanFormal.IUT.XiFPaper.Mzk1LANAQPilotWallRegionActual
end
