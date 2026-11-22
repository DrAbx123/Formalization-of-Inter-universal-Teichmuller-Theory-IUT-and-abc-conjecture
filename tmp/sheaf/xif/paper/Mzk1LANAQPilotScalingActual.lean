/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.lana.iut.Iut.Wall.QPilotRegion
import tmp.sheaf.lana.iut.Iut.Wall.Pilots
import tmp.sheaf.lana.iut.Iut.Wall.Scaling

/-!
# Mzk1LANAQPilotScalingActual — q-pilot scale equalities (gap = 0 side)

A492: the explicit q-pilot scale `|log q|`, the q-pilot lhs, the constructed q-pilot
region log-volume and the LANA mono-analytic scaling `qScale : Scaling D` are four
manifestations of the same number `qPilotScale = D.qPilot.absLogQ`; the `2ℓ`
normalization is `D.qPilot.absLogQ = D.qPilot.logQ/(2ℓ)` and `lhs = -absLogQ`
(`Iut/Cor312/LeftHandSide.lean`).  All proofs unfold the LANA definitions plus the
existing lemmas `shift_qScale`, `logVol_qRegion`, `pilot_qVal`, `pilot_qVal_eq_neg_lhs`.
Single file; no LANA source modified; no incomplete proof. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.Mzk1LANAQPilotScalingActual

open NumberField MeasureTheory
open scoped Pointwise
open Iut
open Iut.Wall

universe u
variable (D : InitialThetaData.{u})

/-- The q-pilot scale `|log q| = absLogQ` of the LANA q-pilot data. -/
def qPilotScale : Real := D.qPilot.absLogQ

/-- The q-pilot scale is positive. -/
theorem qPilotScale_pos : 0 < qPilotScale D := by
  unfold qPilotScale
  exact absLogQ_pos D

/-- The `2ℓ`-normalization: `|log q| = log q / (2ℓ)` (definitional in LANA). -/
theorem qPilotScale_eq_logQ_div :
    qPilotScale D = D.qPilot.logQ / (2 * (D.ℓ : Real)) := rfl

/-- Conversely `log q = 2ℓ · |log q|`. -/
theorem qPilot_logQ_eq_twoL_mul_scale :
    D.qPilot.logQ = (2 * (D.ℓ : Real)) * qPilotScale D := by
  rw [qPilotScale_eq_logQ_div]
  have h5 : (5 : Nat) <= D.ℓ := D.prime.five_le
  have hℓ : (0 : Real) < (D.ℓ : Real) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) h5)
  field_simp

/-- The q-pilot lhs is the negative q-pilot scale (definitional in LANA). -/
theorem qPilot_lhs_eq_neg_scale :
    (concreteVariantData D).qPilot.lhs = -qPilotScale D := by
  have hq : (concreteVariantData D).qPilot = D.qPilot := rfl
  rw [hq, qPilotScale]
  rfl

/-- The LANA `qScale` shift is exactly the negative q-pilot scale. -/
theorem shift_qScale_eq_neg_qPilotScale :
    shift D (qScale D) = -qPilotScale D := by
  rw [shift_qScale]
  rfl

/-- The constructed q-pilot region has log-volume `−|log q|`. -/
theorem logVol_qRegion_eq_neg_qPilotScale :
    logVol D (qRegion D) = -qPilotScale D := by
  rw [logVol_qRegion]
  exact qPilot_lhs_eq_neg_scale D

/-- Scaling and region agree on the q-pilot side: the shift of `qScale` is the
log-volume of the q-pilot region. -/
theorem shift_qScale_eq_logVol_qRegion :
    shift D (qScale D) = logVol D (qRegion D) := by
  rw [shift_qScale_eq_neg_qPilotScale, logVol_qRegion_eq_neg_qPilotScale]

/-- The q-pilot region is the image of the integral region under the `qScale` action. -/
theorem act_qScale_eq_qRegion :
    act D (qScale D) (integralRegion D) = qRegion D := by
  rw [act_qScale]
  rfl

#check qPilotScale_eq_logQ_div
#check qPilot_logQ_eq_twoL_mul_scale
#check shift_qScale_eq_neg_qPilotScale
#check logVol_qRegion_eq_neg_qPilotScale

end LeanFormal.IUT.XiFPaper.Mzk1LANAQPilotScalingActual
end
