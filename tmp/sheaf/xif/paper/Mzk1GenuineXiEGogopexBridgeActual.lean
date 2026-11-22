/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1XiEContainmentGenuineAuditActual
import tmp.sheaf.gogopex.Iut.Stage1.PilotComparison

/-! # A531: genuine xi-e containment => Gogopex signed comparison -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1GenuineXiEGogopexBridgeActual

open Iut.Stage1

variable {X : Type*}

/-- The Gogopex Stage-1 package from the GENUINE xi-e data: signed readings are the
two distinct pilot log-volumes (`qSigned = logVol qImage`, `thetaSigned = logVol thetaHull`),
and the comparison is the paper direction obtained from the Kummer/multiradial
containment (not a definitional union). -/
def stage1ComparisonOfGenuine (logVol : Set X → ℝ)
    (mono : ∀ {S T : Set X}, S ⊆ T → logVol S ≤ logVol T)
    (D : LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentGenuineAuditActual.GenuineXiEData)
    (hqpos : 0 < -logVol D.qImage) (httpos : 0 < -logVol D.thetaHull) :
    Stage1Comparison where
  theta := { side := PilotSide.theta, value := -logVol D.thetaHull }
  q := { side := PilotSide.q, value := -logVol D.qImage }
  theta_side := rfl
  q_side := rfl
  q_positive := hqpos
  comparison := by
    have hle : logVol D.qImage ≤ logVol D.thetaHull := mono D.kummer_qImage_subset
    show -(-logVol D.thetaHull) ≥ -(-logVol D.qImage)
    linarith

end LeanFormal.IUT.XiFPaper.Mzk1GenuineXiEGogopexBridgeActual
