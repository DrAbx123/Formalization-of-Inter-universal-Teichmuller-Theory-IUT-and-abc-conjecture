/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1XiFFormalStepActual
import tmp.sheaf.xif.paper.Mzk1FourTriangleObjectActual

/-!
# Mzk1XiEContainmentObjectActual — xi-e containment object and xi-f ⇒ Cor 3.12

A518: the xi-e containment input of IUT III Cor 3.12 Step (xi-e), packaged as a
real object over the abstract xi-f formal step (`Mzk1XiFFormalStepActual`):
* a `StepXIContract` plus the containment `qSigned ∈ regionLe thetaSigned`;
* xi-f step: `qSigned ≤ thetaSigned`;
* Cor 3.12 conclusion;
* the analog for the fourth triangle (`FourTriangleSynthesis`).

No new axiom, no comparison beyond the containment input. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentObjectActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1XiFFormalStepActual
open LeanFormal.IUT.XiFPaper.Mzk1FourTriangleSharedActual
open LeanFormal.IUT.XiFPaper.Mzk1FourTriangleObjectActual

/-- The xi-e containment object: a contract plus the containment of its
q-pilot log-volume in the possible Theta-pilot log-volumes. -/
structure XiEContainmentObject where
  /-- the StepXI contract. -/
  contract : StepXIContract
  /-- xi-e containment of the q-slot in the Theta-pilot possible set. -/
  containment : contract.qSigned ∈ regionLe contract.thetaSigned

/-- The constructed containment object. -/
def xiEContainmentObject (contract : StepXIContract)
    (h : contract.qSigned ∈ regionLe contract.thetaSigned) :
    XiEContainmentObject where
  contract := contract
  containment := h

/-- xi-f formal step: the containment gives `qSigned ≤ thetaSigned`. -/
theorem xiEContainmentObject_le (O : XiEContainmentObject) :
    O.contract.qSigned ≤ O.contract.thetaSigned :=
  xi_f_formal_step O.containment

/-- Cor 3.12 conclusion from the containment object. -/
theorem xiEContainmentObject_cor312 (O : XiEContainmentObject) :
    Cor312Conclusion O.contract :=
  xiEContainmentObject_le O

/-- The calibrated `C_Θ ≥ −1` conclusion from the calibrated pilot data and
the xi-e containment. -/
theorem xiEContainmentObject_C_ge_neg_one (D : CalibratedPilots)
    (h : D.logq ∈ possibleLogVolumes D) : -1 ≤ D.C :=
  xi_f_C_ge_neg_one D h

/-- Containment object attached to a four-triangle synthesis (fourth triangle). -/
structure XiEFourTriangleContainment (DSC SHEOut : Type*) where
  /-- the shared-B four-triangle synthesis. -/
  synthesis : FourTriangleSynthesis DSC SHEOut
  /-- xi-e containment for its contract. -/
  containment : synthesis.contract.qSigned ∈
    regionLe synthesis.contract.thetaSigned

/-- Cor 3.12 conclusion from the four-triangle containment. -/
theorem xiEFourTriangleContainment_cor312 {DSC SHEOut : Type*}
    (C : XiEFourTriangleContainment DSC SHEOut) :
    Cor312Conclusion C.synthesis.contract :=
  xi_f_formal_step C.containment

#check xiEContainmentObject_cor312
#check xiEFourTriangleContainment_cor312

end LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentObjectActual
end
