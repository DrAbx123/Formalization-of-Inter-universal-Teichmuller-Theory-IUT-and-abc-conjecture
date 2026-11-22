/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1HullDetFourTriangleActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.Contract

/-!
# Mzk1SHEIPLAPTObjectActual — actual SHE/IPL/APT object (3.11 input side)

A517 object file reusing our green assets:
* `SHEArrowStatement` with the PROVED evidence `sheArrowStatement_proved`
  (`Mzk1QPilotSHEDoubleImageActual`, simultaneous holomorphic expressibility);
* `ipl`/`apt` slots as explicit named propositions with supplied evidence
  (the standard `StepXIContract` pattern; NOT claimed constructed here).

Packages the three into one object and into the `StepXIContract` slots.
No new axiom, no comparison, no True placeholder. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.Mzk1SHEIPLAPTObjectActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.Mzk1QPilotSHEDoubleImageActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-- The SHE/IPL/APT evidence object: proofs of three named propositions. -/
structure SHEIPLAPTObject (she ipl apt : Prop) where
  /-- evidence for the SHE slot. -/
  she_proof : she
  /-- evidence for the IPL slot. -/
  ipl_proof : ipl
  /-- evidence for the APT slot. -/
  apt_proof : apt

/-- The constructed object: SHE is the actual proved double-image statement; IPL/APT
are the caller's named propositions with evidence. -/
noncomputable def sheIPLAPTObject (ipl : Prop) (hipl : ipl)
    (apt : Prop) (hapt : apt) :
    SHEIPLAPTObject (SHEArrowStatement T) ipl apt where
  she_proof := sheArrowStatement_proved T
  ipl_proof := hipl
  apt_proof := hapt

/-- `_constructed`: the SHE evidence is the proved SHE arrow statement. -/
theorem sheIPLAPTObject_constructed (ipl : Prop) (hipl : ipl)
    (apt : Prop) (hapt : apt) :
    (sheIPLAPTObject T ipl hipl apt hapt).she_proof = sheArrowStatement_proved T :=
  rfl

/-- The SHE arrow statement, as an independent theorem of the double image. -/
theorem she_of_double_image : SHEArrowStatement T := sheArrowStatement_proved T

/-- The object provides the three contract slots with their evidence. -/
theorem sheIPLAPTObject_slots (ipl : Prop) (hipl : ipl) (apt : Prop) (hapt : apt) :
    let O := sheIPLAPTObject T ipl hipl apt hapt
    O.she_proof ∧ O.ipl_proof ∧ O.apt_proof := by
  intro O
  exact ⟨O.she_proof, O.ipl_proof, O.apt_proof⟩

/-- Feeding the object's SHE evidence into a `StepXIContract`. -/
def sheIPLAPTObject_contract (ipl : Prop) (hipl : ipl) (apt : Prop) (hapt : apt)
    (qSigned thetaSigned targetSigned : Real) (hq : qSigned < 0)
    (hqt : qSigned ≤ targetSigned) (htt : targetSigned ≤ thetaSigned) :
    StepXIContract where
  qSigned := qSigned
  thetaSigned := thetaSigned
  targetSigned := targetSigned
  q_negative := hq
  ipl := ipl
  she := SHEArrowStatement T
  apt := apt
  ipl_evidence := hipl
  she_evidence := sheArrowStatement_proved T
  apt_evidence := hapt
  q_le_target := hqt
  target_le_theta := htt

#check sheIPLAPTObject_constructed
#check she_of_double_image
#check sheIPLAPTObject_contract

end LeanFormal.IUT.XiFPaper.Mzk1SHEIPLAPTObjectActual
end
