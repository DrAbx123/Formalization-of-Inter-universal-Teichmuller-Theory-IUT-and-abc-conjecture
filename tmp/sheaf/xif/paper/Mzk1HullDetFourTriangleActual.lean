import tmp.sheaf.xif.paper.Mzk1HullDetStep3115Actual
import tmp.sheaf.xif.paper.Mzk1QPilotSHEDoubleImageActual

/-! # Mzk1HullDetFourTriangleActual — hull/det readouts wired into the shared
four-triangle synthesis (A487, shared B-version interface).

Assembles `hullDetHDD` / `hullDetDsc` / `hullDetSheOut` from
`Mzk1HullDetStep3115Actual` into a `FourTriangleSynthesis` of the shared module
`Mzk1FourTriangleSharedActual`.  The Step (xi-f) comparison is the proved
det-normalized comparison `packetDet packet * q <= 1`.

The StepXI contract slots: `she` is the PROVED SHE arrow statement on the literal
carriers (`SHEArrowStatement T`, evidence `sheArrowStatement_proved T`, reusing the
qpilot double-image proof); `ipl`/`apt` are explicit named propositions with their
supplied evidence (no `True`/`trivial` placeholders).

No sorry/axiom; no closure claim. Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1HullDetFourTriangleActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.Mzk1FourTriangleSharedActual
open LeanFormal.IUT.XiFPaper.Mzk1HullDetStep3115Actual
open LeanFormal.IUT.XiFPaper.Mzk1QPilotSHEDoubleImageActual

universe u

variable {label : Type u} [Fintype label] [DecidableEq label]
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)

/-- Wiring: given a StepXI contract whose q/theta slots are the concrete hull/det
readouts (hypotheses) and the normalized comparison input, produce the shared
four-triangle synthesis instance. -/
def hullDetFourTriangle (x : HullDetState label) (contract : StepXIContract)
    (hull_eq : contract.qSigned =
      (fourTriangleReadout hullDetHDD (hullDetDsc x) hullDetSheOut).1)
    (theta_eq : contract.thetaSigned =
      (fourTriangleReadout hullDetHDD (hullDetDsc x) hullDetSheOut).2)
    (hcmp : packetDet x.packet * x.q <= 1) :
    FourTriangleSynthesis (HullDetState label) Unit where
  contract := contract
  hdd := hullDetHDD
  dsc := hullDetDsc x
  sheOut := hullDetSheOut
  hull_eq := hull_eq
  theta_eq := theta_eq
  step3115_comparison := step3115_comparison_hullDet x hcmp

/-- The Cor 3.12 conclusion from the wired shared four-triangle instance. -/
theorem hullDetFourTriangle_cor312 (x : HullDetState label)
    (contract : StepXIContract)
    (hull_eq : contract.qSigned =
      (fourTriangleReadout hullDetHDD (hullDetDsc x) hullDetSheOut).1)
    (theta_eq : contract.thetaSigned =
      (fourTriangleReadout hullDetHDD (hullDetDsc x) hullDetSheOut).2)
    (hcmp : packetDet x.packet * x.q <= 1) :
    Cor312Conclusion contract :=
  cor312Conclusion_of_fourTriangleSynthesis
    (hullDetFourTriangle x contract hull_eq theta_eq hcmp)

/-- Concrete StepXI contract for the hull/det step: qSigned is the hull
log-volume, thetaSigned is the det-normalized -log|q|, targetSigned is the hull
log-volume.  The `she` slot is the proved SHE arrow statement on the literal
carriers; `ipl`/`apt` are explicit named propositions with evidence. -/
def hullDetContract (x : HullDetState label) (hneg : hullReadout x < 0)
    (ipl : Prop) (hipl : ipl) (apt : Prop) (hapt : apt)
    (hcmp : packetDet x.packet * x.q <= 1) : StepXIContract where
  qSigned := hullReadout x
  thetaSigned := detReadout x
  targetSigned := hullReadout x
  q_negative := hneg
  ipl := ipl
  she := SHEArrowStatement T
  apt := apt
  ipl_evidence := hipl
  she_evidence := sheArrowStatement_proved T
  apt_evidence := hapt
  q_le_target := le_rfl
  target_le_theta := hullReadout_le_detReadout_of_packetDet_mul_le_one x hcmp

/-- The concrete contract wired into the shared four-triangle instance. -/
def hullDetFourTriangleConcrete (x : HullDetState label)
    (hneg : hullReadout x < 0) (ipl : Prop) (hipl : ipl)
    (apt : Prop) (hapt : apt)
    (hcmp : packetDet x.packet * x.q <= 1) :
    FourTriangleSynthesis (HullDetState label) Unit :=
  hullDetFourTriangle x
    (hullDetContract T x hneg ipl hipl apt hapt hcmp) rfl rfl hcmp

/-- Cor 3.12 conclusion from the concrete wired instance. -/
theorem hullDetFourTriangleConcrete_cor312 (x : HullDetState label)
    (hneg : hullReadout x < 0) (ipl : Prop) (hipl : ipl)
    (apt : Prop) (hapt : apt)
    (hcmp : packetDet x.packet * x.q <= 1) :
    Cor312Conclusion
      (hullDetFourTriangleConcrete T x hneg ipl hipl apt hapt hcmp).contract :=
  cor312Conclusion_of_fourTriangleSynthesis _

end LeanFormal.IUT.XiFPaper.Mzk1HullDetFourTriangleActual
