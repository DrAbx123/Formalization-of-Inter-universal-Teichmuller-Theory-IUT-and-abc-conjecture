import LeanFormal.IUT.IUTIII.Corollary312.StepXI.Contract

/-! Mainline: explicit Step-XI contract assembly constructor (real helper; no sorry/axiom). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIContractAssemblyActual

open LeanFormal.IUT

/-- Assemble a Step XI contract from supplied ordered data and slot evidence. -/
def assembleStepXIContract (q theta target : ℝ) (hq : q < 0)
    (hqt : q ≤ target) (htth : target ≤ theta)
    {ipl she apt : Prop} (hipl : ipl) (hshe : she) (hapt : apt) :
    StepXIContract where
  qSigned := q
  thetaSigned := theta
  targetSigned := target
  q_negative := hq
  ipl := ipl
  she := she
  apt := apt
  ipl_evidence := hipl
  she_evidence := hshe
  apt_evidence := hapt
  q_le_target := hqt
  target_le_theta := htth

theorem assembleStepXIContract_conclusion (q theta target : ℝ) (hq : q < 0)
    (hqt : q ≤ target) (htth : target ≤ theta)
    {ipl she apt : Prop} (hipl : ipl) (hshe : she) (hapt : apt) :
    Cor312Conclusion
      (assembleStepXIContract q theta target hq hqt htth hipl hshe hapt) :=
  cor312_of_constructed_stepXI
    (assembleStepXIContract q theta target hq hqt htth hipl hshe hapt)

theorem assembleStepXIContract_q_positive (q theta target : ℝ) (hq : q < 0)
    (hqt : q ≤ target) (htth : target ≤ theta)
    {ipl she apt : Prop} (hipl : ipl) (hshe : she) (hapt : apt) :
    0 < -(assembleStepXIContract q theta target hq hqt htth hipl hshe hapt).qSigned :=
  q_positive_of_constructed_stepXI
    (assembleStepXIContract q theta target hq hqt htth hipl hshe hapt)

theorem assembleStepXIContract_ipl (q theta target : ℝ) (hq : q < 0)
    (hqt : q ≤ target) (htth : target ≤ theta)
    {ipl she apt : Prop} (hipl : ipl) (hshe : she) (hapt : apt) :
    (assembleStepXIContract q theta target hq hqt htth hipl hshe hapt).ipl :=
  hipl

end LeanFormal.IUT.XiFPaper.Mzk1StepXIContractAssemblyActual