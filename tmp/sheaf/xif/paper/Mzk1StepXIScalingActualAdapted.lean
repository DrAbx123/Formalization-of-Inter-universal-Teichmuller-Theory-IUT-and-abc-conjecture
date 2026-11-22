import LeanFormal.IUT.IUTIII.Corollary312.StepXI.Contract

/-! Mainline: positive rescaling of a Step-XI contract preserves all ordered data and the
  Cor 3.12 conclusion (real construction; no sorry/axiom). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIScalingActualAdapted

open LeanFormal.IUT

/-- Positive rescaling of a Step-XI contract (scales the three signed quantities only). -/
def scaleStepXIContract (k : ℝ) (hk : 0 < k) (C : StepXIContract) : StepXIContract where
  qSigned := k * C.qSigned
  thetaSigned := k * C.thetaSigned
  targetSigned := k * C.targetSigned
  q_negative := mul_neg_of_pos_of_neg hk C.q_negative
  ipl := C.ipl
  she := C.she
  apt := C.apt
  ipl_evidence := C.ipl_evidence
  she_evidence := C.she_evidence
  apt_evidence := C.apt_evidence
  q_le_target := mul_le_mul_of_nonneg_left C.q_le_target (le_of_lt hk)
  target_le_theta := mul_le_mul_of_nonneg_left C.target_le_theta (le_of_lt hk)

theorem scaleStepXIContract_conclusion (k : ℝ) (hk : 0 < k) (C : StepXIContract) :
    Cor312Conclusion (scaleStepXIContract k hk C) :=
  cor312_of_constructed_stepXI (scaleStepXIContract k hk C)

theorem scaleStepXIContract_q_positive (k : ℝ) (hk : 0 < k) (C : StepXIContract) :
    0 < -(scaleStepXIContract k hk C).qSigned :=
  q_positive_of_constructed_stepXI (scaleStepXIContract k hk C)

theorem scaleStepXIContract_ipl (k : ℝ) (hk : 0 < k) (C : StepXIContract) :
    (scaleStepXIContract k hk C).ipl :=
  C.ipl_evidence

theorem scaleStepXIContract_one (C : StepXIContract) :
    (scaleStepXIContract 1 zero_lt_one C).qSigned = C.qSigned :=
  one_mul C.qSigned

end LeanFormal.IUT.XiFPaper.Mzk1StepXIScalingActualAdapted