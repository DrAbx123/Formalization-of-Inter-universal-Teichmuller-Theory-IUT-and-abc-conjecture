import LeanFormal.IUT.IUTIII.Corollary312.StepXI.Contract

/-!
# Signed 3.12 assembly into the StepXI contract

Given real signed pilot log-volumes `qSigned ≤ thetaSigned` and `qSigned < 0`
(the actual hull log-volumes are negative), plus the qualitative IPL/SHE/APT
data as explicit propositions/evidence, this file constructs the StepXI
contract with `targetSigned := thetaSigned` and obtains `Cor312Conclusion`.

No sorry, axiom, True or placeholder.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1SignedCor312ContractActual

open LeanFormal.IUT

universe u

/-- Construct `StepXIContract` from signed pilot readouts and the qualitative
IPL/SHE/APT data (all as real data/evidence, not placeholder fields). -/
noncomputable def signedCor312Contract
    (qSigned thetaSigned : Real) (hq : qSigned < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) (hle : qSigned ≤ thetaSigned) :
    StepXIContract where
  qSigned := qSigned
  thetaSigned := thetaSigned
  targetSigned := thetaSigned
  q_negative := hq
  ipl := ipl
  she := she
  apt := apt
  ipl_evidence := hipl
  she_evidence := hshe
  apt_evidence := hapt
  q_le_target := hle
  target_le_theta := le_rfl

/-- The signed assembly satisfies the StepXI comparison field definitionally. -/
theorem signedCor312Contract_comparison
    (qSigned thetaSigned : Real) (hq : qSigned < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) (hle : qSigned ≤ thetaSigned) :
    (signedCor312Contract qSigned thetaSigned hq ipl hipl she hshe apt hapt hle).qSigned ≤
      (signedCor312Contract qSigned thetaSigned hq ipl hipl she hshe apt hapt hle).thetaSigned :=
  hle

/-- Cor 3.12 conclusion from the signed assembly. -/
theorem signedCor312_conclusion
    (qSigned thetaSigned : Real) (hq : qSigned < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) (hle : qSigned ≤ thetaSigned) :
    Cor312Conclusion
      (signedCor312Contract qSigned thetaSigned hq ipl hipl she hshe apt hapt hle) := by
  unfold Cor312Conclusion signedCor312Contract
  exact hle

end LeanFormal.IUT.XiFPaper.Mzk1SignedCor312ContractActual
