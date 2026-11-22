import tmp.sheaf.xif.paper.Mzk1Cor312FinalStatementActual
import tmp.sheaf.xif.paper.Mzk1SignedCor312ContractActual

/-! # Cor 3.12 final self-checks: target vs genuine content -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalSelfChecksActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalStatementActual
open LeanFormal.IUT.XiFPaper.Mzk1SignedCor312ContractActual

/-- `Cor312Conclusion` is definitionally the signed inequality (no hidden target). -/
theorem cor312Conclusion_definition (C : StepXIContract) :
    Cor312Conclusion C ↔ C.qSigned ≤ C.thetaSigned := by
  unfold Cor312Conclusion
  exact Iff.rfl

/-- `target_le_theta` is the paper-readout identity `theta := target` (rfl),
not the xi-e inequality; the genuine inequality is `q_le_target`. -/
theorem target_le_theta_is_identity (q theta : Real) (hq : q < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) (hle : q ≤ theta) :
    (signedCor312Contract q theta hq ipl hipl she hshe apt hapt hle).targetSigned
      = (signedCor312Contract q theta hq ipl hipl she hshe apt hapt hle).thetaSigned := rfl

/-- The genuine comparison field is exactly the supplied `q ≤ theta` hypothesis. -/
theorem q_le_target_is_genuine (q theta : Real) (hq : q < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) (hle : q ≤ theta) :
    (signedCor312Contract q theta hq ipl hipl she hshe apt hapt hle).qSigned ≤
      (signedCor312Contract q theta hq ipl hipl she hshe apt hapt hle).targetSigned :=
  hle

/-- Paper target from magnitudes gives the signed inequality (paper shape check). -/
theorem paperTarget_signed_check (qMag thetaMag : Real)
    (h : thetaMag ≤ qMag) : paperTarget qMag thetaMag :=
  (paperTarget_iff_magnitudes qMag thetaMag).2 h

end LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalSelfChecksActual
