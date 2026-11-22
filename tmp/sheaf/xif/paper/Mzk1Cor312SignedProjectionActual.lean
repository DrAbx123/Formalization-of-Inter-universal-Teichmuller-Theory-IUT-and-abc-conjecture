import tmp.sheaf.xif.paper.Mzk1SignedCor312ContractActual
import tmp.sheaf.xif.paper.Mzk1Signed312AssemblyActual

/-! # Signed contract projection checks (A545 lattice lane) -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312SignedProjectionActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1SignedCor312ContractActual

/-- qSigned projection of the signed contract is the supplied q value. -/
theorem signedContract_qSigned (q theta : Real) (hq : q < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) (hle : q ≤ theta) :
    (signedCor312Contract q theta hq ipl hipl she hshe apt hapt hle).qSigned = q := rfl

/-- thetaSigned projection is the supplied theta value. -/
theorem signedContract_thetaSigned (q theta : Real) (hq : q < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) (hle : q ≤ theta) :
    (signedCor312Contract q theta hq ipl hipl she hshe apt hapt hle).thetaSigned = theta := rfl

/-- targetSigned projection equals theta (paper readout identity). -/
theorem signedContract_targetSigned (q theta : Real) (hq : q < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) (hle : q ≤ theta) :
    (signedCor312Contract q theta hq ipl hipl she hshe apt hapt hle).targetSigned = theta := rfl

/-- q_le_target projection is the supplied comparison argument. -/
theorem signedContract_q_le_target (q theta : Real) (hq : q < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) (hle : q ≤ theta) :
    (signedCor312Contract q theta hq ipl hipl she hshe apt hapt hle).qSigned ≤
      (signedCor312Contract q theta hq ipl hipl she hshe apt hapt hle).targetSigned :=
  hle

/-- Conclusion projection: `Cor312Conclusion` is the signed inequality. -/
theorem signedContract_conclusion (q theta : Real) (hq : q < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) (hle : q ≤ theta) :
    Cor312Conclusion (signedCor312Contract q theta hq ipl hipl she hshe apt hapt hle) ↔
      q ≤ theta := by
  unfold Cor312Conclusion
  rw [signedContract_qSigned, signedContract_thetaSigned]
  exact Iff.rfl

end LeanFormal.IUT.XiFPaper.Mzk1Cor312SignedProjectionActual
