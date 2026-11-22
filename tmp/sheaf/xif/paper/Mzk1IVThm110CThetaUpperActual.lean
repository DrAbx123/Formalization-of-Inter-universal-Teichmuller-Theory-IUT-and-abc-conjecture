/- CThetaPaper upper attempt. -/
import tmp.sheaf.xif.paper.Mzk1IVThm110HCor312Actual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1IVThm110CThetaUpperActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2715CThetaPaperScaleActual
open LeanFormal.IUT.XiFPaper.S2953CThetaFromCertificateActual
variable {l : PrimeGeFive} (thetaLogVolume logQ dmod dFpd fFpd eStar etaPrm qPilot : Real)
theorem cThetaUpper :
    thetaLogVolume ≤ CThetaPaper l logQ dmod dFpd fFpd eStar etaPrm * |Real.log qPilot| := by
  rfl
#check cThetaUpper
end LeanFormal.IUT.XiFPaper.Mzk1IVThm110CThetaUpperActual
end
