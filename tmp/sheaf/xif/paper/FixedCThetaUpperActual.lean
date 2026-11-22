/- Fixed actual CTheta upper from the paper parameter source. -/
import tmp.sheaf.xif.paper.PaperCThetaBindingActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.FixedCThetaUpperActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.PaperCThetaBindingActual
/-- Paper CTheta upper from the actual bound B.  The inequality
B <= paperCTheta * qAbs is the remaining actual numeric/source comparison. -/
theorem fixedCThetaUpper_of_bound {a b c : Nat} (P : PaperParamSource a b c)
    (thetaLogVolume qAbs B : Real)
    (hTheta : thetaLogVolume ≤ B)
    (hB : B ≤ paperCTheta P * qAbs) :
    thetaLogVolume ≤ paperCTheta P * qAbs :=
  le_trans hTheta hB
#check fixedCThetaUpper_of_bound
end LeanFormal.IUT.XiFPaper.FixedCThetaUpperActual
end
