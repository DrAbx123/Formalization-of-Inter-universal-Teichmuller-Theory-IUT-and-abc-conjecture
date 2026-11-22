import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing

namespace LeanFormal.IUT.XiFPaper.EtaleThetaCoreUExponentGrowthActual

theorem thetaUExponent_strictMono : StrictMono thetaUExponent := by
  intro n m h
  unfold thetaUExponent
  omega

theorem thetaUExponent_injective : Function.Injective thetaUExponent := by
  intro n m h
  unfold thetaUExponent at h
  omega

theorem thetaUExponent_strictAnti :
    StrictAnti (fun n : Int => thetaUExponent (-n - 1)) := by
  intro n m h
  unfold thetaUExponent
  nlinarith

#check thetaUExponent_strictMono
#check thetaUExponent_injective
#check thetaUExponent_strictAnti

end LeanFormal.IUT.XiFPaper.EtaleThetaCoreUExponentGrowthActual
