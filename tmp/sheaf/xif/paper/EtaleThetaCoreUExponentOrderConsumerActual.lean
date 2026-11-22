import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaCoreUExponentGrowthActual
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaCoreUExponentOrderConsumerActual

theorem thetaUExponent_lt_of_lt {n m : Int} (h : n < m) :
    LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing.thetaUExponent n <
      LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing.thetaUExponent m :=
  LeanFormal.IUT.XiFPaper.EtaleThetaCoreUExponentGrowthActual.thetaUExponent_strictMono h

theorem thetaUExponent_involution_lt_of_lt {n m : Int} (h : n < m) :
    LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing.thetaUExponent (-m - 1) <
      LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing.thetaUExponent (-n - 1) :=
  LeanFormal.IUT.XiFPaper.EtaleThetaCoreUExponentGrowthActual.thetaUExponent_strictAnti h

#check thetaUExponent_lt_of_lt
#check thetaUExponent_involution_lt_of_lt

end LeanFormal.IUT.XiFPaper.EtaleThetaCoreUExponentOrderConsumerActual
