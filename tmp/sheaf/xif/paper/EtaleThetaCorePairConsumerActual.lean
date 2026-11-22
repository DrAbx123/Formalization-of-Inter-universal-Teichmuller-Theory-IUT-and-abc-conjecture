import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaCoreCoeffAtPairSymmetryActual
import tmp.sheaf.xif.paper.EtaleThetaCoreUExponentGrowthActual

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaCorePairConsumerActual

universe u

theorem thetaCoeffAt_pair_consumer (K : Type u) [Field K] (n : Int) :
    LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffAtPairSymmetryActual.thetaCoeffAt K (-n - 1) =
      LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffAtPairSymmetryActual.thetaCoeffAt K n :=
  LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffAtPairSymmetryActual.thetaCoeffAt_pair K n

theorem thetaUExponent_strictMono_consumer :
    StrictMono LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing.thetaUExponent :=
  LeanFormal.IUT.XiFPaper.EtaleThetaCoreUExponentGrowthActual.thetaUExponent_strictMono

theorem thetaUExponent_strictAnti_consumer :
    StrictAnti (fun n : Int =>
      LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing.thetaUExponent (-n - 1)) :=
  LeanFormal.IUT.XiFPaper.EtaleThetaCoreUExponentGrowthActual.thetaUExponent_strictAnti

theorem thetaUExponent_pair_consumer :
    StrictMono LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing.thetaUExponent ∧
      StrictAnti (fun n : Int =>
        LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing.thetaUExponent (-n - 1)) :=
  ⟨thetaUExponent_strictMono_consumer, thetaUExponent_strictAnti_consumer⟩

#check thetaCoeffAt_pair_consumer
#check thetaUExponent_pair_consumer

end LeanFormal.IUT.XiFPaper.EtaleThetaCorePairConsumerActual
