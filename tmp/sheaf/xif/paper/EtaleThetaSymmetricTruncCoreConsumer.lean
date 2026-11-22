import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing
import tmp.sheaf.xif.paper.EtaleThetaSymmetricTruncZeroActual
import tmp.sheaf.xif.paper.EtaleThetaSymmetricTruncSupportActual
import tmp.sheaf.xif.paper.EtaleThetaCoeffAtNonnegActual

noncomputable section

namespace LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncCoreConsumer

universe u

theorem symmetricTrunc_zero_consumer (K : Type u) [Field K] :
    LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncZeroActual.etaleThetaSymmetricTrunc K 0 =
      LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncZeroActual.thetaPairTerm K 0 :=
  LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncZeroActual.etaleThetaSymmetricTrunc_zero K

theorem thetaPairTerm_support_consumer (K : Type u) [Field K] (n : Int) :
    (LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSupportActual.thetaPairTerm K n).support ⊆
      ({LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing.thetaQExponent n} : Set Rat) :=
  LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSupportActual.thetaPairTerm_support K n

theorem thetaQExponent_nonneg_consumer {n : Int} (h : 0 <= n) :
    0 <= LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing.thetaQExponent n :=
  LeanFormal.IUT.XiFPaper.EtaleThetaCoeffAtNonnegActual.thetaQExponent_nonneg h

#check symmetricTrunc_zero_consumer
#check thetaPairTerm_support_consumer
#check thetaQExponent_nonneg_consumer

end LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncCoreConsumer
