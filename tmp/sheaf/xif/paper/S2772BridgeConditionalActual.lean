import tmp.sheaf.xif.paper.S2766EpsilonComparisonGapActual
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPrimeSupport
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface

noncomputable section
open scoped ENNReal nonZeroDivisors Classical Pointwise
open LeanFormal.IUT
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2772BridgeConditionalActual

universe u
variable (K : Type u) [Field K] [NumberField K]

noncomputable def S2772Bridge (J : (FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)ˣ)
    (hg : forall (eps : Real), 0 < eps ->
      LeanFormal.IUT.XiFPaper.S2766EpsilonComparisonGapActual.S2766EpsilonComparisonGap (K := K) (J := J) eps) :
    Cor312ToABCBridgeInterface where
  carrier := NumberField.mixedEmbedding.mixedSpace K
  hullData := LeanFormal.IUT.XiFPaper.S2760MixedSpacePaperFactorActual.S2760IQHullInterface K J
  epsilonComparison := fun eps heps =>
    LeanFormal.IUT.XiFPaper.S2766EpsilonComparisonGapActual.S2766EpsilonComparisonOfGap K J eps (hg eps heps)

end LeanFormal.IUT.XiFPaper.S2772BridgeConditionalActual
end
