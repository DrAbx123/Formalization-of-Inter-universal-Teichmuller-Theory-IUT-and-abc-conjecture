import tmp.sheaf.xif.paper.S2836AdditiveBridgeActual
import LeanFormal.IUT.ABCBridge.Arithmetic.ABCHeightArithmeticWeightComparison
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPrimeSupport

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2836AdditiveBridgeActual
open LeanFormal.IUT.XiFPaper.S2833S2800HregionActual
open LeanFormal.IUT.XiFPaper.S2781PointedLineBundleRegionActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000

namespace LeanFormal.IUT.XiFPaper.S2837ABCFromAdditiveHeightActual

/-- Conditional ABC conjecture from the explicit additive height input. -/
theorem S2837_abcConjecture
    (hadd : forall (eps : Real), 0 < eps ->
      exists A : Real, forall a b c : Nat, IsABCTriple a b c ->
        Height.logHeight₁ (abcRationalPoint a c)
          <= (1 + eps) * (S2836W.logVolume
              (normalizedComparisonRegion S2836W (S2781LogShellPoint S2833l) a b c)).toReal
            + A) :
    ABCConjecture :=
  abcConjecture_iff_ABCHeightWeightAdditiveBoundV2.mpr
    (S2836AdditiveBridge hadd)

end LeanFormal.IUT.XiFPaper.S2837ABCFromAdditiveHeightActual
end
