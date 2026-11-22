import tmp.sheaf.xif.paper.S2752FinalHweightvolActual
import tmp.sheaf.xif.paper.ArithmeticLineBundleActual
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPrimeSupport

noncomputable section
open scoped ENNReal nonZeroDivisors
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaperArithmeticLineBundle
open LeanFormal.IUT.XiFPaper.S2735QPilotLineBundleActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2800LineBundleCor312BridgeActual

abbrev S2800Carrier (l : PrimeGeFive) : Type :=
  (SourceLineBundle (A := S2735Arithmetic l))ˣ

def S2800LogVolume (l : PrimeGeFive)
    (covolume : S2800Carrier l -> Real) (S : Set (S2800Carrier l)) : ENNReal :=
  ⨆ y : S, ENNReal.ofReal ((1 / 2) * covolume y.1)

structure S2800GlobalData (l : PrimeGeFive) where
  covolume : S2800Carrier l -> Real
  W : IQHullLogVolumeInterface (S2800Carrier l)
  logShellPoint : Nat -> Nat -> Nat -> S2800Carrier l
  W_logVolume_eq : forall S : Set (S2800Carrier l),
    W.logVolume S = S2800LogVolume l covolume S

structure S2800EpsData (l : PrimeGeFive) (G : S2800GlobalData l) (eps : Real) where
  hregion : exists D : Real, forall a b c : Nat, IsABCTriple a b c ->
    (G.W.logVolume (normalizedComparisonRegion G.W G.logShellPoint a b c)).toReal
      <= (1 + eps) * arithmeticWeight (abcRationalPoint a c)
        + (G.W.logVolume G.W.hull).toReal + D
  hheight : forall a b c : Nat, IsABCTriple a b c ->
    Height.logHeight₁ (abcRationalPoint a c)
      <= (1 + eps) * (G.W.logVolume
          (normalizedComparisonRegion G.W G.logShellPoint a b c)).toReal

noncomputable def S2800EpsilonComparison (l : PrimeGeFive) (G : S2800GlobalData l)
    (eps : Real) (B : S2800EpsData l G eps) :
    Cor312EpsilonArithmeticComparison G.W eps where
  logShellPoint := G.logShellPoint
  height_le_normalizedRegionVolume := B.hheight
  regionVolume_le_normalizedWeight := B.hregion

noncomputable def S2800Bridge (l : PrimeGeFive) (G : S2800GlobalData l)
    (hg : forall eps : Real, 0 < eps -> S2800EpsData l G eps) :
    Cor312ToABCBridgeInterface where
  carrier := S2800Carrier l
  hullData := G.W
  epsilonComparison := fun eps heps =>
    S2800EpsilonComparison l G eps (hg eps heps)

end LeanFormal.IUT.XiFPaper.S2800LineBundleCor312BridgeActual
end
