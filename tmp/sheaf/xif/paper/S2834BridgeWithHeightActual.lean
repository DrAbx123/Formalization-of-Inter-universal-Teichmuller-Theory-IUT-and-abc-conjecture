import tmp.sheaf.xif.paper.S2833S2800HregionActual
import tmp.sheaf.xif.paper.S2800LineBundleCor312BridgeActual
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPrimeSupport

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2800LineBundleCor312BridgeActual
open LeanFormal.IUT.XiFPaper.S2833S2800HregionActual
open LeanFormal.IUT.XiFPaper.S2808S2800HalfNormalizedActual
open LeanFormal.IUT.XiFPaper.S2781PointedLineBundleRegionActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2834BridgeWithHeightActual

noncomputable def S2834Bridge
    (hheight : forall (eps : Real), 0 < eps ->
      forall a b c : Nat, IsABCTriple a b c ->
        Height.logHeight₁ (abcRationalPoint a c)
          <= (1 + eps) * ((S2808HalfIQHull S2833l 1).logVolume
              (normalizedComparisonRegion (S2808HalfIQHull S2833l 1)
                (S2781LogShellPoint S2833l) a b c)).toReal) :
    Cor312ToABCBridgeInterface :=
  S2800Bridge S2833l (S2808Global S2833l) (fun eps heps =>
    S2833EpsData eps (le_of_lt heps) (hheight eps heps))

/-- The assembled bridge gives the ABC height bound, with only the explicit
height gap as input. -/
theorem S2834_heightBound
    (hheight : forall (eps : Real), 0 < eps ->
      forall a b c : Nat, IsABCTriple a b c ->
        Height.logHeight₁ (abcRationalPoint a c)
          <= (1 + eps) * ((S2808HalfIQHull S2833l 1).logVolume
              (normalizedComparisonRegion (S2808HalfIQHull S2833l 1)
                (S2781LogShellPoint S2833l) a b c)).toReal) :
    forall epsilon : Real, 0 < epsilon -> exists A : Real,
      forall a b c : Nat, IsABCTriple a b c ->
        Height.logHeight₁ (abcRationalPoint a c)
          <= (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + A :=
  cor312ToABCBridge_heightBound (S2834Bridge hheight)


/-- Conditional ABC conjecture from the assembled bridge and the single
explicit height gap. -/
theorem S2834_abcConjecture
    (hheight : forall (eps : Real), 0 < eps ->
      forall a b c : Nat, IsABCTriple a b c ->
        Height.logHeight₁ (abcRationalPoint a c)
          <= (1 + eps) * ((S2808HalfIQHull S2833l 1).logVolume
              (normalizedComparisonRegion (S2808HalfIQHull S2833l 1)
                (S2781LogShellPoint S2833l) a b c)).toReal) :
    ABCConjecture :=
  cor312ToABCBridge_abcConjecture (S2834Bridge hheight)


end LeanFormal.IUT.XiFPaper.S2834BridgeWithHeightActual
end
