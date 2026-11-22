import tmp.sheaf.xif.paper.S2836AdditiveBridgeActual
import LeanFormal.IUT.ABCBridge.Arithmetic.ABCInvariantHeight
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPrimeSupport
import LeanFormal.IUT.ABCBridge.Geometry.FreyTateParameterComparison

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2792NormalizedLineBundleBridge
open LeanFormal.IUT.XiFPaper.S2836AdditiveBridgeActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000

namespace LeanFormal.IUT.XiFPaper.S2838HeightComparisonReductionActual

/-- The exact IUT IV theta/J upper estimate needed for the height comparison:
the J-invariant height is bounded by a constant times the (line-bundle)
region volume plus an additive error.  This is the C_Theta upper estimate
object; it is NOT derived from the carrier fields. -/
def S2838ThetaUpperGap (eps AJ : Real) : Prop :=
  forall a b c : Nat, IsABCTriple a b c ->
    Height.logHeight₁ (abcJInvariant a b c)
      <= 6 * (1 + eps) * S2792RegionVolume a b c + AJ

/-- Actual J-invariant height comparison from ABCInvariantHeight: the ABC point
height is controlled by the J-invariant height with explicit constants. -/
theorem S2838_height_le_Jlog (a b c : Nat) (habc : IsABCTriple a b c) :
    6 * Height.logHeight₁ (abcRationalPoint a c) + Real.log (27 / 64 : Real)
      <= Height.logHeight₁ (abcJInvariant a b c) :=
  (abcJInvariant_logHeight_bounds_abcRationalPoint habc).1

/-- Actual reduction: theta/J upper gap gives the additive height/region
comparison (IUT IV Theorem A shape), hence feeds S2836/S2837. -/
theorem S2838_additiveHeightComparison_of_thetaGap
    (eps AJ : Real) (hgap : S2838ThetaUpperGap eps AJ) :
    forall a b c : Nat, IsABCTriple a b c ->
      Height.logHeight₁ (abcRationalPoint a c)
        <= (1 + eps) * S2792RegionVolume a b c
          + (AJ / 6 - Real.log (27 / 64 : Real) / 6) := by
  intro a b c habc
  have hJ := S2838_height_le_Jlog a b c habc
  have hg := hgap a b c habc
  linarith

end LeanFormal.IUT.XiFPaper.S2838HeightComparisonReductionActual
end
