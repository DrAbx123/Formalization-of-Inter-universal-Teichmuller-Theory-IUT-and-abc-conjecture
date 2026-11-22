import LeanFormal.IUT.ABCBridge.Bridge.ABCFrontierReductions
import LeanFormal.IUT.ABCBridge.Bridge.Cor312PointwiseMembershipWeakening
import LeanFormal.IUT.ABCBridge.Arithmetic.ABCHeightArithmeticWeightComparison
import LeanFormal.IUT.ABCBridge.Bridge.IUTToABC

/-! Mainline (T3): frontier forms packaged with all accepted ABC forms and bridge
  inhabitation in one composed conclusion (T0-T6 main chain package). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1FrontierPackageActual

open LeanFormal.IUT

universe u

theorem frontierPackage_of_gapReduced (h : ABCFrontierGapReduced.{u}) :
    ABCConjecture ∧ ABCLogConjecture ∧ (∀ epsilon : Real, 0 < epsilon → ∃ A : Real, ∀ a b c : Nat, IsABCTriple a b c → Height.logHeight₁ (abcRationalPoint a c) ≤ (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + A) ∧
      ABCHeightWeightAdditiveBoundV2 ∧ Nonempty (Cor312ToABCBridgeInterface.{u}) := by
  have habc : ABCConjecture := abcConjecture_of_frontierGapReduced h
  exact ⟨habc,
    abcConjecture_iff_abcLogConjecture.mp habc,
    abcConjecture_iff_abcArithmeticWeightHeightBound.mp habc,
    abcConjecture_iff_ABCHeightWeightAdditiveBoundV2.mp habc,
    ⟨bridgeInterface_of_frontierGapReduced h⟩⟩

theorem frontierPackage_of_pointwiseWeakened
    (h : ABCFrontierPointwiseWeakened.{u}) :
    ABCConjecture ∧ ABCHeightWeightAdditiveBoundV2 ∧
      Nonempty (Cor312ToABCBridgeInterface.{u}) := by
  have habc : ABCConjecture := abcConjecture_of_frontierPointwiseWeakened h
  exact ⟨habc,
    abcConjecture_iff_ABCHeightWeightAdditiveBoundV2.mp habc,
    ⟨bridgeInterface_of_frontierPointwiseWeakened h⟩⟩

end LeanFormal.IUT.XiFPaper.Mzk1FrontierPackageActual