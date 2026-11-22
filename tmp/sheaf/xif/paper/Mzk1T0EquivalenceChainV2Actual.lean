import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
import LeanFormal.IUT.ABCBridge.Arithmetic.ABCHeightArithmeticWeightComparison
import LeanFormal.IUT.ABCBridge.Bridge.IUTToABC

/-! Mainline: T0 equivalence chain (V2: explicit directions avoid reducible-def
  unfolding friction in `Iff.trans`). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1T0EquivalenceChainV2Actual

open LeanFormal.IUT

theorem nonempty_iff_abcArithmeticWeightHeightBound :
    Nonempty (Cor312ToABCBridgeInterface.{0}) ↔ (∀ epsilon : Real, 0 < epsilon → ∃ A : Real, ∀ a b c : Nat, IsABCTriple a b c → Height.logHeight₁ (abcRationalPoint a c) ≤ (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + A) :=
  ⟨fun h => abcConjecture_iff_abcArithmeticWeightHeightBound.mp
      (cor312ToABCBridgeInterface_nonempty_iff_abcConjecture.mp h),
   fun h => cor312ToABCBridgeInterface_nonempty_iff_abcConjecture.mpr
      (abcConjecture_iff_abcArithmeticWeightHeightBound.mpr h)⟩

theorem nonempty_iff_additiveV2 :
    Nonempty (Cor312ToABCBridgeInterface.{0}) ↔ ABCHeightWeightAdditiveBoundV2 :=
  ⟨fun h => abcConjecture_iff_ABCHeightWeightAdditiveBoundV2.mp
      (cor312ToABCBridgeInterface_nonempty_iff_abcConjecture.mp h),
   fun h => cor312ToABCBridgeInterface_nonempty_iff_abcConjecture.mpr
      (abcConjecture_iff_ABCHeightWeightAdditiveBoundV2.mpr h)⟩

theorem nonempty_iff_abcLog :
    Nonempty (Cor312ToABCBridgeInterface.{0}) ↔ ABCLogConjecture :=
  ⟨fun h => abcConjecture_iff_abcLogConjecture.mp
      (cor312ToABCBridgeInterface_nonempty_iff_abcConjecture.mp h),
   fun h => cor312ToABCBridgeInterface_nonempty_iff_abcConjecture.mpr
      (abcConjecture_iff_abcLogConjecture.mpr h)⟩

end LeanFormal.IUT.XiFPaper.Mzk1T0EquivalenceChainV2Actual