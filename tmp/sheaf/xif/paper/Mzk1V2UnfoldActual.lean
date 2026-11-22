import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
import LeanFormal.IUT.ABCBridge.Arithmetic.ABCHeightArithmeticWeightComparison

/-! Mainline: additive V2 unfolding + interface <-> V2 linkage. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1V2UnfoldActual

open LeanFormal.IUT

theorem additiveV2_unfold :
    ABCHeightWeightAdditiveBoundV2 ↔
      ∀ (epsilon : Real), 0 < epsilon → ∃ A : Real,
        ∀ a b c : Nat, IsABCTriple a b c →
          Height.logHeight₁ (abcRationalPoint a c) ≤
            (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + A :=
  Iff.rfl

theorem additiveV2_of_interface (D : Cor312ToABCBridgeInterface.{0}) :
    ABCHeightWeightAdditiveBoundV2 :=
  abcConjecture_iff_ABCHeightWeightAdditiveBoundV2.mp
    (cor312ToABCBridge_abcConjecture D)

theorem interface_of_additiveV2 (h : ABCHeightWeightAdditiveBoundV2) :
    Nonempty (Cor312ToABCBridgeInterface.{0}) :=
  cor312ToABCBridgeInterface_nonempty_iff_abcConjecture.mpr
    (abcConjecture_iff_ABCHeightWeightAdditiveBoundV2.mpr h)

end LeanFormal.IUT.XiFPaper.Mzk1V2UnfoldActual