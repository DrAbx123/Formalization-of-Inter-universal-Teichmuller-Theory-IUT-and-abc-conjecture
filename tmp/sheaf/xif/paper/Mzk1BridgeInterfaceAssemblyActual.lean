import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface

/-! Mainline: bridge-interface assembly from a per-epsilon comparison family (real helper). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1BridgeInterfaceAssemblyActual

open LeanFormal.IUT

universe u

/-- Assemble the bridge interface from carrier, hull interface and a comparison family. -/
def assembleBridgeInterface (X : Type u) (W : IQHullLogVolumeInterface X)
    (C : ∀ (ε : Real) (hε : 0 < ε), Cor312EpsilonArithmeticComparison W ε) :
    Cor312ToABCBridgeInterface.{u} where
  carrier := X
  hullData := W
  epsilonComparison := C

theorem nonempty_bridgeInterface_of_comparisonFamily (X : Type u)
    (W : IQHullLogVolumeInterface X)
    (C : ∀ (ε : Real) (hε : 0 < ε), Cor312EpsilonArithmeticComparison W ε) :
    Nonempty (Cor312ToABCBridgeInterface.{u}) :=
  ⟨assembleBridgeInterface X W C⟩

theorem abcConjecture_of_comparisonFamily (X : Type u)
    (W : IQHullLogVolumeInterface X)
    (C : ∀ (ε : Real) (hε : 0 < ε), Cor312EpsilonArithmeticComparison W ε) :
    ABCConjecture :=
  cor312ToABCBridge_abcConjecture (assembleBridgeInterface X W C)

theorem heightBound_of_comparisonFamily (X : Type u)
    (W : IQHullLogVolumeInterface X)
    (C : ∀ (ε : Real) (hε : 0 < ε), Cor312EpsilonArithmeticComparison W ε) :
    ∀ ε : Real, 0 < ε → ∃ A : Real, ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + ε) * arithmeticWeight (abcRationalPoint a c) + A :=
  cor312ToABCBridge_heightBound (assembleBridgeInterface X W C)

end LeanFormal.IUT.XiFPaper.Mzk1BridgeInterfaceAssemblyActual