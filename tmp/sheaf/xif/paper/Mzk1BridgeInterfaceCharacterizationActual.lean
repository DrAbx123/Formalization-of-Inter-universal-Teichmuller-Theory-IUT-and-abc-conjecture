import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface

/-! Mainline (T1): structural characterization of the bridge interface as an explicit
  carrier + hull data + per-epsilon comparison family (new iff, real proof). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1BridgeInterfaceCharacterizationActual

open LeanFormal.IUT

universe u

theorem nonempty_bridgeInterface_iff_exists_comparisonFamily :
    Nonempty (Cor312ToABCBridgeInterface.{u}) ↔
      ∃ (X : Type u) (W : IQHullLogVolumeInterface X),
        Nonempty (∀ epsilon : Real, 0 < epsilon →
          Cor312EpsilonArithmeticComparison W epsilon) := by
  constructor
  · rintro ⟨D⟩
    exact ⟨D.carrier, D.hullData, ⟨D.epsilonComparison⟩⟩
  · rintro ⟨X, W, ⟨C⟩⟩
    exact ⟨{ carrier := X, hullData := W, epsilonComparison := C }⟩

def comparisonFamily_of_bridgeInterface (D : Cor312ToABCBridgeInterface.{u}) :
    ∀ epsilon : Real, 0 < epsilon →
      Cor312EpsilonArithmeticComparison D.hullData epsilon :=
  D.epsilonComparison

end LeanFormal.IUT.XiFPaper.Mzk1BridgeInterfaceCharacterizationActual