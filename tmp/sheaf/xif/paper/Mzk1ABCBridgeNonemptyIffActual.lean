import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface

/-! Mainline: ABC bridge interface nonemptiness <-> ABCConjecture (T1/T2 wiring). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1ABCBridgeNonemptyIffActual

open LeanFormal.IUT

theorem mainline_cor312Interface_nonempty_iff_abcConjecture :
    Nonempty (Cor312ToABCBridgeInterface.{0}) ↔ ABCConjecture :=
  cor312ToABCBridgeInterface_nonempty_iff_abcConjecture

theorem mainline_abcConjecture_of_nonempty
    (h : Nonempty (Cor312ToABCBridgeInterface.{0})) : ABCConjecture :=
  cor312ToABCBridge_abcConjecture h.some

theorem mainline_nonempty_of_abcConjecture
    (h : ABCConjecture) : Nonempty (Cor312ToABCBridgeInterface.{0}) :=
  mainline_cor312Interface_nonempty_iff_abcConjecture.mpr h

end LeanFormal.IUT.XiFPaper.Mzk1ABCBridgeNonemptyIffActual