import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
import LeanFormal.IUT.ABCBridge.Arithmetic.ABCHeightArithmeticWeightComparison
import LeanFormal.IUT.ABCBridge.Bridge.IUTToABC

/-! Mainline: T0 equivalence chain (composed tree equivalences). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1T0EquivalenceChainActualAdapted

open LeanFormal.IUT

theorem nonempty_iff_abcArithmeticWeightHeightBound :
    Nonempty (Cor312ToABCBridgeInterface.{0}) ↔ ABCArithmeticWeightHeightBound :=
  cor312ToABCBridgeInterface_nonempty_iff_abcConjecture.trans
    abcConjecture_iff_abcArithmeticWeightHeightBound

theorem nonempty_iff_additiveV2 :
    Nonempty (Cor312ToABCBridgeInterface.{0}) ↔ ABCHeightWeightAdditiveBoundV2 :=
  cor312ToABCBridgeInterface_nonempty_iff_abcConjecture.trans
    abcConjecture_iff_ABCHeightWeightAdditiveBoundV2

theorem nonempty_iff_abcLog :
    Nonempty (Cor312ToABCBridgeInterface.{0}) ↔ ABCLogConjecture :=
  cor312ToABCBridgeInterface_nonempty_iff_abcConjecture.trans
    abcConjecture_iff_abcLogConjecture

end LeanFormal.IUT.XiFPaper.Mzk1T0EquivalenceChainActualAdapted