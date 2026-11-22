import LeanFormal.IUT.ABCBridge.Bridge.IUTToABC
import LeanFormal.IUT.ABCBridge.Arithmetic.ABCHeightArithmeticWeightComparison

/-! Mainline: additive V2 route consumers to all accepted ABC forms (real compositions). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1V2ToABCTargetActualAdapted

open LeanFormal.IUT

theorem abcConjecture_of_v2 (h : ABCHeightWeightAdditiveBoundV2) :
    ABCConjecture :=
  abcConjecture_iff_ABCHeightWeightAdditiveBoundV2.mpr h

theorem v2_of_abcConjecture (h : ABCConjecture) :
    ABCHeightWeightAdditiveBoundV2 :=
  abcConjecture_iff_ABCHeightWeightAdditiveBoundV2.mp h

theorem abcLogConjecture_of_v2 (h : ABCHeightWeightAdditiveBoundV2) :
    ABCLogConjecture :=
  abcConjecture_iff_abcLogConjecture.mp (abcConjecture_of_v2 h)

theorem abcArithmeticWeightHeightBound_of_v2
    (h : ABCHeightWeightAdditiveBoundV2) :
    ABCArithmeticWeightHeightBound :=
  abcConjecture_iff_abcArithmeticWeightHeightBound.mp (abcConjecture_of_v2 h)

end LeanFormal.IUT.XiFPaper.Mzk1V2ToABCTargetActualAdapted