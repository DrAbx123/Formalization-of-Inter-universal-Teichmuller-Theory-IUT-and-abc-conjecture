import LeanFormal.IUT.ABCBridge.Bridge.IUTToABC
import LeanFormal.IUT.ABCBridge.Arithmetic.ABCHeightArithmeticWeightComparison

/-! Mainline: TargetABC height/weight shape (paper ABC target) and its equivalences. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1TargetABCShapeActualAdapted

open LeanFormal.IUT

/-- Paper-target shape: the arithmetic-weight-height bound (IUT IV final form). -/
def TargetABCHeightWeight : Prop :=
  ABCArithmeticWeightHeightBound

/-- The paper-target shape is equivalent to ABCConjecture (tree equivalence). -/
theorem targetABC_iff_abcConjecture :
    TargetABCHeightWeight ↔ ABCConjecture :=
  abcConjecture_iff_abcArithmeticWeightHeightBound.symm

/-- The additive V2 contract is the same height/weight shape. -/
theorem v2_iff_targetABC :
    ABCHeightWeightAdditiveBoundV2 ↔ TargetABCHeightWeight :=
  abcConjecture_iff_ABCHeightWeightAdditiveBoundV2.symm.trans
    abcConjecture_iff_abcArithmeticWeightHeightBound

/-- TargetABC (height/weight) follows from V2. -/
theorem targetABC_of_v2 (h : ABCHeightWeightAdditiveBoundV2) :
    TargetABCHeightWeight :=
  v2_iff_targetABC.mp h

/-- And conversely. -/
theorem v2_of_targetABC (h : TargetABCHeightWeight) :
    ABCHeightWeightAdditiveBoundV2 :=
  v2_iff_targetABC.mpr h

end LeanFormal.IUT.XiFPaper.Mzk1TargetABCShapeActualAdapted