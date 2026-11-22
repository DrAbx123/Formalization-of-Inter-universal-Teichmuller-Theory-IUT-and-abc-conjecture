import LeanFormal.IUT.ABCBridge.Bridge.ABCFrontierReductions
import LeanFormal.IUT.ABCBridge.Bridge.Cor312PointwiseMembershipWeakening
import LeanFormal.IUT.ABCBridge.Arithmetic.ABCHeightArithmeticWeightComparison
import LeanFormal.IUT.ABCBridge.Bridge.IUTToABC

/-! Mainline (T3): frontier consumers to the additive V2 / logarithmic forms
  (new composed conclusions from the proved reductions). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1FrontierFormsChainActual

open LeanFormal.IUT

universe u

theorem v2_of_frontierGapReduced (h : ABCFrontierGapReduced.{u}) :
    ABCHeightWeightAdditiveBoundV2 :=
  abcConjecture_iff_ABCHeightWeightAdditiveBoundV2.mp
    (abcConjecture_of_frontierGapReduced h)

theorem logConjecture_of_frontierGapReduced (h : ABCFrontierGapReduced.{u}) :
    ABCLogConjecture :=
  abcConjecture_iff_abcLogConjecture.mp (abcConjecture_of_frontierGapReduced h)

theorem v2_of_frontierPointwiseWeakened
    (h : ABCFrontierPointwiseWeakened.{u}) : ABCHeightWeightAdditiveBoundV2 :=
  abcConjecture_iff_ABCHeightWeightAdditiveBoundV2.mp
    (abcConjecture_of_frontierPointwiseWeakened h)

end LeanFormal.IUT.XiFPaper.Mzk1FrontierFormsChainActual