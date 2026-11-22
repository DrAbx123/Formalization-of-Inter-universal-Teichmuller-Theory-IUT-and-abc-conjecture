/- P8 uniform-height input: the exact remaining input is the additive height
bound P8P6IVInequalityInput (equivalent to ABC); the Frey producer implies it. -/
import tmp.sheaf.xif.paper.Mzk1P8FromP6IVInequalityActual
import tmp.sheaf.xif.paper.Mzk1G1FreyHeightActual
import tmp.sheaf.xif.paper.Mzk1G1EllipticHeightCriterionActual
import tmp.sheaf.xif.paper.ABCStatementBridgeActual
import tmp.sheaf.xif.paper.Mzk1P8ActualDisplayHeightActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.P8UniformHeightInputActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1G1Actual
open LeanFormal.IUT.XiFPaper.Mzk1P8ActualDisplayHeightActual
open LeanFormal.IUT.XiFPaper.Mzk1P8FromP6IVInequalityActual
open LeanFormal.IUT.XiFPaper.ABCStatementBridgeActual

abbrev P8UniformHeightInput : Prop := P8P6IVInequalityInput
abbrev P8FreyProducer : Prop := ∀ ε : Real, 0 < ε → Nonempty (FreyHeightBound ε)

theorem p8UniformHeightInput_implies_ABC
    (h : P8UniformHeightInput) : ABCConjecture :=
  abcConjecture_of_p6IVInequality h

theorem p8UniformHeightInput_implies_bound
    (h : P8UniformHeightInput) : P8UniformHeightBound :=
  p8UniformHeightBound_of_p6IVInequality h

theorem p8Producer_implies_input (h : P8FreyProducer) : P8UniformHeightInput :=
  (LeanFormal.IUT.abcConjecture_iff_abcArithmeticWeightHeightBound).mp
    (ABCStatementBridgeActual.abcStatement_to_ABCConjecture
      (abcStatement_of_ellipticHeightCriterion
        (freyHeightBoundAll_iff_criterionAll.mp h)))

theorem p8Producer_implies_bound_via_input (h : P8FreyProducer) :
    P8UniformHeightBound :=
  p8UniformHeightInput_implies_bound (p8Producer_implies_input h)

theorem p8Input_iff_ABC : P8UniformHeightInput ↔ ABCConjecture :=
  (LeanFormal.IUT.abcConjecture_iff_abcArithmeticWeightHeightBound).symm

#print axioms p8UniformHeightInput_implies_ABC
#print axioms p8Producer_implies_input
#print axioms p8Input_iff_ABC

end LeanFormal.IUT.XiFPaper.P8UniformHeightInputActual
end
