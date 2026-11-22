import tmp.sheaf.xif.paper.Mzk1P8CriterionAllFromPointActual
import tmp.sheaf.xif.paper.ABCStatementBridgeActual
import Mathlib.Tactic
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1P8PointHeightCriterionActual
open LeanFormal.IUT.XiFPaper.Mzk1P8CriterionAllFromPointActual
open LeanFormal.IUT.XiFPaper.Mzk1G1Actual
open LeanFormal.IUT.XiFPaper.ABCStatementBridgeActual
namespace LeanFormal.IUT.XiFPaper.Mzk1P8ABCFromPointActual
theorem p8_abcStatement_of_pointCriterion (h : P8PointHeightCriterion) :
    ABCStatement :=
  abcStatement_of_ellipticHeightCriterion (p8_criterionAll_of_pointCriterion h)
theorem p8_abcConjecture_of_pointCriterion (h : P8PointHeightCriterion) :
    ABCConjecture :=
  abcStatement_iff_ABCConjecture.mp (p8_abcStatement_of_pointCriterion h)
#print axioms p8_abcConjecture_of_pointCriterion
end LeanFormal.IUT.XiFPaper.Mzk1P8ABCFromPointActual
end