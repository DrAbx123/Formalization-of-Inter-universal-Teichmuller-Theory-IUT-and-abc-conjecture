import tmp.sheaf.xif.paper.Mzk1P8FreyHeightFromPointActual
import tmp.sheaf.xif.paper.Mzk1G1EllipticHeightCriterionActual
import Mathlib.Tactic
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1P8PointHeightCriterionActual
open LeanFormal.IUT.XiFPaper.Mzk1P8FreyHeightFromPointActual
open LeanFormal.IUT.XiFPaper.Mzk1G1Actual
namespace LeanFormal.IUT.XiFPaper.Mzk1P8CriterionAllFromPointActual
theorem p8_criterionAll_of_pointCriterion (h : P8PointHeightCriterion) :
    ABCEllipticHeightCriterionAll :=
  criterionAll_of_freyHeight (p8_freyHeightBound_of_pointCriterion h)
#print axioms p8_criterionAll_of_pointCriterion
end LeanFormal.IUT.XiFPaper.Mzk1P8CriterionAllFromPointActual
end