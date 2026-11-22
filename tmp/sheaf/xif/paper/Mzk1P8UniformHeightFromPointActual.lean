import tmp.sheaf.xif.paper.Mzk1P8PointHeightCriterionActual
import tmp.sheaf.xif.paper.Mzk1P8ActualDisplayHeightActual
import tmp.sheaf.xif.paper.Mzk1P8UniformHeightActual
import Mathlib.Tactic
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1P8PointHeightCriterionActual
open LeanFormal.IUT.XiFPaper.Mzk1P8ActualDisplayHeightActual
open LeanFormal.IUT.XiFPaper.Mzk1P8UniformHeightActual
namespace LeanFormal.IUT.XiFPaper.Mzk1P8UniformHeightFromPointActual
theorem p8_uniformHeightBound_of_pointCriterion (h : P8PointHeightCriterion) :
    P8UniformHeightBound :=
  (p8_pointHeightCriterion_iff_freyJ).mp h
theorem p8_abc_of_pointCriterion (h : P8PointHeightCriterion) : ABCConjecture :=
  p8UniformHeight_consumer (p8_uniformHeightBound_of_pointCriterion h)
#print axioms p8_abc_of_pointCriterion
end LeanFormal.IUT.XiFPaper.Mzk1P8UniformHeightFromPointActual
end