import tmp.sheaf.xif.paper.Mzk1P8PointHeightCriterionActual
import LeanFormal.IUT.ABCBridge.Bridge.ABCEllipticHeightCriterion
import Mathlib.Tactic
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1P8PointHeightCriterionActual
namespace LeanFormal.IUT.XiFPaper.Mzk1P8PointHeightProducerFinal
/-- Uniform Frey j-height criterion gives the uniform ABC point-height criterion. -/
def p8PointHeightProducerFinal (h : ABCFreyJProductHeightCriterion) :
    P8PointHeightCriterion :=
  p8_pointHeightCriterion_iff_freyJ.mpr h
theorem p8PointHeightProducerFinal_nonempty
    (h : ABCFreyJProductHeightCriterion) : Nonempty P8PointHeightCriterion :=
  ⟨p8PointHeightProducerFinal h⟩
end LeanFormal.IUT.XiFPaper.Mzk1P8PointHeightProducerFinal
end