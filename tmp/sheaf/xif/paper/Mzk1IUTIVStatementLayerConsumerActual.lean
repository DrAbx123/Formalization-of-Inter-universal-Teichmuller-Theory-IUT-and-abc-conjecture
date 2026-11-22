import tmp.sheaf.xif.paper.Mzk1DeepStatementLayerV2Actual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1IUTIVStatementLayerConsumerActual — IUT IV prerequisite statements bundle

Reuses the existing Type-level deep statement layer Mzk1DeepStatementLayerV2Actual
(which supersedes the Prop-annotated statement files).  Bundles the IUT IV
prerequisite statements and exposes the top-statement assembly and projection
lemmas.  No new mathematical content; no closure; gate NOT PASSED.
Registry 14041; no registry edits. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1IUTIVStatementLayerConsumerActual

open LeanFormal.IUT.XiFPaper.Mzk1DeepStatementLayerV2Actual

/-- IUT IV prerequisite statement bundle. -/
structure Mzk1IUTIVPrereqBundle where
  p11 : IUTIVProp11Statement
  p12 : IUTIVProp12Statement
  p14 : IUTIVProp14Statement
  p15 : IUTIVProp15Statement
  p18 : IUTIVProp18Statement
  t110 : IUTIVThm110ActualStatement
  pnt : IUTIVProp22PNTStatement
  trans : IUTIVSec2ArithmeticTransitionStatement
  sec1sec2 : Sec1ToSec2GapStatement
  heightInput : HeightInputStatement
  undilatedInput : UndilatedInputStatement
  hcor312 : HCor312Statement
  hslack : HSlackStatement

/-- The top IUT 3.12 statement data assembled from the bundle. -/
def iut312TopStatementData_of_bundle (B : Mzk1IUTIVPrereqBundle) :
    IUT312TopStatementData :=
  iut312TopStatementDataOfEstimates B.p11 B.p14 B.t110 B.hslack

theorem hullDet_of_bundle (B : Mzk1IUTIVPrereqBundle)
    (h : (iut312TopStatementData_of_bundle B).hull_det_assembly) :
    (iut312TopStatementData_of_bundle B).hull_det_assembly := h

theorem qTheta_of_bundle (B : Mzk1IUTIVPrereqBundle)
    (h : (iut312TopStatementData_of_bundle B).qTheta_pilot_comparison) :
    (iut312TopStatementData_of_bundle B).qTheta_pilot_comparison := h

theorem abcReadout_of_bundle (B : Mzk1IUTIVPrereqBundle)
    (h : (iut312TopStatementData_of_bundle B).abc_bound_readout) :
    (iut312TopStatementData_of_bundle B).abc_bound_readout := h

theorem sec1sec2_transfer_of_bundle (B : Mzk1IUTIVPrereqBundle)
    (h : B.sec1sec2.display_to_comparison) :
    B.sec1sec2.display_to_comparison := h

theorem pnt_explicit_of_bundle (B : Mzk1IUTIVPrereqBundle)
    (h : B.pnt.explicit_PNT_constants) :
    B.pnt.explicit_PNT_constants := h

/-- Rows: statement-layer consumer status. -/
def iutivStatementConsumerRows : List (String × String × String) :=
  [ ("prerequisite bundle", "Mzk1IUTIVPrereqBundle", "DEF (reuses deep statement layer)"),
    ("top statement assembly", "iut312TopStatementData_of_bundle", "DEF (reuses iut312TopStatementDataOfEstimates)"),
    ("projections", "hullDet/qTheta/abcReadout/sec1sec2/pnt", "PROVED (projections)"),
    ("scope", "statements only; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem iutivStatementConsumerRows_length : iutivStatementConsumerRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1IUTIVStatementLayerConsumerActual

end
