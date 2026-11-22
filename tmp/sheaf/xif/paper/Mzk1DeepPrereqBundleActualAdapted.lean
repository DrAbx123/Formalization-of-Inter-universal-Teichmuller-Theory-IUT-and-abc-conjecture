import tmp.sheaf.xif.paper.Mzk1DeepStatementLayerV2ActualAdapted

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1DeepPrereqBundleActualAdapted (adapted copy, A475 reuse) — deep prerequisite bundle (reuse statement layer)

Reuses Mzk1DeepStatementLayerV2ActualAdapted (Type-level deep statement layer) to bundle
all prerequisite-object statements relevant to the IUT 3.12 target sentence.  Public
projections and the IUT312TopStatementData assembly are exposed; no proof of any
named paper object is claimed.  No closure; gate NOT PASSED; registry 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1DeepPrereqBundleActualAdapted

open LeanFormal.IUT.XiFPaper.Mzk1DeepStatementLayerV2ActualAdapted

/-- Bundle of all deep prerequisite statements, reusing the Type-level layer. -/
structure Mzk1DeepPrereqBundle where
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
  etth02 : EtTh02DeepInputs
  etth11 : EtTh11Rows567
  absIII : AbsTopIII58_55Statement
  qpilot : QPilotPreciseConstructionStatement
  thetaIQ : ThetaPilotIQContainmentStatement
  section0 : Section0SaturatedTheoryStatement
  classB : ClassBRealizationRows
  sources : Sources1995_2015Inputs
  hcor312 : HCor312Statement
  hslack : HSlackStatement
  gapSupply : Cor312GapSupplyData

/-- The IUT 3.12 top statement data assembled from the deep bundle. -/
def iut312TopStatementData_of_deepBundle (B : Mzk1DeepPrereqBundle) :
    IUT312TopStatementData :=
  iut312TopStatementDataOfEstimates B.p11 B.p14 B.t110 B.hslack

theorem deepBundle_hullDet (B : Mzk1DeepPrereqBundle) :
    (iut312TopStatementData_of_deepBundle B).hull_det_assembly :=
  (iut312TopStatementData_of_deepBundle B).hull_det_assembly

theorem deepBundle_qTheta (B : Mzk1DeepPrereqBundle) :
    (iut312TopStatementData_of_deepBundle B).qTheta_pilot_comparison :=
  (iut312TopStatementData_of_deepBundle B).qTheta_pilot_comparison

theorem deepBundle_abcReadout (B : Mzk1DeepPrereqBundle) :
    (iut312TopStatementData_of_deepBundle B).abc_bound_readout :=
  (iut312TopStatementData_of_deepBundle B).abc_bound_readout

theorem deepBundle_qpilot_object (B : Mzk1DeepPrereqBundle) :
    B.qpilot.qPilot_object :=
  qPilotPrecise_object B.qpilot

theorem deepBundle_thetaPilot_containment (B : Mzk1DeepPrereqBundle) :
    B.thetaIQ.thetaPilot_iq_containment :=
  thetaPilotIQ B.thetaIQ

theorem deepBundle_sec1sec2 (B : Mzk1DeepPrereqBundle) :
    B.sec1sec2.display_to_comparison :=
  sec1_sec2_transfer B.sec1sec2

def deepPrereqRows : List (String × String × String) :=
  [ ("deep bundle", "Mzk1DeepPrereqBundle", "DEF (reuses Type-level statement layer)"),
    ("top statement", "iut312TopStatementData_of_deepBundle", "DEF (reuses assembly)"),
    ("projections", "hullDet/qTheta/abcReadout/qpilot/thetaPilot/sec1sec2", "PROVED"),
    ("scope", "statements only; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem deepPrereqRows_length : deepPrereqRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1DeepPrereqBundleActualAdapted

end
