import LeanFormal.IUT.Audit.Status
import tmp.sheaf.xif.paper.S3171IUTIVSection1StatementActual
import tmp.sheaf.xif.paper.S3131Thm110ElementaryLayerReuseActual

/-! # S3171b IUT IV §1: estimates layer rows for Thm 1.10 steps (iii)/(vi) - data only -/

namespace LeanFormal.IUT.XiFPaper.S3171IUTIVSection1EstimatesActual

/-- Estimate-layer mapping: which tree files already supply each Thm 1.10 step's
elementary content (STEP 0: all reused; no re-proof). -/
def S3171Theorem110Estimates : List (String × String × String) :=
  [ ("step (iii) local log-volume computations at v in V_good", "IUTIV/Estimates/Section1.lean:115/119/125/157/172 (Prop 1.7 weighted machinery); ArithmeticDivisorDegree:1214/1221/1225/1310; SourceImageHullVolume:103", "reuse"),
    ("step (iv) indeterminacy bounds (Ind1,2,3 + hull)", "stepxi Indet01/02/03 finite-instance layer; hull: CardAMPL/CardHullReal*; Ind3 upper-semi one-sided", "partial (A35 gap)"),
    ("step (v) FINAL DISPLAY (Theta-pilot log-volume estimate)", "(b) UndilatedHeightBound -> HeightComparisonFamily; (c) UndilatedRegionBound -> RegionVolumeFamily; remaining: uniform height-vs-volume + RegionRelativeToHullAndWeight + weight<=theta", "class B"),
    ("step (vi) weighted averages / (R1)-(R3) splitting estimates", "IUTIV/Estimates/StepVProcessionAverage.lean:35/39/54/68/100/125 -> (R4) only; Section1 Prop 1.7 averages; (R1)-(R3) REMAINING", "partial"),
    ("step (vii) Cor 3.12-shaped conclusion", "S3131CanonicalRootedQC_le_HC + magnitude (GREEN, probe trio)", "proven"),
    ("step (viii) assembly toward ABC via [GenEll]", "GenEll P0 + GenEll05b wiring map + GenEll10H6Closure (interface-level); (ii)=>(i) paper-input", "class B"),
    ("Thm 1.10 elementary estimates e1-e6", "IUTIV/Estimates/ElementaryEstimates.lean:76-146 (reuse file S3131Thm110ElementaryLayerReuseActual)", "reuse"),
    ("epsilon arithmetic / absorption", "GenEll05Theorem21Actual.paper_epsilon_absorption (PROVED); StepVProcessionAverage:68", "proven/reuse") ]

theorem S3171Theorem110Estimates_length : S3171Theorem110Estimates.length = 8 := rfl

def S3171RemainingStepInputs : List String :=
  [ "(R1)-(R3) prime-splitting/rounding estimates (only (R4) supplied by StepV)",
    "uniform height-vs-volume comparison (b) two delta-families",
    "RegionRelativeToHullAndWeight + finite hull/region volume + weight<=theta (c)",
    "full Ind1,2,3 indeterminacy quotients (A35 gap; finite-instance only)",
    "[Mzk1] noncritical Belyi (single named deep input; stage4 statement pending import)" ]

theorem S3171RemainingStepInputs_length : S3171RemainingStepInputs.length = 5 := rfl

#check LeanFormal.IUT.XiFPaper.S3131Thm110ElementaryLayerReuseActual.S3131Thm110ElementaryLayer_length
#check LeanFormal.IUT.XiFPaper.S3171IUTIVSection1StatementActual.S3171Theorem110Steps_length

end LeanFormal.IUT.XiFPaper.S3171IUTIVSection1EstimatesActual
