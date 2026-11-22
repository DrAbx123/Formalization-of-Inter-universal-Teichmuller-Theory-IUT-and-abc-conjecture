import LeanFormal.IUT.Audit.Status
import tmp.sheaf.xif.paper.S3131PaperRouteHeightReductionActual
import tmp.sheaf.xif.paper.S3131PaperRouteRegionReductionActual
import tmp.sheaf.xif.paper.S3131PaperRouteFieldStatementsActual

/-! # S3171 IUT IV §1: Theorem 1.10 (Log-volume Estimates for Θ-Pilot Objects) statement layer

IUT IV §1 = 'Log-volume Estimates' (corpus l.38); Thm 1.10 at corpus l.1255, proof steps
(i)-(viii), final display in Step (v). This file states the theorem with our existing
objects and records the obligation class of each step; the final display is wired to
(b) `UndilatedHeightBound -> HeightComparisonFamily` and
(c) `UndilatedRegionBound -> RegionVolumeFamily`. No closure claims. -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S3171IUTIVSection1StatementActual

universe u

open LeanFormal.IUT.XiFPaper.S3131PaperRouteHeightReductionActual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteRegionReductionActual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteFieldStatementsActual

/-- Statement objects of Thm 1.10 mapped to our definitions (paper object -> ours -> status). -/
def S3171Theorem110Objects : List (String × String × String) :=
  [ ("initial Theta-data (Fr, XF, l, D, V, V_bad, V_good, epsilon)", "model: SourceUnitRegionHaarDataActual sourceHaarActualOriginalInput; abstract: S3131/S3137 paper-route data", "model closed in-model; abstract class B"),
    ("F_mod, F_tpd prime strips", "SourceUnitRegionHaarDataActual prime-strip units / SourceImageRealization", "reuse"),
    ("F, d, dADiv, qADiv, fADiv", "ArithmeticDivisorDegree heightWeight/hTerm (.1214/.1221/.1225/.1310)", "available/adapt"),
    ("log(d_v), log(q_v), log(f_v)", "Height.logHeight1, arithmeticWeight, sourceLocalLogDegree (SourceImageHullVolume:103)", "reuse"),
    ("Theta-pilot object (Theta^+-)", "ThetaPilotCarrier/ThetaPilotPoint; canonical rooted Q_C/H_C readouts", "citable"),
    ("log-shells / unit region", "IQHullLogVolumeInterface.unitRegion, logShellPoint, normalizedComparisonRegion", "concrete IQCarrier interface :193"),
    ("holomorphic hull / determinant", "W.hull; CardAMPLThetaBoundSupply (hull<=theta); HullDeterminantLogVolumeReduction matrixLogDet", "hull half free; det scaling-law adapt"),
    ("log-volume of Theta-pilot / q-pilot", "IQHullLogVolumeInterface.logVolume; regionVolume_le_normalizedWeight target", "(c) interface Cor312ComparisonGapReduction:306"),
    ("final display (Step (v))", "(b) UndilatedHeightBound -> HeightComparisonFamily; (c) UndilatedRegionBound -> RegionVolumeFamily", "class B; exact remaining hypotheses A26/A31/A32") ]

theorem S3171Theorem110Objects_length : S3171Theorem110Objects.length = 9 := rfl

/-- Obligation classes of the proof steps (i)-(viii) (A provable now; B paper-level target; C convention/data). -/
def S3171Theorem110Steps : List (String × String × String) :=
  [ ("(i) setup of initial Theta-data / F_mod,F_tpd conventions", "C/B", "model reuse; abstract conventions"),
    ("(ii) Theta-link/log-link, procession normalization", "C", "S3131/S3137 paper route; model q=1"),
    ("(iii) local log-volume computations (d/q/f divisors)", "A/B", "ArithmeticDivisorDegree; sourceLocalLogDegree"),
    ("(iv) indeterminacy bounds (Ind1,2,3 + hull)", "B/C", "A35 layer Indet01-03 finite-instance laws; full Ind not modelled"),
    ("(v) FINAL DISPLAY: Theta-pilot log-volume estimate", "B", "(b)/(c) undilated interfaces -> families; remaining weight<=theta + uniform height-volume comparison"),
    ("(vi) weighted averages / (R1)-(R3) splitting estimates", "B", "StepVProcessionAverage (R4 only); (R1)-(R3) remaining"),
    ("(vii) Cor 3.12-shaped conclusion", "B", "S3131CanonicalRootedQC_le_HC (green, 4th triangle inequality)"),
    ("(viii) assembly toward ABC via [GenEll]", "B", "H6 interface-level GenEll10H6ClosureActual; (ii)=>(i) paper-input") ]

theorem S3171Theorem110Steps_length : S3171Theorem110Steps.length = 8 := rfl

/-- (b)/(c) interface hookup: the final display is consumed exactly through the two
undilated reduction interfaces (reuse; no new proof here). -/
def S3171FinalDisplayInterface : List String :=
  [ "UndilatedHeightBound (S3131PaperRouteHeightReductionActual) -> HeightComparisonFamily via heightComparisonFamily_of_undilated",
    "UndilatedRegionBound (S3131PaperRouteRegionReductionActual) -> RegionVolumeFamily via regionVolumeFamily_of_undilated" ]

theorem S3171FinalDisplayInterface_length : S3171FinalDisplayInterface.length = 2 := rfl

#check UndilatedHeightBound
#check UndilatedRegionBound
#check HeightComparisonFamily
#check RegionVolumeFamily
#check heightComparisonFamily_of_undilated
#check regionVolumeFamily_of_undilated

end LeanFormal.IUT.XiFPaper.S3171IUTIVSection1StatementActual
end