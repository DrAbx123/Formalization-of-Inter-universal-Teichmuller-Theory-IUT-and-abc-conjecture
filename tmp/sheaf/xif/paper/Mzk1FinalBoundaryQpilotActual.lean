/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1FinalCertificateQpilotActual
import tmp.sheaf.xif.paper.Mzk1A618ProofQpilotActual
import tmp.sheaf.xif.paper.Mzk1HeightWeightFromTripleQpilotActual
import tmp.sheaf.xif.paper.Mzk1RegionNecessitySummaryQpilotActual
import tmp.sheaf.xif.paper.Mzk1HqnegDischargedGateQpilotActual
import Mathlib.Tactic
import tmp.sheaf.xif.paper.Mzk1ABCTwoEstimatesModelQpilotActual
import tmp.sheaf.xif.paper.Mzk1QPilotSHEDoubleImageActual

/-! # Mzk1FinalBoundaryQpilotActual — final boundary summary (A647)

Boundary summary: which parts are green (conditional on named gaps), which are
proved obstructions, and which are calibrations.  One table + payload of the
actual results. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 5000000

namespace LeanFormal.IUT.XiFPaper.Mzk1FinalBoundaryQpilotActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1QPilotSHEDoubleImageActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesModelQpilotActual
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperComparisonRegionScalingActual
open LeanFormal.IUT.XiFPaper.Mzk1FinalCertificateQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1A618ProofQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1HeightWeightFromTripleQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1RegionNecessitySummaryQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1HqnegDischargedGateQpilotActual
open MeasureTheory
open scoped ENNReal

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [Nonempty (Bad (nativePlaceSelection T))]

/-- The final boundary table. -/
def finalBoundaryRows : List (String × String × String) :=
  [ ("Cor 3.12 final assembly", "GREEN conditional on hqneg (discharged via hull model)",
     "cor312Conclusion_final / hqnegDischarged_exists"),
    ("hqneg discharge", "GREEN (hull side model, imported)",
     "Mzk1HqnegHullModelActual.canonicalHqneg"),
    ("A618 estimates", "GREEN conditional on named gaps",
     "a618_heightEstimate / a618_volumeEstimate"),
    ("triple comparison -> height-weight", "GREEN conditional on two named gaps",
     "heightWeightBoundShape_of_tripleComparison"),
    ("region necessity obstructions", "PROVED (obstructions)",
     "no_constantRegion_heightComparison / no_heightDictionary_into_finiteHull"),
    ("gap tightness calibration", "CALIBRATED (numeric)",
     "Mzk1GapTightnessCalibrationQpilotActual") ]

theorem finalBoundaryRows_length : finalBoundaryRows.length = 6 := rfl

/-- The final boundary payload: the actual proved results behind the table. -/
structure FinalBoundaryPayload where
  certificate : Nonempty (FinalCertificate T)
  hqnegDischarged : ∀ (qRead : Real), qRead < 0 → ∀ (apt : Prop), apt →
    ∃ C : StepXIContract, Cor312Conclusion C
  tripleBound : ∀ (point : Nat → Nat → Nat → S1902Carrier T)
    (C : TripleDependentComparison T point), HeightWeightBoundShape
  regionNecessity : Nonempty RegionNecessityPayload.{0}

/-- The constructed final boundary payload. -/
noncomputable def finalBoundaryPayload : FinalBoundaryPayload T where
  certificate := ⟨finalCertificate T⟩
  hqnegDischarged := fun qRead hq apt hapt =>
    hqnegDischarged_exists T qRead hq (SHEArrowStatement T)
      (sheArrowStatement_proved T) apt hapt
  tripleBound := fun point C => heightWeightBoundShape_of_tripleComparison T point C
  regionNecessity := ⟨regionNecessityPayload⟩

#check finalBoundaryRows_length
#check finalBoundaryPayload

end LeanFormal.IUT.XiFPaper.Mzk1FinalBoundaryQpilotActual
end
