import tmp.sheaf.xif.paper.S3132SourceAdaptedPilotComparisonActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Source-adapted Corollary 3.12 comparison data (from vendor promachina)

Adapted (source reference only; not imported) from
vendor/promachina/snapshots/1fa6387f.../Iut/Stage1/CorollarySchema.lean:28-92.
The vendor record isolates the real-valued comparison payload of the Corollary
3.12 endpoint; re-declared under `Adapted` for the paper-route comparison region.
Real declarations only.
-/

namespace LeanFormal.IUT.XiFPaper.S3132SourceAdaptedCorollary312DataActual

open LeanFormal.IUT.XiFPaper.S3132SourceAdaptedPilotComparisonActual

/-- Abstract signed comparison payload for the Corollary 3.12 endpoint. -/
structure AdaptedCorollary312ComparisonData where
  thetaSigned : ℝ
  qSigned : ℝ
  q_positive : 0 < -qSigned
  qSigned_le_thetaSigned : qSigned ≤ thetaSigned

namespace AdaptedCorollary312ComparisonData

/-- The Theta-side tagged pilot log-volume. -/
def thetaPilot (data : AdaptedCorollary312ComparisonData) : AdaptedPilotLogVolume :=
  adaptedSignedPilotLogVolume AdaptedPilotSide.theta data.thetaSigned

/-- The q-side tagged pilot log-volume. -/
def qPilot (data : AdaptedCorollary312ComparisonData) : AdaptedPilotLogVolume :=
  adaptedSignedPilotLogVolume AdaptedPilotSide.q data.qSigned

theorem thetaPilot_side (data : AdaptedCorollary312ComparisonData) :
    data.thetaPilot.side = AdaptedPilotSide.theta := rfl

theorem qPilot_side (data : AdaptedCorollary312ComparisonData) :
    data.qPilot.side = AdaptedPilotSide.q := rfl

theorem qPilot_positive (data : AdaptedCorollary312ComparisonData) :
    0 < data.qPilot.value := by
  simpa [qPilot, adaptedSignedPilotLogVolume] using data.q_positive

/-- The adapted record satisfies the Corollary 3.12 inequality. -/
theorem corollary312 (data : AdaptedCorollary312ComparisonData) :
    AdaptedCorollary312Inequality data.thetaPilot data.qPilot :=
  adaptedCorollary312_of_signed_le data.qSigned_le_thetaSigned

/-- The adapted record as a full Stage 1 comparison package. -/
def stage1Comparison (data : AdaptedCorollary312ComparisonData) :
    AdaptedStage1Comparison :=
  { theta := data.thetaPilot
    q := data.qPilot
    theta_side := data.thetaPilot_side
    q_side := data.qPilot_side
    q_positive := data.qPilot_positive
    comparison := data.corollary312 }

#check AdaptedCorollary312ComparisonData
#check AdaptedCorollary312ComparisonData.thetaPilot
#check AdaptedCorollary312ComparisonData.qPilot
#check AdaptedCorollary312ComparisonData.qPilot_positive
#check AdaptedCorollary312ComparisonData.corollary312
#check AdaptedCorollary312ComparisonData.stage1Comparison

end AdaptedCorollary312ComparisonData

end LeanFormal.IUT.XiFPaper.S3132SourceAdaptedCorollary312DataActual
