import Mathlib.Data.Real.Basic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Source-adapted pilot comparison schema (from vendor promachina)

Adapted (source reference only; not imported) from
vendor/promachina/snapshots/1fa6387f.../Iut/Stage1/PilotComparison.lean:21-56.
The vendor structures isolate the Corollary 3.12-shaped real comparison; we
re-declare them under the `Adapted` prefix so the paper-route comparison-region
wiring can consume them from this stream without depending on the vendor project.
Real declarations only; no proof reuse from the vendor.
-/

namespace LeanFormal.IUT.XiFPaper.S3132SourceAdaptedPilotComparisonActual

/-- Names for the two pilot sides of Corollary 3.12. -/
inductive AdaptedPilotSide where
  | q
  | theta
  deriving DecidableEq, Repr

/-- A real log-volume value tagged by its pilot side. -/
structure AdaptedPilotLogVolume where
  side : AdaptedPilotSide
  value : ℝ

/-- The bare real inequality appearing in Corollary 3.12:
`-theta.value >= -q.value`. -/
def AdaptedCorollary312Inequality (theta q : AdaptedPilotLogVolume) : Prop :=
  -theta.value ≥ -q.value

/-- Minimal endpoint package for a Stage 1 comparison (paper-route shape). -/
structure AdaptedStage1Comparison where
  theta : AdaptedPilotLogVolume
  q : AdaptedPilotLogVolume
  theta_side : theta.side = AdaptedPilotSide.theta
  q_side : q.side = AdaptedPilotSide.q
  q_positive : 0 < q.value
  comparison : AdaptedCorollary312Inequality theta q

/-- Projection of the stored comparison. -/
theorem adaptedCorollary312_from_stage1Comparison (data : AdaptedStage1Comparison) :
    AdaptedCorollary312Inequality data.theta data.q :=
  data.comparison

/-- Signed log-volume to tagged positive-magnitude pilot log-volume. -/
def adaptedSignedPilotLogVolume (side : AdaptedPilotSide) (signedValue : ℝ) :
    AdaptedPilotLogVolume :=
  { side := side, value := -signedValue }

@[simp] theorem adaptedSignedPilotLogVolume_side
    (side : AdaptedPilotSide) (signedValue : ℝ) :
    (adaptedSignedPilotLogVolume side signedValue).side = side := rfl

@[simp] theorem adaptedSignedPilotLogVolume_value
    (side : AdaptedPilotSide) (signedValue : ℝ) :
    (adaptedSignedPilotLogVolume side signedValue).value = -signedValue := rfl

/-- Corollary-3.12-shaped inequality from a signed real comparison. -/
theorem adaptedCorollary312_of_signed_le {thetaSigned qSigned : ℝ}
    (hle : qSigned ≤ thetaSigned) :
    AdaptedCorollary312Inequality
      (adaptedSignedPilotLogVolume AdaptedPilotSide.theta thetaSigned)
      (adaptedSignedPilotLogVolume AdaptedPilotSide.q qSigned) := by
  unfold AdaptedCorollary312Inequality adaptedSignedPilotLogVolume
  simpa using hle

#check AdaptedPilotSide
#check AdaptedPilotLogVolume
#check AdaptedCorollary312Inequality
#check AdaptedStage1Comparison
#check adaptedCorollary312_of_signed_le

end LeanFormal.IUT.XiFPaper.S3132SourceAdaptedPilotComparisonActual