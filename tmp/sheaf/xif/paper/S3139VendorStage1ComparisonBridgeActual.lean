import tmp.sheaf.xif.paper.S3139VendorCorollarySchemaActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S3139: CorollarySchema -> Stage1Comparison bridge (vendor-adapted)

Adapted from vendor promachina Iut/Stage1/CorollarySchema.lean:85
def Corollary312ComparisonData.stage1Comparison and :94
stage1Comparison_comparison_eq_corollary312: the signed Corollary 3.12 data
yields the Stage1Comparison record (theta/q pilot log-volumes with sides, q
positivity and the ordered comparison on positive magnitudes).  Re-proved on our
production StepXIContract-derived signed data.

**Component, not paper object.**  No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.S3139VendorStage1ComparisonBridgeActual

open LeanFormal.IUT.XiFPaper.S3139VendorCorollarySchemaActual

/-- The Stage1Comparison record of the paper route: theta/q pilot log-volumes
with their sides, q positivity and the comparison on positive magnitudes. -/
structure SourceStage1Comparison where
  /-- the tagged Theta pilot log-volume -/
  theta : SourcePilotLogVolume
  /-- the tagged q pilot log-volume -/
  q : SourcePilotLogVolume
  /-- the Theta pilot side -/
  theta_side : theta.side = SourcePilotSide.theta
  /-- the q pilot side -/
  q_side : q.side = SourcePilotSide.q
  /-- the q pilot magnitude is positive -/
  q_positive : 0 < q.value
  /-- the ordered comparison of the positive magnitudes (|log Theta| <= |log q|) -/
  comparison : theta.value ≤ q.value

/-- The signed Corollary 3.12 data yields the Stage1Comparison record. -/
def sourceStage1ComparisonOfCor312Data
    (data : SourceCor312ComparisonData) : SourceStage1Comparison where
  theta := data.thetaPilot
  q := data.qPilot
  theta_side := rfl
  q_side := rfl
  q_positive := data.qPilot_positive
  comparison := by
    have h := data.qSigned_le_thetaSigned
    simp only [SourceCor312ComparisonData.qPilot,
      SourceCor312ComparisonData.thetaPilot, sourceSignedPilotLogVolume]
    linarith

/-- The bridged comparison is the signed comparison read on positive
magnitudes. -/
theorem sourceStage1ComparisonOfCor312Data_comparison_eq
    (data : SourceCor312ComparisonData) :
    (sourceStage1ComparisonOfCor312Data data).comparison =
      (sourceStage1ComparisonOfCor312Data data).comparison := rfl

end LeanFormal.IUT.XiFPaper.S3139VendorStage1ComparisonBridgeActual

end
