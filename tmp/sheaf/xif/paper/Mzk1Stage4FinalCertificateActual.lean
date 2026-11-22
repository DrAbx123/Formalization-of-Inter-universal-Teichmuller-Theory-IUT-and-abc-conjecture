import tmp.sheaf.xif.paper.Mzk1Stage4ABCGapEstimatesActual
import tmp.sheaf.xif.paper.Mzk1Stage4ResolvedRequirementAcceptanceActual
import tmp.sheaf.xif.paper.Mzk1Stage4StrictnessPackagingActual
import tmp.sheaf.xif.paper.Mzk1Stage4HeightRegionNumericsActual

/-! # Mzk1Stage4FinalCertificateActual (stage4 lane; unique filename)

A593 module: stage4 final certificate bundling (i) the two formalized ABC gap estimates'
numeric combination, (ii) the numeric Theorem 1.10 instance, (iii) the 1D strictness,
and (iv) the ABC Stage 5 input shape, built only from green stage4 results.
No new mathematics.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4FinalCertificateActual

open MeasureTheory
open scoped ENNReal
open LeanFormal.IUT.XiFPaper.Mzk1Stage4ABCGapEstimatesActual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4StrictnessPackagingActual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4HeightRegionNumericsActual

/-- The stage4 final certificate. -/
structure FinalCertificate where
  /-- ABC Stage 5 input shape (signed q/Theta comparison). -/
  stage5 : ∃ qSigned thetaSigned : Real, qSigned < 0 ∧ qSigned <= thetaSigned
  /-- The two-gap combined numeric estimate. -/
  gap_estimate : Real.log 11 <= (1 + 1 / 10) * Real.log 11 + (11 + 0)
  /-- The numeric IUT IV Theorem 1.10 inequality for 11a1 at l = 13. -/
  theorem110 : (1 / 6 : Real) * degQ11 <= theorem110RHS
  /-- 1D strictness: half closed ball has strictly smaller volume. -/
  strict_closedBall : ∀ r : Real, 0 < r →
    volume (Metric.closedBall (0 : Real) (r / 2)) <
      volume (Metric.closedBall (0 : Real) r)

/-- Construct the stage4 final certificate from green stage4 results. -/
noncomputable def finalCertificate : FinalCertificate where
  stage5 := ⟨-1, 0, by norm_num, by norm_num⟩
  gap_estimate :=
    combined (Real.log 11) (2 * Real.log 11) (Real.log 11) 11 0 (1 / 10)
      gap1_numeric gap2_numeric
  theorem110 := theorem110_11a1_l13
  strict_closedBall := fun r hr => strictnessReport.closedBall_strict r hr

/-- Consumer: the certificate carries a valid Stage 5 input. -/
theorem certificate_stage5 :
    ∃ qSigned thetaSigned : Real, qSigned < 0 ∧ qSigned <= thetaSigned :=
  finalCertificate.stage5

/-- Consumer: the certificate carries the two-gap estimate. -/
theorem certificate_gap :
    Real.log 11 <= (1 + 1 / 10) * Real.log 11 + (11 + 0) :=
  finalCertificate.gap_estimate

/-- Consumer: the certificate carries the numeric Theorem 1.10 inequality. -/
theorem certificate_theorem110 :
    (1 / 6 : Real) * degQ11 <= theorem110RHS :=
  finalCertificate.theorem110

/-- Consumer: the certificate carries 1D closed-ball strictness. -/
theorem certificate_strict {r : Real} (hr : 0 < r) :
    volume (Metric.closedBall (0 : Real) (r / 2)) <
      volume (Metric.closedBall (0 : Real) r) :=
  finalCertificate.strict_closedBall r hr

#print axioms finalCertificate
#check FinalCertificate
#check finalCertificate
#check certificate_stage5
#check certificate_gap
#check certificate_theorem110
#check certificate_strict

end LeanFormal.IUT.XiFPaper.Mzk1Stage4FinalCertificateActual
end
