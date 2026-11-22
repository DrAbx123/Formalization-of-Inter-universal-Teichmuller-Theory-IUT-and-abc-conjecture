import tmp.sheaf.xif.paper.Mzk1FinalBoundarySzpiroActual
import tmp.sheaf.xif.paper.Mzk1PaperFaithful312NormedActual
import tmp.sheaf.xif.paper.Mzk1Paper312StatementActual
import tmp.sheaf.xif.paper.Mzk1N3SharedContainerBridgeShaActual
import Mathlib.Tactic

/-!
# A771 boundary ↔ paper-normalized 3.12 (shehdd)

Two formalizations are connected here:
* the **normalized** route `Mzk1PaperFaithful312NormedActual` (`rpVolumeNorm =
  raw/fullRegion`, unconditional `hqneg_norm`, `final_3_12_normed`), whose signed
  values are `log(rpVolumeNorm rpRegion)` and `0`;
* the **paper boundary** `Mzk1FinalBoundarySzpiroActual` / `Mzk1Paper312StatementActual`,
  whose readings are the actual S3137 values `qPilotLogVolumeReading P` and
  `thetaPilotHullLogVolumeReal C3`.

Their alignment is exactly a two-field dictionary (normalization + carrier):
`NormalizationDictionary qNorm thetaNorm qPaper thetaPaper` with `qNorm = qPaper`
and `thetaNorm = thetaPaper`.  Under it:
* normalized conclusion (= `log ratio <= 0`) ↔ `Paper312Statement` (= `paperGap`);
* no unconditional identification is claimed (the carriers differ: S1902 vs C3).

No RETRACTED statement is used.  No sorry/axiom/True.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1BoundaryNormalizationBridgeShaActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.Mzk1SignedLogVolumeCor312Actual
open LeanFormal.IUT.XiFPaper.Mzk1HaarProductStrictMainlineActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperFaithful312NormedActual
open LeanFormal.IUT.XiFPaper.Mzk1Paper312StatementActual
open LeanFormal.IUT.XiFPaper.Mzk1N3SharedContainerBridgeShaActual
open LeanFormal.IUT.XiFPaper.Mzk1N3SharedContainerRealActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.XiFPaper.Mzk1FinalBoundarySzpiroActual
open MeasureTheory
open scoped ENNReal BigOperators

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- Normalized signed q-value is the log of the normalized rp volume. -/
theorem normed_signedQ_eq :
    requirementSignedQ (rpRequirementNorm T) =
      Real.log (rpVolumeNorm T (rpRegion T)) := rfl

/-- Normalized signed Theta-value is zero (hull normalized to the full region). -/
theorem normed_signedTheta_eq_zero :
    requirementSignedTheta (rpRequirementNorm T) = 0 := by
  unfold requirementSignedTheta signedLogVolume
  change Real.log (rpVolumeNorm T (fullRegion T)) = 0
  rw [rpVolumeNorm_fullRegion, Real.log_one]

/-- The normalized 3.12 conclusion is exactly `log(rpVolumeNorm rpRegion) <= 0`. -/
theorem normedConclusion_iff_logRatio_nonpos :
    requirementSignedQ (rpRequirementNorm T) ≤
        requirementSignedTheta (rpRequirementNorm T) ↔
      Real.log (rpVolumeNorm T (rpRegion T)) ≤ 0 := by
  rw [normed_signedQ_eq, normed_signedTheta_eq_zero]

/-- The two-field normalization/carrier dictionary: normalized values equal the
actual S3137 readings. -/
structure NormalizationDictionary (qNorm thetaNorm qPaper thetaPaper : Real) : Prop where
  q_align : qNorm = qPaper
  theta_align : thetaNorm = thetaPaper

theorem normed_to_paper_under_dictionary {qNorm thetaNorm qPaper thetaPaper : Real}
    (D : NormalizationDictionary qNorm thetaNorm qPaper thetaPaper)
    (h : qNorm ≤ thetaNorm) : qPaper ≤ thetaPaper := by
  rw [← D.q_align, ← D.theta_align]
  exact h

theorem paper_to_normed_under_dictionary {qNorm thetaNorm qPaper thetaPaper : Real}
    (D : NormalizationDictionary qNorm thetaNorm qPaper thetaPaper)
    (h : qPaper ≤ thetaPaper) : qNorm ≤ thetaNorm := by
  rw [D.q_align, D.theta_align]
  exact h

variable {V2 : Type} {I2 : OriginalInput l V2}
variable (C3 : SourcePilotRegionData (l := l) (V := V2) I2)
variable (P : PaperQPilotObjectActual (l := l) (I := I2))

/-- **Boundary ↔ normalized 3.12**: under the two-field dictionary, the normalized
conclusion is equivalent to the true paper 3.12 statement. -/
theorem normedConclusion_iff_paper312_under_dictionary
    (D : NormalizationDictionary
      (Real.log (rpVolumeNorm T (rpRegion T))) 0
      (qPilotLogVolumeReading P) (thetaPilotHullLogVolumeReal C3)) :
    requirementSignedQ (rpRequirementNorm T) ≤
        requirementSignedTheta (rpRequirementNorm T) ↔
      Paper312Statement C3 P := by
  rw [normedConclusion_iff_logRatio_nonpos]
  unfold Paper312Statement
  rw [← D.q_align, ← D.theta_align]

end LeanFormal.IUT.XiFPaper.Mzk1BoundaryNormalizationBridgeShaActual

#print axioms LeanFormal.IUT.XiFPaper.Mzk1BoundaryNormalizationBridgeShaActual.normedConclusion_iff_logRatio_nonpos
#print axioms LeanFormal.IUT.XiFPaper.Mzk1BoundaryNormalizationBridgeShaActual.normedConclusion_iff_paper312_under_dictionary
