/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1PaperFaithful312NormedActual
import tmp.sheaf.xif.paper.S3137QThetaPilotLogVolumeReadingsActual
import Mathlib.Tactic

/-! # A746 hull: strength audit of our 3.12 and upgrade to S3137 readings

This file checks the actual strength of the current rpRequirementNorm 3.12:

* requirementSignedQ (rpRequirementNorm T) = Real.log (rpVolumeNorm T (rpRegion T));
* requirementSignedTheta (rpRequirementNorm T) = Real.log (rpVolumeNorm T (fullRegion T)) = 0;

hence the current 3.12 conclusion is EXACTLY the geometric normalized-measure
inequality rpVolumeNorm T (rpRegion T) <= 1 (a containment/volume fact), not the
paper comparison of the actual q-pilot and Theta-pilot log-volume readings.

The genuine paper shape is defined below using the S3137 actual readings:

  Paper312Statement C3 P := qPilotLogVolumeReading P <= thetaPilotHullLogVolumeReal C3

i.e. -|log q| <= log-vol(theta hull) (qThetaPilotLogVolumeComparison in S3137).
The upgrade requires replacing the product-Haar region volumes by these readings
(see upgradeRows); no proof of the paper comparison is fabricated here.

No RETRACTED file referenced. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312StrengthHullUpgradeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.Mzk1PaperFaithful312NormedActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarProductStrictMainlineActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.Mzk1SignedLogVolumeCor312Actual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open MeasureTheory
open scoped ENNReal BigOperators

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- Current signed q-volume is the log of the normalized product-Haar volume. -/
theorem signedQ_norm_eq_log_ratio :
    requirementSignedQ (rpRequirementNorm T) =
      Real.log (rpVolumeNorm T (rpRegion T)) := rfl

/-- Current signed theta-volume is log 1 = 0 (the full region is normalized to 1). -/
theorem signedTheta_norm_eq_zero :
    requirementSignedTheta (rpRequirementNorm T) = 0 := by
  unfold requirementSignedTheta signedLogVolume
  rw [show (rpRequirementNorm T).hullRegion = fullRegion T from rfl,
    rpVolumeNorm_fullRegion T, Real.log_one]

/-- The current 3.12 conclusion is exactly rpVolumeNorm rpRegion <= 1:
a geometric normalized-measure/containment inequality, with no theta arithmetic. -/
theorem normed_cor312_iff_ratio_le_one :
    requirementSignedQ (rpRequirementNorm T) <=
        requirementSignedTheta (rpRequirementNorm T) <->
      rpVolumeNorm T (rpRegion T) <= 1 := by
  rw [signedQ_norm_eq_log_ratio T, signedTheta_norm_eq_zero T]
  have hpos : 0 < rpVolumeNorm T (rpRegion T) := (rpRequirementNorm T).q_pos
  exact Real.log_nonpos_iff hpos.le

/-! ## Genuine paper 3.12 shape with S3137 readings -/

variable {V : Type} {I : OriginalInput l V}

/-- The true paper-shaped comparison of the actual q-pilot reading with the actual
Theta-pilot hull log-volume reading (S3137). -/
def Paper312Statement
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (P : PaperQPilotObjectActual (l := l) (I := I)) : Prop :=
  qPilotLogVolumeReading P <= thetaPilotHullLogVolumeReal C3

theorem paper312Statement_iff_qThetaComparison
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (P : PaperQPilotObjectActual (l := l) (I := I)) :
    Paper312Statement C3 P <-> qThetaPilotLogVolumeComparison C3 P := Iff.rfl

/-- Expanded form: -|log q| <= log-vol(theta hull). -/
theorem paper312Statement_iff_neg_abs_le
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (P : PaperQPilotObjectActual (l := l) (I := I)) :
    Paper312Statement C3 P <->
      -|Real.log (‖P.line.C3.q.q‖)| <= thetaPilotHullLogVolumeReal C3 := by
  unfold Paper312Statement
  rw [qPilotLogVolumeReading_eq_neg_abs_qParameter P]

/-- Theta side is the region log-volume (green S3137 identity). -/
theorem paper312Statement_iff_regionLogVolume
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (P : PaperQPilotObjectActual (l := l) (I := I)) :
    Paper312Statement C3 P <->
      -|Real.log (‖P.line.C3.q.q‖)| <=
        Real.log ((actualC3LogShellTensorHaar C3)
          (actualC3LogShellTensorRegion C3)).toReal := by
  rw [paper312Statement_iff_neg_abs_le C3 P,
    thetaPilotHullLogVolumeReal_eq_regionLogVolume C3]

def currentStrengthRows : List (String × String × String) :=
  [ ("current qSigned", "requirementSignedQ (rpRequirementNorm T) = Real.log (rpVolumeNorm T (rpRegion T))", "rfl"),
    ("current thetaSigned", "requirementSignedTheta (rpRequirementNorm T) = Real.log 1 = 0", "PROVED (signedTheta_norm_eq_zero)"),
    ("current 3.12 conclusion", "log(rpVolumeNorm rpRegion) <= 0 <-> rpVolumeNorm rpRegion <= 1", "PROVED (normed_cor312_iff_ratio_le_one)"),
    ("meaning", "geometric normalized product-Haar measure/containment inequality; no Theta value arithmetic", "STRENGTH LIMIT") ]

theorem currentStrengthRows_length : currentStrengthRows.length = 4 := rfl

def upgradeRows : List (String × String × String) :=
  [ ("volume functional", "replace rpVolumeNorm (product Haar ratio) by S3137 readings: q side qPilotLogVolumeReading = -|log q|, theta side thetaPilotHullLogVolumeReal = log(theta-hull Haar)", "NEW INTERFACE needed"),
    ("requirement structure", "XiEContainmentRequirement (set-volume interface) not suitable; use signed reading interface or direct Prop Paper312Statement", "REPLACE"),
    ("carrier", "current rpRegion : Set (S1902Carrier T); S3137 lives on C3LogShellTensorBlock C3 / PaperQPilotObjectActual; need identification or move requirement to S3137 data", "MISSING BRIDGE"),
    ("q-pilot object", "current requirement has no q-pilot object; need P : PaperQPilotObjectActual and qPilotLogVolumeReading P", "ADD INPUT"),
    ("theta reading", "fullRegion volume = rootExtensionProductImageHull measure; need thetaPilotHullLogVolumeReal C3 (theta-hull log-volume)", "REPLACE"),
    ("new theorem shape", "paper312_statement : Paper312Statement C3 P; unconditional target unavailable; qThetaPilotLogVolumeComparison is the S3137 named candidate", "PRECISE GAP") ]

theorem upgradeRows_length : upgradeRows.length = 6 := rfl

def gapRows : List (String × String × String) :=
  [ ("precise gap", "Paper312Statement C3 P (equiv qThetaPilotLogVolumeComparison C3 P)", "named comparison; S3137 records it as pending, not proved"),
    ("paper form", "-|log q| <= log-vol(theta hull)", "EXPANDED (paper312Statement_iff_neg_abs_le)"),
    ("current 3.12", "rpVolumeNorm rpRegion <= 1 (geometric)", "does NOT imply Paper312Statement without reading bridge"),
    ("no fake proof", "no theorem asserting Paper312Statement is added; only the Prop and equivalences are proved", "INTEGRITY; ABC gate NOT passed") ]

theorem gapRows_length : gapRows.length = 4 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1Cor312StrengthHullUpgradeActual.signedQ_norm_eq_log_ratio
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Cor312StrengthHullUpgradeActual.normed_cor312_iff_ratio_le_one
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Cor312StrengthHullUpgradeActual.paper312Statement_iff_neg_abs_le

end LeanFormal.IUT.XiFPaper.Mzk1Cor312StrengthHullUpgradeActual

end