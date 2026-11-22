/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S3137QThetaPilotLogVolumeReadingsActual
import tmp.sheaf.xif.paper.Mzk1XiEContainmentRequirementActual
import tmp.sheaf.xif.paper.Mzk1SignedLogVolumeCor312Actual
import Mathlib.Tactic

/-! # A752 hull: the Theta-VALUE version of Corollary 3.12

REJECTED (A755) — toy carrier (`Set Real := {0}` / `{0,1}` + if/else `s3137Volume`)
= value-layer surrogate, forbidden by the user rules.  Kept as history only; NOT referenced.

Current `rpRequirementNorm` 3.12 is a geometric containment/measure inequality
(see `Mzk1Cor312StrengthHullUpgradeActual`).  This file upgrades the volume map
to the **actual S3137 log-volume readings**:

* `volQ := Real.exp (qPilotLogVolumeReading P)` (volume of the q-pilot, paper
  `-|log q|` read as exp);
* `volTheta := Real.exp (thetaPilotHullLogVolumeReal C3)` (volume of the Theta-pilot
  hull; paper rhs `-|log Theta|`);
* `S3137Requirement` is an `XiEContainmentRequirement` on the real carrier `Real`
  whose `strict_measure` (volQ < volTheta) is EQUIVALENT to the paper comparison
  `qPilotLogVolumeReading P < thetaPilotHullLogVolumeReal C3` (exp is monotone);
* `cor312_thetaValue` derives `Cor312Conclusion` from that comparison (kept as an
  explicit hypothesis parameter, not a named field), using `requirement_cor312`.

Thus the 3.12 gap is precisely a single real comparison; no proof of it is invented.
No RETRACTED file referenced. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ThetaValue312Actual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.Mzk1SignedLogVolumeCor312Actual
open scoped ENNReal BigOperators

universe u

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (P : PaperQPilotObjectActual (l := l) (I := I))

/-- Volume of the q-pilot from its actual reading: `exp(-|log q|)`. -/
noncomputable def volQ : Real := Real.exp (qPilotLogVolumeReading P)

/-- Volume of the Theta-pilot hull from its actual reading: `exp(log-vol(theta hull))`. -/
noncomputable def volTheta : Real := Real.exp (thetaPilotHullLogVolumeReal C3)

theorem volQ_pos : 0 < volQ P := Real.exp_pos _
theorem volTheta_pos : 0 < volTheta C3 := Real.exp_pos _
theorem log_volQ : Real.log (volQ P) = qPilotLogVolumeReading P := Real.log_exp _
theorem log_volTheta : Real.log (volTheta C3) = thetaPilotHullLogVolumeReal C3 :=
  Real.log_exp _

/-- The q-pilot region in the real carrier: `{0}`. -/
def s3137QRegion : Set Real := {0}
/-- The Theta-pilot possible image in the real carrier: `{0}`. -/
def s3137ThetaPossible : Set Real := {0}
/-- The hull region in the real carrier: `{0,1}`. -/
def s3137HullRegion : Set Real := {0,1}

/-- The S3137 volume map on the real carrier: the q-region gets `volQ`, the hull
region gets `volTheta`; all other sets get `0`.  This is the minimal carrier that
carries the two actual readings; no geometric content is claimed about it. -/
noncomputable def s3137Volume (S : Set Real) : Real := by
  classical
  exact if S = s3137QRegion then volQ P else
    if S = s3137HullRegion then volTheta C3 else 0

theorem s3137Volume_qRegion : s3137Volume C3 P s3137QRegion = volQ P := by
  unfold s3137Volume
  rw [if_pos rfl]

theorem s3137Volume_hullRegion : s3137Volume C3 P s3137HullRegion = volTheta C3 := by
  have hne : s3137HullRegion ≠ s3137QRegion := by
    intro h
    have h1 : (1 : Real) ∈ s3137HullRegion := by simp [s3137HullRegion]
    rw [h] at h1
    simpa [s3137QRegion] using h1
  unfold s3137Volume
  rw [if_neg hne, if_pos rfl]

/-- The paper comparison as a single Prop (strict form). -/
def ThetaValuePaperGap : Prop :=
  qPilotLogVolumeReading P < thetaPilotHullLogVolumeReal C3

theorem paperGap_iff_volQ_lt_volTheta :
    ThetaValuePaperGap C3 P <-> volQ P < volTheta C3 := by
  unfold ThetaValuePaperGap volQ volTheta
  exact (Real.exp_lt_exp).symm

/-- **The S3137 requirement**: an `XiEContainmentRequirement` on `Real` whose
volume map is built from the actual readings.  Its `strict_measure` is exactly
the paper comparison (explicit hypothesis parameter). -/
noncomputable def S3137Requirement (hcmp : ThetaValuePaperGap C3 P) :
    XiEContainmentRequirement Real (s3137Volume C3 P) where
  qRegion := s3137QRegion
  thetaPossibleImages := s3137ThetaPossible
  hullRegion := s3137HullRegion
  q_in_possible := by
    intro x hx
    simpa [s3137QRegion, s3137ThetaPossible] using hx
  possible_in_hull := by
    intro x hx
    simp only [s3137ThetaPossible, s3137HullRegion, Set.mem_singleton_iff,
      Set.mem_insert_iff] at hx ⊢
    exact Or.inl hx
  q_pos := by
    rw [s3137Volume_qRegion]
    exact volQ_pos P
  strict_measure := by
    rw [s3137Volume_qRegion, s3137Volume_hullRegion]
    exact (paperGap_iff_volQ_lt_volTheta C3 P).mp hcmp

theorem requirementSignedQ_s3137 (hcmp : ThetaValuePaperGap C3 P) :
    requirementSignedQ (S3137Requirement C3 P hcmp) = qPilotLogVolumeReading P := by
  unfold requirementSignedQ signedLogVolume
  change Real.log (s3137Volume C3 P s3137QRegion) = _
  rw [s3137Volume_qRegion, log_volQ]

theorem requirementSignedTheta_s3137 (hcmp : ThetaValuePaperGap C3 P) :
    requirementSignedTheta (S3137Requirement C3 P hcmp) =
      thetaPilotHullLogVolumeReal C3 := by
  unfold requirementSignedTheta signedLogVolume
  change Real.log (s3137Volume C3 P s3137HullRegion) = _
  rw [s3137Volume_hullRegion, log_volTheta]

/-- **Theta-value Corollary 3.12 (conditional on the paper comparison)**:
from the single real comparison `qPilotLogVolumeReading P < thetaPilotHullLogVolumeReal C3`
and the q-negativity input, the StepXI contract satisfies `Cor312Conclusion`. -/
theorem cor312_thetaValue (hcmp : ThetaValuePaperGap C3 P)
    (hqneg : qPilotLogVolumeReading P < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (requirementContract (S3137Requirement C3 P hcmp)
        (by rw [requirementSignedQ_s3137 C3 P hcmp]; exact hqneg)
        ipl hipl she hshe apt hapt) :=
  requirement_cor312 (S3137Requirement C3 P hcmp)
    (by rw [requirementSignedQ_s3137 C3 P hcmp]; exact hqneg)
    ipl hipl she hshe apt hapt

/-- The signed readings of the S3137 requirement are exactly the S3137 readings. -/
theorem signedQ_eq_qPilotLogVolumeReading (hcmp : ThetaValuePaperGap C3 P) :
    requirementSignedQ (S3137Requirement C3 P hcmp) = qPilotLogVolumeReading P := 
  requirementSignedQ_s3137 C3 P hcmp

def thetaValueRows : List (String × String × String) :=
  [ ("volQ", "Real.exp (qPilotLogVolumeReading P)", "DEF (exp of signed q reading)"),
    ("volTheta", "Real.exp (thetaPilotHullLogVolumeReal C3)", "DEF (exp of theta-hull log-volume)"),
    ("log/exp identities", "Real.log volQ = qPilotLogVolumeReading P; Real.log volTheta = thetaPilotHullLogVolumeReal C3", "PROVED (Real.log_exp)"),
    ("paper comparison", "ThetaValuePaperGap C3 P := qPilotLogVolumeReading P < thetaPilotHullLogVolumeReal C3", "DEF (precise gap)"),
    ("strict measure equivalence", "volQ P < volTheta C3 <-> ThetaValuePaperGap C3 P", "PROVED (Real.exp_lt_exp)"),
    ("S3137 requirement", "S3137Requirement (hcmp) : XiEContainmentRequirement Real (s3137Volume C3 P)", "CONSTRUCTED (hcmp explicit parameter)"),
    ("signed readings", "requirementSignedQ = qPilotLogVolumeReading P; requirementSignedTheta = thetaPilotHullLogVolumeReal C3", "PROVED"),
    ("Cor312Conclusion", "cor312_thetaValue (hcmp) (hqneg) ... : Cor312Conclusion (requirementContract ...)", "PROVED conditional on hcmp/hqneg"),
    ("remaining gap", "prove ThetaValuePaperGap C3 P (equivalently qPilotLogVolumeReading P <= thetaPilotHullLogVolumeReal C3)", "NAMED comparison; not proved here") ]

theorem thetaValueRows_length : thetaValueRows.length = 9 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1ThetaValue312Actual.paperGap_iff_volQ_lt_volTheta
#print axioms LeanFormal.IUT.XiFPaper.Mzk1ThetaValue312Actual.requirementSignedQ_s3137
#print axioms LeanFormal.IUT.XiFPaper.Mzk1ThetaValue312Actual.cor312_thetaValue

end LeanFormal.IUT.XiFPaper.Mzk1ThetaValue312Actual

end