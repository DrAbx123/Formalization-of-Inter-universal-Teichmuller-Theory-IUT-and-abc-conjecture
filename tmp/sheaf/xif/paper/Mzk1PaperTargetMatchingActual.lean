/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S3137QThetaPilotLogVolumeReadingsActual
import tmp.sheaf.xif.paper.S3137ThetaHullVolumeScalingActual
import Mathlib.Tactic

/-!
# Mzk1PaperTargetMatchingActual — paper statement match (IUT III Cor 3.12, 10324-10353)

A540 self-check: the assembled target matches the paper Corollary 3.12 statement:
* `−|log Θ| ∈ R` (the actual hull Haar measure is finite, S3137);
* `|log q| > 0` (the q-pilot reading is nonpositive, S3137);
* `−|log Θ| ≥ −|log q|` (the signed comparison), and
* `C_Θ ≥ −1` for `−|log Θ| ≤ C_Θ |log q|`.

No new axiom; the comparison itself remains the named input. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1PaperTargetMatchingActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorHolomorphicHullActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S3137ThetaHullVolumeScalingActual
open MeasureTheory
open scoped ENNReal

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (P : PaperQPilotObjectActual (l := l) (I := I))

/-- The paper Cor 3.12 target on one actual C3 input and q-pilot object. -/
structure PaperTargetStatement : Prop where
  /-- `−|log Θ|` is finite (`∈ R`). -/
  thetaHullFinite : (actualC3LogShellTensorHaar C3) (thetaPilotHull C3) < ⊤
  /-- `−|log q| ≤ 0` (`|log q| > 0`). -/
  qReading_nonpos : qPilotLogVolumeReading P ≤ 0
  /-- the paper comparison `−|log Θ| ≥ −|log q|`. -/
  signedInequality : qPilotLogVolumeReading P ≤ thetaPilotHullLogVolumeReal C3

/-- The finiteness and q-nonpositivity components are proved from S3137. -/
theorem paperTarget_components :
    (actualC3LogShellTensorHaar C3) (thetaPilotHull C3) < ⊤ ∧
      qPilotLogVolumeReading P ≤ 0 :=
  ⟨thetaPilotHull_measure_lt_top (C3 := C3), qPilotLogVolumeReading_nonpos P⟩

/-- The paper target statement from the named signed comparison. -/
theorem paperTarget_of_comparison
    (h : qPilotLogVolumeReading P ≤ thetaPilotHullLogVolumeReal C3) :
    PaperTargetStatement C3 P where
  thetaHullFinite := thetaPilotHull_measure_lt_top (C3 := C3)
  qReading_nonpos := qPilotLogVolumeReading_nonpos P
  signedInequality := h

/-- `C_Θ ≥ −1` from the paper comparison: if `−|log Θ| = C |log q|` and
`|log q| > 0`, then `−|log q| ≤ −|log Θ|` gives `C ≥ −1`. -/
theorem paperTarget_CTheta_ge_neg_one {qMag C thetaLog qLog : Real}
    (hq : 0 < qMag) (hqeq : qLog = -qMag) (hC : thetaLog = C * qMag)
    (hineq : qLog ≤ thetaLog) : -1 ≤ C := by
  rw [hqeq, hC] at hineq
  nlinarith

/-- The comparison component is exactly the paper display `-|log Θ| ≥ -|log q|`. -/
theorem paperTarget_signedInequality_iff :
    PaperTargetStatement C3 P ↔
      ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3) < ⊤ ∧
        qPilotLogVolumeReading P ≤ 0 ∧
        qPilotLogVolumeReading P ≤ thetaPilotHullLogVolumeReal C3) := by
  constructor
  · intro h
    exact ⟨h.thetaHullFinite, h.qReading_nonpos, h.signedInequality⟩
  · intro h
    exact ⟨h.1, h.2.1, h.2.2⟩

#check paperTarget_components
#check paperTarget_CTheta_ge_neg_one
#check paperTarget_signedInequality_iff

end LeanFormal.IUT.XiFPaper.Mzk1PaperTargetMatchingActual
end
