/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S3137QThetaPilotLogVolumeReadingsActual
import tmp.sheaf.xif.paper.S3137ThetaHullVolumeScalingActual
import tmp.sheaf.xif.paper.Mzk1S3137ComparisonArithmeticActual
import tmp.sheaf.xif.paper.Mzk1S3137ComparisonNumericInstanceActual
import tmp.sheaf.xif.paper.RefLANAMultiradialSpecActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.Contract

/-!
# A525 CORRECTED signed 3.12 assembly: q-pilot reading vs Theta-pilot hull volume

**Correction (A525).**  The previous version identified `qSigned` with the signed
log-volume of `actualC3LogShellTensorRegion`; but S3137 proves
`thetaPilotHull = actualC3LogShellTensorRegion`, so that is the SAME region and the
comparison was a renaming, not the paper comparison.  Here:

* `qSigned := qPilotLogVolumeReading P = -|log q|` — the paper q-pilot log-volume of the
  actual q-pilot object (a NUMBER, not the region's log-volume);
* `thetaSigned := thetaPilotHullLogVolumeReal C3 = Real.log ((haar C3) thetaPilotHull)`
  — the actual Theta-pilot hull log-volume (a different object);
* the paper comparison `qThetaPilotLogVolumeComparison C3 P` is
  `qPilotLogVolumeReading P ≤ thetaPilotHullLogVolumeReal C3`.  Its truth is the named
  candidate; it is reduced to pure real arithmetic by
  `Mzk1S3137ComparisonArithmeticActual.qThetaComparison_iff_arithmetic` under the two
  explicit identifications (hull/procession proportionality and q normalization), and a
  concrete numeric instance is PROVED (`numeric_l13_p11_m5` /
  `qThetaComparison_of_numericInstance`).  No same-region substitution is used.

Consequence: the StepXI contract below uses the two DIFFERENT readings; the inequality is
either the named candidate (`SignedReadings.comparison`) or supplied by the arithmetic
reduction/numeric instance.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1SignedCor312AssemblyActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorHolomorphicHullActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S3137ThetaHullVolumeScalingActual
open LeanFormal.IUT.XiFPaper.Mzk1S3137ComparisonArithmeticActual
open LeanFormal.IUT.XiFPaper.Mzk1S3137ComparisonNumericInstanceActual
open MeasureTheory
open scoped Pointwise ENNReal

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

local instance correctedAssemblyBlockMeasurableSpace :
    MeasurableSpace (C3LogShellTensorBlock C3) := borel _

local instance correctedAssemblyBlockBorelSpace :
    BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

/-! ## 1. The two DIFFERENT paper readings -/

variable (P : PaperQPilotObjectActual (l := l) (I := I))

/-- The paper q-pilot reading `-|log q|` (S3137 q-side; a number, not a region
  log-volume). -/
def qPilotLogVolume : ℝ :=
  qPilotLogVolumeReading P

/-- The paper Theta-pilot hull reading `-|log(Theta)|` (S3137 Theta-side). -/
def thetaPilotLogVolume : ℝ :=
  thetaPilotHullLogVolumeReal C3

/-- The q reading is `-|log q|` of the actual source completion. -/
theorem qPilotLogVolume_eq_neg_abs :
    qPilotLogVolume C3 P = -|Real.log (‖P.line.C3.q.q‖)| :=
  qPilotLogVolumeReading_eq_neg_abs_qParameter P

/-- The Theta reading is the actual Haar log-volume of the actual Theta-pilot hull
  (different object from the q reading). -/
theorem thetaPilotLogVolume_eq_hullHaar :
    thetaPilotLogVolume C3 =
      Real.log ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3)).toReal :=
  rfl

/-- The hull is the same SET as the actual tensor log-shell region (S3137 identity);
  this is recorded for reference only — it is NOT used to identify the two readings. -/
theorem thetaPilotHull_eq_actualRegion :
    thetaPilotHull C3 = actualC3LogShellTensorRegion C3 :=
  thetaPilotHull_eq_region (C3 := C3)

/-! ## 2. The comparison: named candidate / arithmetic reduction / numeric instance -/

/-- The paper comparison is the S3137 named candidate (different objects). -/
theorem comparison_iff_namedCandidate :
    qPilotLogVolume C3 P ≤ thetaPilotLogVolume C3 ↔
      qThetaPilotLogVolumeComparison C3 P :=
  Iff.rfl

/-- **Arithmetic reduction**: under the two explicit named identifications (hull equal to
  the procession average; q reading equal to the arithmetic volume), the comparison is
  pure real arithmetic. -/
theorem comparison_iff_arithmetic {m n : Nat} {p : ℝ}
    (hTheta : thetaPilotHullLogVolumeReal C3 = processionAverage m n p)
    (hq : qPilotLogVolumeReading P = qPilotArithmeticVolume m n p) :
    qPilotLogVolume C3 P ≤ thetaPilotLogVolume C3 ↔
      qPilotArithmeticVolume m n p ≤ processionAverage m n p :=
  qThetaComparison_iff_arithmetic C3 P m n p hTheta hq

/-- **Numeric instance (PROVED arithmetic)**: for `l = 13, p = 11, m = 5`, the
  arithmetic comparison holds; hence, given the two named identifications, the actual
  q/Theta comparison holds. -/
theorem comparison_of_numericInstance
    (hTheta : thetaPilotHullLogVolumeReal C3 = processionAverage 5 6 (11 : ℝ))
    (hq : qPilotLogVolumeReading P = qPilotArithmeticVolume 5 6 (11 : ℝ)) :
    qPilotLogVolume C3 P ≤ thetaPilotLogVolume C3 :=
  (comparison_iff_arithmetic C3 P hTheta hq).mpr (numeric_l13_p11_m5)

/-! ## 3. The StepXI contract from the two different readings -/

/-- The signed readings on the actual C3 input: the paper q reading and Theta reading
  (DIFFERENT objects) together with the comparison.  The field `comparison` is either the
  named candidate (S3137) or supplied by `comparison_of_numericInstance`; it is never
  replaced by a same-region identity. -/
structure SignedReadings where
  /-- The signed q-pilot reading `-|log q|`. -/
  qSigned : ℝ
  /-- The signed Theta-pilot hull reading `-|log(Theta)|`. -/
  thetaSigned : ℝ
  /-- Paper q reading (S3137). -/
  qSigned_eq : qSigned = qPilotLogVolume C3 P
  /-- Paper Theta reading (S3137). -/
  thetaSigned_eq : thetaSigned = thetaPilotLogVolume C3
  /-- The q reading is negative. -/
  qSigned_neg : qSigned < 0
  /-- The paper comparison `-|log q| <= -|log(Theta)|` (named candidate / numeric
  instance); NOT a same-region identity. -/
  comparison : qSigned ≤ thetaSigned

/-- The comparison from the numeric instance (named identifications supplied). -/
def signedReadingsOfNumericInstance
    (hTheta : thetaPilotHullLogVolumeReal C3 = processionAverage 5 6 (11 : ℝ))
    (hq : qPilotLogVolumeReading P = qPilotArithmeticVolume 5 6 (11 : ℝ))
    (hneg : qPilotLogVolume C3 P < 0) : SignedReadings C3 P where
  qSigned := qPilotLogVolume C3 P
  thetaSigned := thetaPilotLogVolume C3
  qSigned_eq := rfl
  thetaSigned_eq := rfl
  qSigned_neg := hneg
  comparison := comparison_of_numericInstance C3 P hTheta hq

/-- The StepXI contract from the signed readings: q/Theta slots are the two DIFFERENT
  paper readings and the ordering is the comparison field. -/
def signedContract (D : SignedReadings C3 P) (ipl she apt : Prop)
    (hipl : ipl) (hshe : she) (hapt : apt) : StepXIContract where
  qSigned := D.qSigned
  thetaSigned := D.thetaSigned
  targetSigned := D.qSigned
  q_negative := D.qSigned_neg
  ipl := ipl
  she := she
  apt := apt
  ipl_evidence := hipl
  she_evidence := hshe
  apt_evidence := hapt
  q_le_target := le_rfl
  target_le_theta := D.comparison

/-- Cor 3.12 ordered conclusion from the (corrected) signed readings. -/
theorem cor312Conclusion_of_signedReadings (D : SignedReadings C3 P)
    (ipl she apt : Prop) (hipl : ipl) (hshe : she) (hapt : apt) :
    Cor312Conclusion (signedContract C3 P D ipl she apt hipl hshe hapt) :=
  cor312_of_constructed_stepXI _

end

end LeanFormal.IUT.XiFPaper.Mzk1SignedCor312AssemblyActual