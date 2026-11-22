/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S3137QThetaPilotLogVolumeReadingsActual
import tmp.sheaf.xif.paper.QPilotScalarIdentificationActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange
import LeanFormal.IUT.Foundations.LocalFields.LocalDifferentNormOrder
import Mathlib.Tactic

/-! # A769 hull: explicit q-side expansion of `qPilotLogVolumeReading`

Green inputs:
* `qPilotLogVolumeReading P = P.signedQPilotLogVolume` (S3137);
* `= -|log ||P.line.C3.q.q|||` (`signedQPilotLogVolume_eq_neg_abs_qParameter`);
* q candidate: `qNorm_eq_residueNormBase_zpow`, `localLogMagnitude_eq_order_mul_log`,
  `localLogMagnitude_eq_exponent_mul_log` (ArithmeticQPilotBaseChange).

Explicit closed form:

  `qPilotLogVolumeReading P = -(order * log(residueNormBase place))`
  `= -(exponent * log(residueNormBase place))`,

so the q side is exactly a finite-place order times a residue-norm log. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.Mzk1QSideExplicitActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.N8Closure.PaperQPilotLogVolume
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.LocalDifferentNormOrder
open scoped ENNReal BigOperators

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (P : PaperQPilotObjectActual (l := l) (I := I))

/-- The q-pilot reading is the actual local signed q-log. -/
theorem qPilotLogVolumeReading_eq_localSignedLog :
    qPilotLogVolumeReading P = localSignedLog P.line.C3.q := by
  have hneg : Real.log ‖P.line.C3.q.q‖ < 0 := localSignedLog_neg P.line.C3.q
  rw [qPilotLogVolumeReading_eq_neg_abs_qParameter, abs_of_neg hneg, neg_neg]
  rfl

/-- The q-pilot reading is the log norm of the actual completion q. -/
theorem qPilotLogVolumeReading_eq_log_norm :
    qPilotLogVolumeReading P = Real.log ‖P.line.C3.q.q‖ := by
  rw [qPilotLogVolumeReading_eq_neg_abs_qParameter]
  have hneg : Real.log ‖P.line.C3.q.q‖ < 0 := localSignedLog_neg P.line.C3.q
  rw [abs_of_neg hneg, neg_neg]

/-- **Explicit q-side closed form**: `-(order * log(residueNormBase))`. -/
theorem qPilotLogVolumeReading_eq_neg_order_mul_log :
    qPilotLogVolumeReading P =
      -((P.line.C3.q.order : Real) *
        Real.log (residueNormBase (K := I.initial.arithmetic.Fmod) ((P.line.C3.place).val))) := by
  rw [qPilotLogVolumeReading_eq_log_norm]
  have h := localLogMagnitude_eq_order_mul_log (parameter := P.line.C3.q)
  have hneg : Real.log ‖P.line.C3.q.q‖ = -localLogMagnitude P.line.C3.q := by
    unfold localLogMagnitude localSignedLog
    ring
  rw [hneg, h]

/-- Exponent form of the same closed form. -/
theorem qPilotLogVolumeReading_eq_neg_exponent_mul_log :
    qPilotLogVolumeReading P =
      -((P.line.C3.q.exponent : Real) *
        Real.log (residueNormBase (K := I.initial.arithmetic.Fmod) ((P.line.C3.place).val))) := by
  rw [qPilotLogVolumeReading_eq_log_norm]
  have h := localLogMagnitude_eq_exponent_mul_log (parameter := P.line.C3.q)
  have hneg : Real.log ‖P.line.C3.q.q‖ = -localLogMagnitude P.line.C3.q := by
    unfold localLogMagnitude localSignedLog
    ring
  rw [hneg, h]

/-- The q-pilot reading is strictly negative. -/
theorem qPilotLogVolumeReading_neg' : qPilotLogVolumeReading P < 0 := by
  rw [qPilotLogVolumeReading_eq_log_norm]
  exact localSignedLog_neg P.line.C3.q

/-- The q-pilot reading is nonpositive. -/
theorem qPilotLogVolumeReading_nonpos' : qPilotLogVolumeReading P <= 0 :=
  le_of_lt (qPilotLogVolumeReading_neg' P)

/-- The tensor index cardinality carried by the C3 input. -/
noncomputable def tensorIndexCard {l : PrimeGeFive} {V : Type}
    {I : OriginalInput l V} (C3 : SourcePilotRegionData (l := l) (V := V) I) : Nat :=
  Fintype.card C3.tensorIndex

/-- The q-side dictionary rows for the gap computation. -/
def qSideRows : List (String × String × String) :=
  [ ("q reading", "qPilotLogVolumeReading P = -|log ||P.line.C3.q.q|||", "S3137 / QPilotScalarIdentification (GREEN)"),
    ("q log norm", "= Real.log ||P.line.C3.q.q|| = localSignedLog P.line.C3.q", "PROVED"),
    ("q order form", "= -(order * log(residueNormBase place))", "PROVED (localLogMagnitude_eq_order_mul_log)"),
    ("q exponent form", "= -(exponent * log(residueNormBase place))", "PROVED"),
    ("q sign", "strictly negative", "PROVED"),
    ("tensor index", "Fintype.card C3.tensorIndex (no green equality with nC for a general C3)", "DEF / GAP") ]

theorem qSideRows_length : qSideRows.length = 6 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1QSideExplicitActual.qPilotLogVolumeReading_eq_neg_order_mul_log
#print axioms LeanFormal.IUT.XiFPaper.Mzk1QSideExplicitActual.qPilotLogVolumeReading_eq_neg_exponent_mul_log
#print axioms LeanFormal.IUT.XiFPaper.Mzk1QSideExplicitActual.qPilotLogVolumeReading_neg'

end LeanFormal.IUT.XiFPaper.Mzk1QSideExplicitActual

end