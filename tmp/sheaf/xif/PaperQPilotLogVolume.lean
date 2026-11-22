import tmp.sheaf.n8.closure.C9Paper
import tmp.sheaf.n8.closure.SourcePilotRegion
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume

/-! # Paper q-pilot signed log-volume

This file constructs the actual signed q-pilot log-volume from the source
completion q in SourcePilotRegionData, not from the theta-label-1 value-layer
surrogate sourceQPilotLogVolume / card.

The actual source q scalar is C3.q : FinitePlaceQCandidate C3.place.val.
C9QPaper.qPaperScalar C3 = localSignedLog C3.q is the signed log
Real.log ||C3.q.q|| (negative for the contracting q).  Its negative is the
paper magnitude |log q|.

The file proves:
* the signed q-pilot volume equals the actual completion log-norm;
* it is negative;
* its negative magnitude is positive and equals localLogMagnitude C3.q;
* it is exactly the C9Paper.QPaper.qPilotLogVolume of a QPaper built from the
  same C3 (definitional scalar connection);
* its negative magnitude is the local log magnitude of the actual q.

Exact source gate: the paper q-pilot object at (1,0) (arithmetic line bundle,
log-Kummer representation, q-pilot possible image) is not constructed by this
log-volume file.  That object is task-493's PaperQPilotObject.  This file only
constructs and identifies the signed q-side log value from the actual source
q; it does not identify it with the theta-label-1 surrogate and does not claim
paper xi-f.

No sorry, no axiom, no toy structure. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.N8Closure.PaperQPilotLogVolume

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.C9Paper
open LeanFormal.IUT.ArithmeticQPilotLogVolume

universe ua uv upi umon ui uL

variable {l : PrimeGeFive} {V : Type uv}
variable {I : Theorem311Source.OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- The actual signed q-pilot log-volume -|log q| from the source completion
q.  It is localSignedLog C3.q, the negative log of the q norm. -/
def paperQPilotLogVolume : Real :=
  localSignedLog C3.q

/-- The paper q-pilot magnitude |log q| = -(-|log q|). -/
def paperQPilotLogMagnitude : Real :=
  - paperQPilotLogVolume C3

/-- The signed q-pilot volume is the actual completion log-norm. -/
theorem paperQPilotLogVolume_eq_log_norm :
    paperQPilotLogVolume C3 = Real.log ‖C3.q.q‖ :=
  rfl

/-- The q-pilot signed volume is negative. -/
theorem paperQPilotLogVolume_neg : paperQPilotLogVolume C3 < 0 :=
  localSignedLog_neg C3.q

/-- The signed volume is the negative of the local log magnitude. -/
theorem paperQPilotLogVolume_eq_neg_magnitude :
    paperQPilotLogVolume C3 = -localLogMagnitude C3.q :=
  localSignedLog_eq_neg_magnitude C3.q

/-- The paper magnitude is positive. -/
theorem paperQPilotLogMagnitude_pos : 0 < paperQPilotLogMagnitude C3 := by
  unfold paperQPilotLogMagnitude
  exact neg_pos.mpr (paperQPilotLogVolume_neg C3)

/-- The magnitude is the actual local log magnitude. -/
theorem paperQPilotLogMagnitude_eq_localLogMagnitude :
    paperQPilotLogMagnitude C3 = localLogMagnitude C3.q := by
  unfold paperQPilotLogMagnitude
  rw [paperQPilotLogVolume_eq_neg_magnitude]
  ring

/-- The q-pilot signed volume of a QPaper built from the same C3 is exactly this
signed value.  This is the definitional QPaper/q-scalar connection. -/
theorem paperQPilotLogVolume_eq_QPaper_qPilotLogVolume
    {Label : Type uL} [Group Label]
    {D : ABCBridge.N8.C4Actual.SourceWitnessedOutputData (l := l) (V := V) I Label}
    {C1 : N8Closure.SourceInputBinding.SourceInputBinding I}
    {C2 : N8Closure.SourceLogKummerRealization.SourceLogKummerData I C1}
    (Q : N8Closure.C9Paper.QPaper (D := D) (C1 := C1) (C2 := C2) (C3 := C3)) :
    Q.qPilotLogVolume = (paperQPilotLogVolume C3 : WithTop Real) := by
  rw [Q.qPilotLogVolume_eq, Q.scalar.value_eq]
  rfl

end LeanFormal.IUT.N8Closure.PaperQPilotLogVolume

end
