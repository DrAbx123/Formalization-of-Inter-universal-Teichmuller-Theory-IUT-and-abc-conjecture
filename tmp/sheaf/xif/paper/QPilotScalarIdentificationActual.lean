import tmp.sheaf.xif.paper.QPilotObjectActual
import tmp.sheaf.xif.PaperQPilotLogVolume
import tmp.sheaf.xif.PaperXiFInclusion

/-! # Actual q-pilot scalar identification

This file closes one of the exact q-pilot identifications: for the actual
paper q-pilot object surface `PaperQPilotObjectActual`, the signed q-pilot
log-volume is definitionally the actual source q scalar `localSignedLog C3.q`.
It is thus the paper q-pilot log-volume `paperQPilotLogVolume C3`, not a
theta-label-1 surrogate. No inhabitant of the object is asserted.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.N8Closure.PaperQPilotObjectActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotLogVolume

universe ua uv upi umon ui uL

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {Label : Type uL} [Group Label]

/-- The q-pilot object's signed log-volume is the actual paper q-pilot scalar. -/
theorem signedQPilotLogVolume_eq_paperQPilotLogVolume
    (P : PaperQPilotObjectActual (l := l) (I := I)) :
    P.signedQPilotLogVolume = paperQPilotLogVolume P.line.C3 :=
  rfl

/-- The q-pilot object's scalar is -|log q| for the actual source completion q. -/
theorem signedQPilotLogVolume_eq_neg_abs_qParameter
    (P : PaperQPilotObjectActual (l := l) (I := I)) :
    P.signedQPilotLogVolume =
      -|Real.log (‖P.line.C3.q.q‖)| := by
  rw [signedQPilotLogVolume_eq_paperQPilotLogVolume]
  exact LeanFormal.IUT.XiFPaper.paperQPilotLogVolume_eq_neg_abs_paperQParameter P.line.C3

/-- The q-pilot object's signed log-volume is nonpositive. -/
theorem signedQPilotLogVolume_nonpos
    (P : PaperQPilotObjectActual (l := l) (I := I)) :
    P.signedQPilotLogVolume ≤ 0 :=
  le_of_lt P.signedQPilotLogVolume_neg

/-- The paper q-pilot magnitude is positive. -/
theorem qPilotLogMagnitude_pos
    (P : PaperQPilotObjectActual (l := l) (I := I)) :
    0 < P.qPilotLogMagnitude :=
  neg_pos.mpr P.signedQPilotLogVolume_neg

end LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
end