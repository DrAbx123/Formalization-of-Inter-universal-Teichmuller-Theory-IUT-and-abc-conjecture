import tmp.sheaf.xif.paper.S1473C9MarkedMapActual
import tmp.sheaf.xif.paper.S1447ReportFMarkedTraceActual

/-! # S2475: actual S1473 value-layer marked-map inhabitant

S1473PaperMarkedMap is an abstract Carrier/finalEvaluationFamily structure.
The actual value-layer data of S1447 (ThetaPilotPoint, allowedOutputSource,
readout) gives a genuine inhabitant under the hull boundedness field.  Its
Carrier is the value layer, NOT ActualOutput R, so it does not construct the
paper P_C; that is the exact missing object. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S2475S1473ValueLayerActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1447MarkedTraceActual
open LeanFormal.IUT.XiFPaper.S1473C9MarkedMapActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)

/-- The actual value-layer marked map: Carrier = ThetaPilotPoint, id marking,
allowedOutputSource as family, readout as g_q. -/
noncomputable def s2475ValueLayerMarkedMap
    (hBdd : BddAbove (I.sourceThetaHullLogValueSet v R n)) :
    S1473PaperMarkedMap I v R n where
  Carrier := I.ThetaPilotPoint v
  u_qv := id
  g_q := readout I v
  finalEvaluationFamily := allowedOutputSource I v R n
  qMark_mem_finalEvaluationFamily := qMark_mem_allowedOutputSource I v R n
  g_q_qMark := readout_qMark I v R n
  finalFamily_bound := by
    intro x hx
    exact le_csSup hBdd ⟨x, allowedOutputSource_subset_hull I v R n hx, rfl⟩

#check s2475ValueLayerMarkedMap

end LeanFormal.IUT.XiFPaper.S2475S1473ValueLayerActual
end
