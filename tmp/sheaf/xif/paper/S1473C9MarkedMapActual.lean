import tmp.sheaf.xif.paper.S1447ReportFMarkedTraceActual

-- S1473: C9 §2/§7 paper marked map u_q,v / g_q and restricted
-- final-evaluation family membership, as the exact first field.
-- The carrier and final family are data of the missing paper construction;
-- the value-layer possibleThetaPilotImageSet is NOT used as that family.
-- From exact marked-map data, the fixed-C comparison is actual.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1473C9MarkedMapActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1447MarkedTraceActual

universe ua uv upi umon ui uC

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)

/-- Exact C9 paper marked-map data: a paper final-evaluation carrier;
marked map u_q,v from the actual theta-pilot carrier; readout g_q; the
restricted final-evaluation family; q-mark membership; and the same
readout/bound compatibility.  No inhabitant is asserted. -/
structure S1473PaperMarkedMap where
  Carrier : Type uC
  u_qv : I.ThetaPilotPoint v → Carrier
  g_q : Carrier → Real
  finalEvaluationFamily : Set Carrier
  qMark_mem_finalEvaluationFamily :
    u_qv (qMark I v R n) ∈ finalEvaluationFamily
  g_q_qMark :
    g_q (u_qv (qMark I v R n)) = I.sourceQPilotLogVolume v R n
  finalFamily_bound : ∀ x ∈ finalEvaluationFamily,
    g_q x ≤ I.sourceThetaHullLogVolume v R n

/-- Actual fixed-C comparison from the exact marked-map data. -/
theorem S1473PaperMarkedMap.comparison (M : S1473PaperMarkedMap I v R n) :
    I.sourceQPilotLogVolume v R n ≤ I.sourceThetaHullLogVolume v R n := by
  rw [← M.g_q_qMark]
  exact M.finalFamily_bound _ M.qMark_mem_finalEvaluationFamily

/-- The exact marked map data gives the S1447 paper output-readout projection;
this is the restricted final-evaluation family membership, not the value-layer
possibleThetaPilotImageSet. -/
theorem S1473PaperMarkedMap.outputReadoutProjection
    (M : S1473PaperMarkedMap I v R n) :
    S1447PaperOutputReadoutProjection (I := I) (v := v) (R := R) (n := n)
      M.finalEvaluationFamily M.g_q :=
  Or.inl ⟨M.u_qv (qMark I v R n), M.qMark_mem_finalEvaluationFamily, M.g_q_qMark⟩

#check S1473PaperMarkedMap
#check S1473PaperMarkedMap.comparison
#check S1473PaperMarkedMap.outputReadoutProjection

end LeanFormal.IUT.XiFPaper.S1473C9MarkedMapActual

end