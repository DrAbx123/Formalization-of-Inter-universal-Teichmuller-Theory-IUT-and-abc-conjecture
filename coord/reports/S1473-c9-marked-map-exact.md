# S1473: C9 paper marked map exact first field

Date: 2026-10-31
Lean: tmp/sheaf/xif/paper/S1473C9MarkedMapActual.lean
EXIT=0; SHA256 A2A7E7A733BE9F97D5FC6B741D088FC19DD2B27847487D99206DDD44E6E19F32
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S1473C9MarkedMapActual.olean

## Exact first field

S1473PaperMarkedMap I v R n:
  Carrier : Type
  u_qv : I.ThetaPilotPoint v -> Carrier
  g_q : Carrier -> Real
  finalEvaluationFamily : Set Carrier
  qMark_mem_finalEvaluationFamily :
    u_qv (qMark I v R n) in finalEvaluationFamily
  g_q_qMark :
    g_q (u_qv (qMark I v R n)) = I.sourceQPilotLogVolume v R n
  finalFamily_bound :
    forall x in finalEvaluationFamily, g_q x <= I.sourceThetaHullLogVolume v R n.

The carrier/final family/u_qv/g_q are exact data of the missing paper
C9 §2/§7 construction.  The value-layer possibleThetaPilotImageSet is not
used as the paper final-evaluation family.

## Actual conditional consequences

S1473PaperMarkedMap.comparison:
  I.sourceQPilotLogVolume v R n <= I.sourceThetaHullLogVolume v R n.

S1473PaperMarkedMap.outputReadoutProjection:
  S1447PaperOutputReadoutProjection I v R n finalEvaluationFamily g_q,
via the exact q-mark witness.

No inhabitant of S1473PaperMarkedMap is asserted; no value-layer substitute,
no circular assumption.
