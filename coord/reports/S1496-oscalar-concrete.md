# S1496: concrete O scalar conditions

Date: 2026-10-31
Lean: tmp/sheaf/xif/paper/S1496OScalarConcreteActual.lean
EXIT=0; SHA256 6B272C3F06594DF42B7EC0CA314A75E770E101C6957C4E73B62224414BB352F6
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S1496OScalarConcreteActual.olean

## Actual conditional implications

S1496QNormOneFifth C3 : Prop := ‖C3.q.q‖ = 1/5.

s1496SignedHull_of_qNorm_oneFifth D C3 hq:
  OrigXiFOSignedHullExactField I D C3,
  i.e. signedHull_le for every actual D.

s1496QPilotLogVolume_le_neg_one_of_qNorm_oneFifth C3 hq:
  OrigXiFPaperQPilotLogVolume C3 <= -1.

S1496SourceBadQFormula C3 : Prop :=
  -sourceBadQAbsLog I.initial = Real.log ‖C3.q.q‖.

s1496ScalarExact_of_sourceBadQFormula O C3 h:
  OrigXiFOScalarExactField I O C3.

s1496ThetaLinkActual O D C3 hq hbad :
  OrigXiFThetaLinkActual O D C3.

## Exact remaining (not asserted)

- S1496ConcreteQNormRequired C3: the concrete S1280/S1321/
  actualSourcePilotRegionDataL q has norm exactly 1/5.  The actual
  concreteQCandidate is a Classical choice of FinitePlaceQCandidate; its
  order is only positive, so norm 1/5 is not derived here.
- S1496ConcreteSourceBadQRequired C3: the concrete sourceBadQAbsLog equals
  log of the C3 norm (equivalently the q order/order=1 branch of S1280).

No inhabitant of either exact condition is asserted; no fake concrete
Gaussian instance.  The conditional structure is actual.
