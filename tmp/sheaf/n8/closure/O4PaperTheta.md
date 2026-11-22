# O4 paper Theta/ellOut from SourceInitialThetaData

Date: 2026-10-24. Owner: logdescent. Lean: O4PaperTheta.lean.
Compile: lake env lean -j1 -R D:/lean -> EXIT=0, zero sorry.

Paper input: SourceInitialThetaData l.  No SourceDefinition31Data shell is
used.

Actual projections: paperArithmetic = S.candidate.arithmetic; paperV =
S.candidate.V; paperPlace = S.candidate.place; paper_bad_nonempty from
clause B.

Paper Theta/ellOut from actual C6 SourceAllowedOutput J:
- PaperTheta := actual C6 hull log-volume B.iqInterface.logVolume B.hull;
- PaperEllOut := actual C6 region log-volume;
- paperEllOut_le_paperTheta unconditional from J.hullPoss and actual C6
  logVolume monotonicity;
- PaperThetaReal/PaperEllOutReal from actual normalized C6 readouts;
- exact gap package PaperThetaGapData (paper arithmetic compatibility,
  hullPoss, actual C6 normalization, region-positive/hull-finite);
- paperEllOutReal_le_paperThetaReal_of_gapData conditional from that package;
- PaperThetaDataGap is the remaining paper-data obligation, not asserted.

No arbitrary J/Theta; no shell conversion.