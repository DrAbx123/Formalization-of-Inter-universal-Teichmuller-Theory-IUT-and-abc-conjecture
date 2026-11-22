# Sign audit for the xi-f formalization

Date: 2026-10-29.  Status: compile/status audit; no new inequality claimed.

## 1. Canonical signs

The paper signed q-pilot log is

    paperSignedLog q = -|Real.log q|.

If 0 < q <= 1 then log q <= 0 and paperSignedLog q = log q.

Let

    Q = nativeGlobalQPilotNormalizedLogMagnitude T   (Q >= 0),
    signedQ = -Q.

Let TTheta >= 0 be a positive Theta-hull log-volume.  Its signed paper value is

    signedTheta = -TTheta.

Corollary 3.12 is

    -|log Theta| >= -|log q|
    <=> signedTheta >= signedQ
    <=> -TTheta >= -Q
    <=> TTheta <= Q.

The paper-level xi-f statement is

    paperXiF q signedTheta  <=>  paperSignedLog q <= signedTheta.

## 2. Verified sign-correct files

| file | sign content | compile |
|---|---|---|
| PaperXiFSpec.lean | paperSignedLog = -|log q|; paperXiF q theta = paperSignedLog q <= theta | existing olean |
| PaperXiFGlobalDirectActual.lean | q = exp(-M), M >= 0, log q = -M, paperSignedLog q = -M; paperXiF iff signed volume <= theta | EXIT=0, olean=True |
| PositiveHullVsQPilotCorrectedActual.lean | positive T <= Q; signed form -Q <= -T; proved equivalent | EXIT=0, olean=True |
| GlobalPositiveHullPaperXiFActual.lean | q = exp(-Q), signedTheta = -T; paperXiF iff T <= Q | EXIT=0, olean=True |
| GlobalHullPaperXiFActual.lean | q = exp(I.qPilotSignedLogVolume), q <= 1, paperSignedLog q = log q; fixed from -log to log | EXIT=0 |
| GlobalHullSignedComparisonActual.lean | signed comparison iff magnitude bound T <= Q | EXIT=0, olean=True |
| SourceHullVolumeSignCorrectedActual.lean | positive point log = -sourceLocalLogDegree; old sourcePointVolume = 0 under theta < 1 | EXIT=0, olean=True |

## 3. Rejected sign/object routes

- Old sourcePointVolume = ENNReal.ofReal sourceLocalLogDegree is 0 for theta values < 1.  Any qSigned <= 0 conclusion from it is a value-layer truncation shortcut, not paper xi-f.
  SourceHullVolumeSignCorrectedActual proves the zero fact explicitly.
- Raw sum of theta values gives TTheta = coefficient * Q with coefficient 2 at l=5, so TTheta <= Q is false; it is not the paper hull.
- Comparing a negative signed scalar with a positive magnitude is trivial and is not the paper direction.
- The local/global q equality and carrier equivalences are not prerequisites for the signed comparison.

## 4. Remaining actual condition

The only remaining mathematical input in the sign-correct reduction is

    globalPositiveThetaHullLogVolume I R n <= nativeQPilotComparisonMagnitude T.

GlobalPositiveHullPaperXiFActual proves that, given this comparison,
paperXiF holds at the actual global q parameter.  The comparison itself is not
asserted or proved.

No sorry, axiom, True, PUnit, or toy object is used in the audit files.
