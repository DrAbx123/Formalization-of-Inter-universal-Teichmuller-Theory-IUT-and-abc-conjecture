# S2137: paper hull normalization reduction

Date: 2026-11-02. Layer O; consumer S2040 paper 3.12.

## Actual

PaperSignedHull gives

  signedHullLogVolume = -ambient hull log-volume
                      = -average   (under hull_logVolume_eq_average).

New Lean:

  s2137_signedHull_eq_log_rootStackTheta_of_average
    (h : P.procession.average = -Real.log rootStackTheta) :
    P.signedHullLogVolume = Real.log rootStackTheta

  s2137_signedHull_eq_log_rootStackTheta_of_ambient
    (h : (P.ambient.logVolume P.ambient.hull).toReal = -Real.log rootStackTheta) :
    P.signedHullLogVolume = Real.log rootStackTheta

These are actual reductions with axioms propext, Classical.choice,
Quot.sound.  They do not assume the paper hull normalization; they make
its exact scalar input explicit.

## Exact first missing

To instantiate the paper hull normalization one must prove, for the actual
S2040/S2057 data,

  s2137HullAverageNormalization P rootStackTheta
    : P.procession.average = -Real.log rootStackTheta.

Equivalently, identify

  P.ambient.logVolume P.ambient.hull
    = ENNReal.ofReal (-Real.log rootStackTheta)

with the actual root hull normalized log:

  paperRootThetaHullLog T b Measure.addHaar

and then use S2057 rootStackTheta (rootNormedElementNorm).  Current exact
gaps:

- RootThetaHullNormalizationGap (root hull Haar positivity/finiteness,
  hull_eq minimal region, ArithmeticTuplePureFractionalScalingData);
- PaperRootHullFormulaGap (paper coefficient family hull_eq + scaling data);
- the actual identification of P's ambient hull with the paper root hull
  and of P.procession.average with -log rootStackTheta.

No inhabitant of these gaps is asserted, and S2040ThetaLink312 is not
assumed completed.

## Lean file

tmp/sheaf/xif/paper/S2137PaperHullNormalizationActual.lean
SHA256 A05C8E9B23B07E904EB61A7E7E42A4825DD98C151AFF3C8CA9B9DE0116E0F4CF
EXIT=0
olean SHA256 D8D2BDFC895277E3E14087EF0E261BF14E784907E53E0EFC0F27C20A975E6E23
size 21208
axioms propext, Classical.choice, Quot.sound.

## Conclusion

- BUILT: exact reduction from average/ambient hull normalization to
  P.signedHullLogVolume = log rootStackTheta.
- MISSING: the actual average/hull identification, recorded as
  s2137HullAverageNormalization; downstream RootThetaHullNormalizationGap /
  PaperRootHullFormulaGap.
- no fake; no S2040 goal assumed.
