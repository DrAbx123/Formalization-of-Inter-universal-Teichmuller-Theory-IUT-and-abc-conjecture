# S1129: S1122 source-comparison target audit

Date: 2026-10-30. Audit + exact conclusion.

## Files read

* S1122ProductSourceComparisonActual.lean: EXIT=0; targets checked.
* ConcreteSignedHullActual.lean: read; actual concrete signed hull built from
  normalized Haar and actual signed C3/Gaussian theta packet.
* ConcreteGlobalPilotDataActual.lean: read; local compile currently blocked
  because C3GaussianThetaPacketActual.olean is absent in this workspace.
  Source confirms:
  - q side is the actual bad q family I.initial.reduction.qParameter;
  - theta side in this file is the fixed source-theater local q=1/5 Gaussian
    packet (actualGaussianThetaPacket), explicitly marked LOCAL PROTOTYPE;
  - paper Remark 3.1.1(ii) procession-normalization weights are not
    constructed (PaperProcessionNormalizationWeights obstruction).

## S1122 target audit

S1122ProductComparison P :=
  P.procession.average <= sourceBadQAbsLog I.initial.

Its counterexample:
  hPavg : P.procession.average = log 25
  hsource : sourceBadQAbsLog I.initial = log(25/24)
  -> not concreteSourceComparison O P.

This is a real arithmetic counterexample to comparing the q_v-product absolute
log sum against an ARBITRARY signed-hull average set to log 25.  It does not use
the paper q_v Theta side.

## Does the paper q_v product comparison need a q_v Theta side?

YES.  The paper comparison cannot pair the q_v product with:
* an arbitrary P.procession.average (S1122's P can be any PaperSignedHull);
* the fixed q=1/5 Gaussian/source-theater local theta packet
  (actualGaussianThetaPacket, marked LOCAL PROTOTYPE), which is not the q_v
  theta data.

The correct paper object must use the Theta side built from the same q_v family:
per-b q_v theta coefficients/order data, e.g. the actual qVFamily/order-based
theta tensor coefficients (qVFamThetaTensorCoefficient /
qVFamPaperThetaTensorCoefficient) and the corresponding theta hull scalar
(paperRootThetaHullLog/globalThetaHullLog), not the fixed q=1/5 packet.

## Exact missing bridge

Existing actual pieces:
* source q_v family and sourceBadQAbsLog (actual);
* qVFamily order coefficients and qVFamThetaTensorCoefficient (actual);
* paperRootThetaHull/paperRootThetaHullLog constructed from qVFam order data
  (actual, conditional inputs).
Missing exact:
1. identification of the source q_v family I.initial.reduction.qParameter with
   the qVFamily T b data used by qVFamThetaTensorCoefficient;
2. the corresponding q_v-dependent theta hull scalar and its comparison with
   sum_b |log q_b|.
Without (1)/(2), S1122's counterexample is only about the wrong/fixed theta
object, not the paper comparison.

## Fake scan

S1122 source: no sorry/axiom/True/PUnit/unsafe/admit.
S1129 audit file EXIT=0; no fake.

## Status

S1122 EXIT=0 and its counterexample is valid for its stated arbitrary-P/fixed
theta target.  Paper q_v product comparison remains an exact gap requiring the
q_v Theta side; S1122 does not refute it.
