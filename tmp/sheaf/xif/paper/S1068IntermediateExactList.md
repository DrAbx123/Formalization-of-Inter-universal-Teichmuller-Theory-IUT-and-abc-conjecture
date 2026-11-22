# S1068: INTERMEDIATE (NOT paper) + exact paper target list

Date: 2026-10-30. Correction.

## Status

S1068 fallback is INTERMEDIATE ONLY.  It uses
PaperLevelXiFTargetProofActual, i.e. the c_norm spectral model:

* qPilotSigned = globalQPilotLog (qPilotClassicalLog, c_norm);
* thetaHullSigned = globalThetaHullLog (rootNormHull, c_norm/(2l)).

It must NOT be cited as the paper target.

## Correct paper target

  canonical qPilot (order)
    <= root-stack theta hull (order/(2l))

in signed-log form.

## Exact object list

Canonical qPilot (order):
* qVFamily T b : FinitePlaceQCandidate;
* qVFamily.order : Nat (actual order coefficient);
* qVFamTensorCoefficient T b = order(qVFamily T b);
* actual qPilot signed scalar candidate:
  sourceQPilotSignedLog I.initial
  (and O.qPilotLogVolume = sourceQPilotSignedLog I.initial for concreteO);
* if a qPilot signed scalar built from order is used, its bridge to
  sourceQPilotSignedLog must be supplied; not derived here.

Root-stack theta hull (order/(2l)):
* qVFamPaperRootCoefficient T b = order(qVFamily T b)/(2l);
* paperRootCoefficientFamily T b = fun _ => qVFamPaperRootCoefficient T b;
* rootThetaRegion cRoot j;
* paperRootThetaHull T b = closure(union_j rootThetaRegion cRoot j);
* paperRootThetaHullNonzero T b for the nonzero-label version;
* paperRootThetaHullLog / paperRootThetaHullLogNonzero: normalized log of that
  hull (signed value is -hull log);
* S782 stackRootSection / stackQSection: divisor coordinates
  order/(2l) and order, with stackRootSection_pow;
* S859 paperIntrinsicLogVolume_root = order/(2l) * log p (actual).

Required exact data/proofs for the paper target:
1. canonical qPilot signed scalar from order / source q; exact bridge to
   sourceQPilotSignedLog if not definitional;
2. root-stack theta hull with coefficient order/(2l) (paperRootThetaHull or
   paperRootThetaHullNonzero), on the finite root-stack extension;
3. signed inequality qPilotSigned <= -paperRootThetaHullLog
   (or the corresponding signed hull value);
4. containment/positivity/finiteness inputs actually used by the chosen
   log-volume monotonicity proof.

## Missing requested chain

S1062-S1066 are absent.  An assembly using exactly those files cannot be
performed in this tree.

## No fake

No c_norm model is renamed as paper.  No equality/scaling is fabricated.
