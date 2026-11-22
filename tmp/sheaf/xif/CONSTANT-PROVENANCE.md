# xi-f constant provenance audit

Date: 2026-10-28

## Question

Are the numerical constants in the xi-f construction genuine project constants, or arbitrary toys?

## 1. gaussianFiveThetaQ / 1/5

- Definition: LeanFormal/IUT/IUTI/HodgeTheater/ConcreteIntegralHodgeTheaterExample.lean:27
  `gaussianFiveThetaQ := ||(localQParameterFor 5 : AlgebraicClosure Q_5)||`.
- Theorem: LeanFormal/IUT/IUTII/Frobenioid/Example36SourceTheaterCarrier.lean:178
  `gaussianFiveThetaQ_eq_inv_five : gaussianFiveThetaQ = (5:Real)^{-1}`.
- Source theater packet: LeanFormal/IUT/IUTII/Theta/ConcreteSourceEtaleThetaBridge.lean:571
  `theta_packet_q : (theater l).thetaPacket.q = gaussianFiveThetaQ`.
- Consumers in xi-f:
  - ThetaPacketContractionProof.lean sourceTheater_theta_q_eq (now stated with gaussianFiveThetaQ)
  - ThetaPacketQIdentificationActual.lean c3WithSourceTheaterTheta_q
  - ThetaPacketQIdentificationProof.lean sourceTheaterC3_thetaPacket_q
  - PaperThetaMagnitudeActual.lean uses source-theater C3 with q=1/5
  - PaperThetaQNormRelation only holds if qNormOfC3 = gaussianFiveThetaQ; no arbitrary universal 1/5.

Verdict: 1/5 is the actual source-theater q constant, not a toy. It is not universal: FiniteThetaPacket.ofQ 2 has q=2, and no theorem identifies an arbitrary C3.thetaPacket.q with 1/5.

## 2. Uniform weight 1/card

- Definition: SignedHullNormalizationActual.procession weight = (Fintype.card (sourceFiniteLabel l):Real)^{-1}.
- Used for the actual procession average; no arbitrary weight chosen.

## 3. Other constants

- 0 and 1 are literal arithmetic identities (log 1 = 0, positivity, etc.).
- card(SignedLabel) is actual Fintype cardinality.
- tensor prime p in C3 donor is from completionRationalPrime/native bad base place, not fixed.

## 4. Rule

A constant is accepted only if it is defined from an actual source object or proved equal to one. Raw magic constants are replaced by named actual constants (gaussianFiveThetaQ) or removed. The source-theater constant is not promoted to an arbitrary C3.
## 5. Important correction: 1/5 is not the xi-f q


## 2026-10-28 CRITICAL: source-theater q=1/5 does NOT satisfy signed xi-f bound

- SignedAverageBoundActual.lean computed actualSignedC3 signed average exactly:
  average = log 5 * (gaussExponentSum / card).
  For l=5: gaussExponentSum = 10, card = 5, so average = 2 log 5 > log 5.
- If C3 completion q also has magnitude log 5 (q=1/5), SignedThetaAverageLeQMagnitude is FALSE.
- Therefore sourceTheater q=1/5 is an actual Example36/source-theater constant, but it cannot be used as the paper xi-f q donor for this signed hull. The earlier C3 construction fixing thetaPacket to sourceTheater does not automatically satisfy xi-f; the C3 completion q is independent donor data and must be smaller (|log q| >= 2 log 5 for l=5) or the theta packet must differ.
- Do not assert SignedThetaAverageLeQMagnitude from q=1/5. Keep it exact missing/possibly false for this model.
- Constant audit remains: gaussianFiveThetaQ=1/5 is genuine source-theater data but not universal paper q.

## 6. Correction: no inequality judgments before actual objects


## 2026-10-28 USER CORRECTION: inequality judgments before actual objects are meaningless

- The source-theater q=1/5 signed-average computation (2 log 5) is a computation in a CONDITIONAL source-theater model, not a judgment about paper xi-f.
- SignedThetaAverageLeQMagnitude / PaperThetaMagnitudeComparison are conditional propositions over abstract C3/PaperSignedHull/procession data. Until the actual unconditional C3 donor, base q, tensor landing, procession and hull objects are constructed, asserting or rejecting these inequalities is not meaningful.
- Therefore SignedAverageBoundActual is retained only as a conditional model calculation; it is NOT evidence that paper xi-f is false, and the q=1/5 route is NOT to be used as a decision about the target.
- Work priority: construct actual unconditional objects first (C3 donor/base q/tensor landing/theta packet/procession/hull); only then evaluate the concrete inequality.
- No shortcuts.
