# P7 Route N0–N11 Asset Map (correction after duplication audit)

Date: 2026-11-15 20:05 (Asia/Shanghai)
Purpose: stop re-deriving already-green N5/N6 assets. Mainline is coord/P7-GLOBAL-Q-HULL-CONSTRUCTION-20261115.md; cards/S3135 are auxiliary.

## Nodes

### N0 01 Actual Frey curve / local height
- Existing donors: ABCEllipticHeightCriterion, FreyTateAnalyticInput, Frey/local height files.
- Status: actual parameter producer partially; no unconditional T yet.

### N1 02 Actual Tate q
- Existing: TateQSeriesCoefficients, TateQSeriesEval, TateQSeriesGeneral, TateQSeriesAnalytic (Prop).
- Missing: TateJQSeriesAnalyticAtFive (analyticity at q=5 + deriv != 0). Mathlib chain identified: ofScalars -> hasFPowerSeriesOnBall -> le_radius_of_bound -> analyticAt; helper norm_padicPowerSeriesEval_le_one needed.
- Construction file active: Node09TateQSeriesAnalyticPartialActual.

### N2 03 Actual quotient stack / groups
- Existing: A2 node03 interfaces/consumers, quotient-stack producer/consumer, integration files.
- Missing: actual quotient stack/group G2 producer. Interfaces only.

### N3 04 Local transport / unit quotient
- Existing: RelativeNormCompletion, PadicField.nrm_norm/v_norm, Fmod transport interface, tensor unit ball interface, WQ interfaces.
- In progress: Mzk1A2Node04TensorUnitBallInhabitant (using arithmeticTensorBlocksAlgEquiv), WQUniformizerAssociated range route.
- Missing: RelativeNormQProperties inhabitant; ValueGroup0.embedding unit lemma; actual tensor decomposition? (new donor exists).

### N4 05 Choose l / qualified Theta-data
- Existing: prime avoidance / large image partial donors (S2020, S2835 only conditional).
- Missing: actual l selection + qualified initial data producer.

### N5 06 Global q divisor / product volume  (ALREADY LARGELY DONE)
- DONE donors:
  * S3133RealifiedQPilotDivisorActual (qVEffectiveMultiplicity = order * localResidueDegree)
  * S3133RealifiedQPilotLogVolumeActual (qPilotRealifiedLogVolume = -sum mult_b log residueNormBase)
  * QPilotGlobalLogVolumeFromQActual
  * Mzk1QVWeightedActual: MqFiber, MqFiber_eq_sum_localLog, actual_A_le_Lbar_add_Dbar_of_fiberMult
  * Mzk1QVFiberWeighted: hfr/hreindex; MqFiber_eq_badWeighted_of_fiber
  * Node09HqAssemblyLink: paper312_of_fiberMult_bounds / paper312_of_MqFiber_bounds
  * Mzk1QVRealifiedBridge (new 11:59:12): qPilotRealifiedLogVolume_eq_neg_MqBad / _neg_fiberWeighted
- Missing:
  * C3BaseQElementIdentification
  * ClauseBBaseQSourceIdentity / BaseChangeQElementCorrespondence
  * MissingQPilotOneColumnReading (represented region reading)
  * MissingRealifiedGlobalFrobenioidPresentation
  * WeightedQSumBridge
- Do NOT re-derive S3133/QVWeighted/MqFiber bridges.

### N6 07 Source action / theta source image / hull
- Existing: Qpilot region/rpRegion/rootExtensionHaar donors; S3133 readout conditional; Node09PM7SNamed.
- Missing: actual Ind1/Ind2 source action; represented-region reading; theta hull actual image.

### N7 08 Same-source signed reading 3.12
- Existing: Node09Paper312Weight, Node09HqAssemblyLink, Node09HperInput, Node09HlogpTransport, Node09AbsNormRat, Node09ResidualInputs, Node09FinalConditional.
- Status: conditional 3.12 endpoint green; cards auxiliary.

### N8 09 IV Box / Thm 1.10
- Existing: S3135 conditional endpoint, Card U unconditional, F5 only Card P, F4 cards exact.
- Missing: Card P/hpoint/frozen gap2; S3135PointLogShellFaithfulness; ScalingLogDegreeZero arbitrary D.

### N9 10 Local-to-global / uniform epsilon
- Existing: conditional bridges.
- Missing: actual paper inputs above.

### N10 11 Frey j-height criterion
- Existing: ABCEllipticHeightCriterion consumer.
- Missing: actual (T) input.

### N11 ABC
- Existing: conditional abcConjecture_of_* only.
- No ABCConjecture/ABCFrontier inhabitant (Node09ABCInhabitantScan 06:12:11).

## Duplication rules
- Before creating a new bridge, grep GOAL-PROGRESS/AUDIT_LEDGER for S3133, QVWeighted, MqFiber, Node09HqAssemblyLink.
- New file must name the existing donor it consumes.
- N5 new work only: C3/base identities and the 4 reading bridges above.
