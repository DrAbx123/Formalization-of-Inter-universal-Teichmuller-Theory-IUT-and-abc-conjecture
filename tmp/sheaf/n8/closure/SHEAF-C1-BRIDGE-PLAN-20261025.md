# SHEAF C1 bridge plan (existing n8-c9 route)

Task ID / group: Q-C9-P0-P7-BRIDGE / n8-c9
Owner: lead (integration); workers: 8 bridge tasks
Date: 2026-10-25
Parent node: n8-c9-output-region-source-route
Child nodes: n8-c9-p0 ... n8-c9-p7 (existing DAG nodes)
Stage: 1 (natural-language/source connection) with bounded stage-2 probes.

## Target

Connect the C9 C1 obligation to the actual IUT formalization already present:

  Theorem311Source.SourceTheorem311ReferenceOutput
  Theorem311Source.SourceTheorem311Layers
  ParametricStepXI.StepXIInput / StepXIContract
  FiniteHull / StepXIFiniteCertificate / SourceHullInterfaceDischarge
  ArithmeticQPilotGlobalNormalization / SourceQSideComparison

without toy Output/logVol/h and without hiding C1 in a structure field.

## Existing DAG nodes

- P0 source input and index
- P1 complete source output/representation: alpha, R_alpha, Ind1/2/3
- P2 unified global signed procession-normalized L on Adm regions
- P3 source hull H, admissible positive finite blocks, Theta finite
- P4 HullPoss enlargement and ValuesBounded <= Theta
- P5 equal-global-volume replacement and determinant/degree calibration
- P6 actual q input realization/one-sided approximation Q
- P7 numeric close: Theta finite and Q<=Theta

All are stage1 in_progress, proof not_started. This plan does not change that
status; it assigns the current 8 bridge tasks to these nodes.

## Work packages and node mapping

| package | owner | node(s) | deliverable | exit |
|---|---|---|---|---|
| 469 | transport | P0/P1 | C9IUTBridgeSkeleton.lean | actual imports + C9SourceBridgeData; EXIT0 |
| 470 | multiradial | P1 | C9IUTBridgeOutput.lean | SourceTheorem311ReferenceOutput -> possible outputs; no toy Type |
| 471 | iplsheapt | P6 | C9IUTBridgeQ.lean | actual signed q carrier; qPilot membership explicit |
| 472 | logdescent | P3/P4 | C9IUTBridgeHull.lean | FiniteHull/sourceHullVolume -> h; hull_upper from q_le_theta |
| 473 | volumedet | P4/P7 | C9IUTBridgeContract.lean | StepXIInput/StepXIContract from bridge; Cor312Conclusion |
| 474 | kummer | P0/P1 | C9IUTBridgeObligations.md | theorem311Output/SourceP1P2Bundle pending map |
| 475 | qside | P3/P4 | C9IUTBridgeAmplitude.md | CertificateHullWiring/amplitude bound map |
| 476 | primespine | all | C9IUTBridgeAdversarial.md | reject toy/hidden C1 |

## Statement dependencies

- SourceTheorem311ReferenceOutput (Theorem311/SourceTheorem311ReferenceContract)
- SourceTheorem311Layers (Theorem311/SourceTheorem311Assembly)
- ParametricStepXI.StepXIInput / StepXIContract
- FiniteHull / StepXIFiniteCertificate
- SourceHullInterfaceDischarge.ValueHullCompactnessInput
- ArithmeticQPilotGlobalNormalization / SourceQSideComparison

## Proof dependencies

- Theorem311Source.SourceTheorem311ReferenceOutput.assemble
- Corollary312.StepXI.cor312_of_constructed_stepXI
- StepXIFiniteCertificate.q_le_theta
- sourceHullVolume_lt_top_of_compactnessInput
- pending: theorem311Output, stepXIContractConstruction, iqHullInterfaceDischarge

## Consumer

- n8-s3-c9 / C9 P6 target.
- StepXIContract/Cor312Conclusion is the existing consumer for the inequality.

## Exact C1 bridge

`qPilotOutput_mem` is NOT a Theorem311 field. It must be a separate
`C1SourceBridge : Prop` or a new node `n8-c9-p1-qPilot-output-bridge`.
If a bridge file needs it, it is a named hypothesis, never a structure field
labelled Theorem3.11.

## Acceptance

- statement_compiles: Lean file EXIT0, no sorry.
- proof_body_checked: for any proved bridge theorem; conditional fields named.
- kernel_closed: only if actual declarations + standard axioms, no custom axiom.
- target_accepted: false until source semantics/consumer reviewed.

## Stop boundary

Do not invent arbitrary Output/logVol/h. Do not claim C1. Mark every missing
source card explicitly. If bridge cannot connect, report the exact missing
declaration and leave P nodes open.