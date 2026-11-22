# C9 → existing IUT formalization: connection map

Date: 2026-10-25. Status: C1 OPEN. This is an integration map, not a proof.
Probe: C9IUTBridgeProbe.lean, EXIT 0.

## 0. Principle

The abstract `ThreeAssumptions` must be replaced by the project's actual
source-facing contracts. Do not add a new toy `Output`/`logVol`/`h`.

## 1. Theorem 3.11 connection

File: LeanFormal/IUT/IUTIII/Theorem311/SourceTheorem311ReferenceContract.lean

- `SourceTheorem311ReferenceOutput (B : SourceP1P2Bundle W S)`
  fields: `output : Theorem311Output R.input`, `partI/II/III`, H1/H2,
  Ind1/2/3, horizontal/evaluation directions.
- `SourceTheorem311Layers` and `assemble (B : SourceP1P2Bundle W S)`
  in SourceTheorem311Assembly.lean.
- `partI/partII/partIII` in SourceFaithfulBoundary.lean.
- Input boundary: `SourceOriginalInput`, `OriginalInput`, `SourceP1P2Bundle`.

Connection: replace `Theorem311Full.Output` by `Theorem311Output R.input` and
`possibleOutputs` by the output/parts of a `SourceTheorem311ReferenceOutput`.

## 2. Corollary 3.12 connection

File: LeanFormal/IUT/IUTIII/Corollary312/StepXI/Contract.lean

- `StepXIContract` fields: qSigned, targetSigned, thetaSigned, q_negative,
  ipl/she/apt + evidence, q_le_target, target_le_theta.
- `Cor312Conclusion contract` and
  `cor312_of_constructed_stepXI : StepXIContract -> Cor312Conclusion`.

File: .../StepXI/ParametricStepXI.lean

- `ParametricStepXI.StepXIInput carrier input` with output, qSigned,
  targetSigned, thetaSigned, q_le_target, target_le_theta, ipl/she/apt.
- `StepXIInput.toContract`; `SourceStepXIAssembly`.

Connection: target `StepXIContract`/`StepXIFiniteCertificate`, not a new
abstract inequality.

## 3. q log-volume connection

- .../Corollary312/ArithmeticQPilotLogVolume.lean
- .../ArithmeticQPilotGlobalNormalization.lean
- .../StepXI/HolomorphicHull/SourceQSideComparison.lean

`sourceQSideNormalizedValue` is the real signed q-side value. The ENNReal
consumer slot degenerates (`iqHullCertificate_hqSlot_of_neg`), so a paper-
faithful real q carrier is still needed. Do not use an arbitrary Real qLog.

## 4. hull/log-volume connection

- .../StepXI/HolomorphicHull/Volume.lean: `FiniteHull`,
  `StepXIFiniteCertificate`, `q_le_theta`.
- .../SourceHullInterfaceDischarge.lean: `ValueHullCompactnessInput`,
  `sourceHullVolume_lt_top_of_compactnessInput`, `iqHullInterfaceDischarge`.
- .../CertificateHullWiring.lean, SourceHullNormalizationConditionalClosure.lean.

Connection: h must be `FiniteHull.hullVolume` or the source hull volume;
hull_upper must come from `q_le_theta`/amplitude card, not an arbitrary field.

## 5. Obligations / gaps

- `Audit.theorem311ReferenceOutputContract`: status interface.
- `Audit.theorem311Output`: pending (Theorem311/Obligations.lean).
- `Audit.stepXIContractConstruction`: pending.
- `Audit.iqHullInterfaceDischarge`: interface, not closed.
- `hullDeterminantLogVolume`: obligation in Volume.lean.

These are the real pending cards. The C1 membership `qPilotOutput_mem` is NOT
among them; it is the missing xi-e/f bridge and must be a new explicit
obligation if it is claimed.

## 6. Concrete next bridge

Create `C9IUTBridge.lean` importing the above and define a structure whose
fields are actual declarations:

- `out : SourceTheorem311ReferenceOutput B`
- `q : StepXIFiniteCertificate` or `StepXIInput` scalar
- `hull : FiniteHull label`
- actual q_le_hull / hull_le_theta fields

Then feed `cor312_of_constructed_stepXI` or `StepXIFiniteCertificate.q_le_theta`.
Leave `qPilotOutput_mem` as the named C1/xi-e bridge, not a hidden field.

## 7. Status

C1 OPEN. Connection points identified and probe-compiled. No claim that the
pending obligations are discharged.