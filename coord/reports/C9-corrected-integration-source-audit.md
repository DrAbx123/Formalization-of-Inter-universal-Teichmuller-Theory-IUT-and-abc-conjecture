# Corrected C9 integration + source donor audit

## S2559CorrectedC9IntegrationActual (EXIT=0)
structure S2559CorrectedC9 (mu) where
  chainA : P6ChainAData X
  source : S2558RelaxedSourceGlobalLqDonor X mu
- toOutput : S2559CorrectedC9 -> S2556CorrectedPaperC9Output.
- Q := chainA.Q; Theta := source.readout.value; Values := readout values.
- Q_eq_native : Q = qPilotSignedLog.
- S2559CorrectedC9_nonempty (hD : Nonempty (P6ChainAData X)) (R : RelaxedP6Readout) (hval : R.value = qPilotSignedLog) : Nonempty.
Axioms trio; no frozen P6Readout.

## S2556/S2557/S2558 actuals
- S2556: CorrectedPaperC9Output; nonempty given P6ChainAData + ProperSpace.
- S2557: constant formal GlobalLqDonor; Nonempty P6ChainAData <-> Nonempty GlobalLqDonor; NOT source-faithful.
- S2558: source-faithful SourceGlobalLqDonor impossible at archimedean; RelaxedSourceGlobalLqDonor + value_eq; SourceAllowedOutput from C6 P6BridgeDonors.

## SourceAllowedOutput component status
bridge: P6BridgeDonors; p6BridgeDonorsExist named sorry; NativeC1PaperSource conditional packet needs R/F.
C2: C2Actual.sourceLogKummerDataActual actual zero sorry.
C3: C3Actual.sourcePilotRegionDataOfDonors conditional; missing SourcePilotRegionDonors.
C4: C4ObligationActualAttempt.c4DataOfInd conditional; missing IndActionData.
T11: T11Actual.thetaIQInterfaceActual actual from C3.
C6: C6ActualIQData.actual actual given measure/addHaar.
measure/Borel/Haar: SourceAllowedOutput requires explicit tensor measurable/Borel and Haar measure; no canonical donor in C3.
witness: Witness is Sigma over SignedLabel; constructible once n/x chosen, no extra source field beyond C4 data.

## P6SourceClosure
Fields: chainA, chainB, hull, readout(frozen), sheInd, tensor, alphaIndex, comparison, sourceExists.
Readout correction replaces one field only; other named obligations remain.

## Finite-place alternative
P6NonarchAdmActual.finitePlaceAdm restricts Adm to finite places; unitSphereAt_ae_localLog_zero actual;
exact missing donor: finite unit-sphere positive finite Haar mass.
RelaxedP6Readout avoids archimedean no-go and preserves ellOut value under ProperSpace.
No fake.