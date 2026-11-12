# C9 source-faithful GlobalLqDonor blocking report

## New actual (S2558, EXIT=0)
- S2558SourceGlobalLqDonor_isImpossible_of_archimedean: under archimedean place assumptions,
  not Nonempty (SourceGlobalLqDonor X mu). Because SourceGlobalLqDonor contains an actual P6Readout,
  and frozen P6Readout is refuted at archimedean.
- S2558RelaxedSourceGlobalLqDonor: relaxed replacement {readout : RelaxedP6Readout, value_eq : value = qPilotSignedLog}.
- S2558RelaxedSourceGlobalLqDonor_nonempty: nonempty given an explicit relaxed readout R and R.value = qPilotSignedLog.
- S2558SourceAllowedOutput_nonempty_of_c6donors: C6ConstructedOutput.P6BridgeDonors X -> Nonempty (SourceAllowedOutput X).
Axioms trio.

## GlobalLqDonor exact gap
Formal P6ChainA.GlobalLqDonor: readout : P6ChainALocal X -> Real; readout (p6ChainALocal X) = qPilotSignedLog X.
Only one-point constraint: underconstrained; constant donor is formal only.
Source-faithful candidate P6GlobalLqTargetCorrection.SourceGlobalLqDonor: readout : P6Readout + value_eq.
Impossible at archimedean: P6Readout frozen Adm requires a.e. localLog=0 at every place, refuted by addHaar_sphere.
Corrected source target: RelaxedP6Readout + value_eq to qPilotSignedLog. Relaxed readout actual under ProperSpace;
value_eq is the remaining numeric/source identification, not automatic.

## SourceAllowedOutput exact gap
C6ConstructedOutput.P6BridgeDonors fields:
  bridge : NativeOldC1Bridge X; C2; C3; D (C4); T (T11); measurable/Borel; mu/addHaar; n,x,w.
sourceAllowedOutputOfDonors gives SourceAllowedOutput from these donors (new actual wrapper).
NativeC1PaperSource packet gives NativeOldC1Bridge and SourceInputBinding, but not C2/C3/C4/T11/witness.
P6Comparison.sourceAllowedOutput_nonempty remains named sorry; paperC9Comparison still needs SourceAllowedOutput.

## P6SourceClosure exact gap
Fields: chainA (P6ChainAData), chainB, hull, readout (frozen P6Readout), sheInd, tensor, alphaIndex,
comparison (P6Exact/P6Epsilon), sourceExists. p6SourceClosure_nonempty is named sorry.
Readout correction replaces only one field; chainA/chainB/hull/sheInd/tensor/comparison/sourceExists remain.

No frozen P6Readout is asserted; constant donor is not source-faithful.