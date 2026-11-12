# C9 corrected relaxed output + GlobalLqDonor audit: ACTUAL

## S2556CorrectedPaperC9OutputActual (EXIT=0)
structure S2556CorrectedPaperC9Output (mu) where
  chainA : P6ChainAData X
  relaxed : RelaxedP6Readout X mu
- Q := chainA.Q; Theta := relaxed.value; Values := set of relaxed.value.
- S2556CorrectedPaperC9Output_nonempty (hD : Nonempty (P6ChainAData X)) [ProperSpace] : Nonempty ...
  Uses relaxedP6Readout_actual; frozen P6Readout is not used.
Axioms trio.

## S2557GlobalLqDonorAuditActual (EXIT=0)
- S2557ConstantGlobalLqDonor: readout := fun _ => qPilotSignedLog X; satisfies readout_eq_local by rfl.
- S2557GlobalLqDonor_nonempty : Nonempty (GlobalLqDonor X).
- S2557P6ChainAData_nonempty_iff : Nonempty (P6ChainAData X) <-> Nonempty (GlobalLqDonor X).
- S2557P6ChainAData_nonempty : Nonempty (P6ChainAData X).
IMPORTANT: this donor is underconstrained (only one value equation), not the paper global Lq readout.
It proves formal existence, not source-faithful C9 data.
Axioms trio.

## Remaining source objects
- GlobalLqDonor / P6ChainAData: formal existence is underconstrained; source-faithful construction still missing.
- SourceAllowedOutput: old-chain bridge + C2/C3/C4/C6/T11 witness; P6Comparison.sourceAllowedOutput_nonempty named sorry.
- P6SourceClosure: chainA, chainB, hull, readout, sheInd, tensor, alphaIndex, comparison, sourceExists; many named obligations.
No fake.