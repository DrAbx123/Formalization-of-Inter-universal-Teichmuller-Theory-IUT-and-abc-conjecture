# S376: StageCharacteristicTauData from an existing CharacteristicSplitting

Date: 2026-10-29. No fake tau/split; no completion/L; no inequality.

## Result

Repo has the actual stageModelFrobenioidPresentation and its
rationalMonoidTransport, but no CharacteristicSplitting instance for the stage
transport.  Therefore tau X cannot be constructed from the stage model data
alone; the only actual construction is from a supplied CharacteristicSplitting.

* stageTauDataOfSplitting C: given
  C : CharacteristicSplitting (nativeStageRationalMonoidTransport),
  define tau X := C.tau X and fill pullback_mem/units_commute/
  multiplication_bijective/isotropicHull_mem_range directly from C.
* NativeStageCharacteristicSplittingMissing T b :=
  Nonempty (CharacteristicSplitting stageTransport).
* nativeStageCharacteristicSplittingMissing_iff:
  this is equivalent to NativeStageCharacteristicSplittingExact (S373).

No CharacteristicSplitting or StageCharacteristicTauData inhabitant is
asserted.  The exact missing datum remains the stage characteristic splitting.

No fake split/tau, no completion root/L.
