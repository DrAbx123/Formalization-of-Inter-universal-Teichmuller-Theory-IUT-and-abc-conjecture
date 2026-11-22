# S373: exact CharacteristicSplitting statement for native stage model

Date: 2026-10-29. No fake split; no completion/L; no inequality.

## Result

The actual stage presentation and rational transport are S369's:
stagePresentation = nativeStageFrobenioidPresentation T b;
stageTransport = nativeStageRationalMonoidTransport T b.

Repo search found no CharacteristicSplitting instance for this transport.
S373 gives the weakest explicit tau statement:

StageCharacteristicTauData:
* tau X <= O^triangle(X.obj) for every isotropic linear object X;
* pullback_mem;
* units_commute;
* multiplication_bijective
  Units(O^triangle(X.obj)) x tau X -> O^triangle(X.obj);
* isotropicHull_mem_range.

NativeStageCharacteristicSplittingExact := Nonempty tau data.

characteristicSplittingOfTauData constructs the repo CharacteristicSplitting
from explicit tau data.  nativeStageCharacteristicSplittingExact_iff proves
the tau statement is equivalent to Nonempty CharacteristicSplitting; hence it
is the weakest exact form.

nativeStageCharacteristicSplittingGap_iff identifies S369's
NativeStageCharacteristicSplittingGap with this tau statement.

No tau data or split is constructed; the gap remains exact missing.

No completion root/L/fake split.
