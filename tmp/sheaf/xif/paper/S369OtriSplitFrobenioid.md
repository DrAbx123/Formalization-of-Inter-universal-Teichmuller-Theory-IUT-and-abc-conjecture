# S369: native stage Frobenioid, rational transport, O_tri split gap

Date: 2026-10-29. No completion root, no L, no fake carrier.

## 1. Actual native stage Frobenioid

nativeStageFrobenioidPresentation T b is
Iut.SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation at the
native bad place (nativeBadLift T).lift b.  This is the actual stage-model
FrobenioidPresentation from the repo, not a fabricated object.

nativeStageRationalMonoidTransport is the actual
Iut.FrobenioidRationalMonoidTransport.rationalMonoidTransport applied to it:
the object monoids are O^triangle(A) = LinearBaseIdentityEndomorphism A, with
the Probenioids I Proposition 2.2 transport.

Exact missing for a SplitFrobenioidPresentation:
NativeStageCharacteristicSplittingGap, i.e. a
CharacteristicSplitting of this rational monoid transport.  The repo defines
CharacteristicSplitting/SplitFrobenioidPresentation but has no instance for the
stage model.  NativeStageSplitFrobenioidPresentation is constructed
conditionally from such a splitting; no splitting is fabricated.

## 2. O_tri submonoid

NativeStageOtriangleMonoid A = actual O^triangle(A);
NativeStageOtimesUnits A = Units(O^triangle(A)) = O^times(A).

NativeStageOtriSubmonoidSpec A records the exact missing O_tri:
* Otri : Submonoid (O^times(A));
* positivityLogShellCondition : Prop (paper condition not in repo);
* qSection, rootSection : Otri;
* root_pow : rootSection^(2l)=qSection;
* qSection_reflects_qVFamily : Prop.

NativeStageOtriSubmonoidRequired A := Nonempty spec; no inhabitant.
No trivial top/bottom submonoid is passed off as O_tri.

## 3. q_v^(1/2l) section

NativeStageQVFamilyOtriSectionRequired A is the same exact missing spec.  No
completion root and no L root are used; S342 already rules out the completion
root.  The O_tri section remains the exact missing datum.

No inequality, no fake carrier/root.
