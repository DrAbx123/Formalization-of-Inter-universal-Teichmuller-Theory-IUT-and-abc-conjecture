# C9 donor status: bridge / C3 / C4 / measure

## Corrected integration actual
S2559CorrectedC9IntegrationActual.lean EXIT=0: S2559CorrectedC9 {chainA, source:RelaxedSourceGlobalLqDonor}; toOutput; Q/Theta/Values; nonempty given hD + explicit relaxed R + value_eq.
No frozen P6Readout, no constant donor as closure.

## P6BridgeDonors
P6Bridge.P6BridgeDonors X = {inputDonors : NativeOriginalInputDonors X, bindingDonors : NativePlaceBindingDonors ...}.
P6Bridge.p6BridgeDonorsExist is named sorry.
NativeC1PaperSource conditional packet fields: X, S : NativeSourceAssembly X.S, e : index equiv, R : NativeImageRealizationSourceFields, F : NativeFiberSourceFields.
NativeSourceAssembly fields: badFinite, split, torsionGaps, exactSequence, curve/puncturedCurve/cover/structureGroup, cover_surjective, cuspCount/pos, d7, cuspHyp, red/tor/orb/sec/cus compatibility props. No unconditional constructor.

## C3 SourcePilotRegionDonors
C3Actual.SourcePilotRegionDonors fields: p/prime, place, q, thetaPacket, roots, roots', kummerClass, rootChange/rootChange_eq, tensorIndex/Fintype, tensorPlaceIndex/places/tuple, tensorUnit, tensorLanding/landing_q.
sourcePilotRegionDataOfDonors conditional actual; no unconditional C3. C3CompleteSourceReduction has named c3SourceObligation, nativeTensorLandingObligation, nativeKummerActionObligation.

### C3 descent actual (S2562)
`tmp/sheaf/xif/paper/S2562C3CompletionDirectionActual.lean` EXIT=0; olean 39152 B; src SHA CB46E8DE17722BB35996206145CAF32B8F9943D8C949696BE5CFB18EBFCF437B; olean SHA 91F012848F3AC54C437C8D1960D1AD7898C6579229409AAFD6630C61E6C4D6F4; axioms trio.
- Base -> F map: `S2562BaseToFCompletionMap := completionMap (k:=Fmod) (nativeFPlaceOverBad X)`, actual injective; this is the existing actual completion embedding.
- F -> base map: `S2562FToBaseNormMap := relativeNormCompletion (X:=X)`, actual algebra norm F-completion -> base completion (not a ring section).
- `S2562BaseQValue := relative norm of nativeQActual.q`.
- `S2562BaseQCandidateOfLaws (hq : value != 0) (hcontr : valuation value < 1) : FinitePlaceQCandidate nativeBadBasePlace`.
Thus a descent map exists (relative norm); the nonzero law is now ACTUAL via S2566 cast transport, and only contraction remains. No unrestricted multiplicative section is available or needed for the norm route.

### TauCeti instance skeleton (S2564)
`tmp/sheaf/xif/paper/S2564TauCetiInstanceSkeletonActual.lean` EXIT=0; olean 49928 B; src SHA EA5448CA2595062F1369C50ACAEBC0E06F2C8AAD25B4B7DA25401F8C94A09A9A; olean SHA E80AFA5694965ECC8ED024E075CBBF174B918CC2F1381DC08FFB5B89E1AE56B9; axioms trio.
- Actual `ValuativeRel` instances on NativeFCompletion and NativeBaseCompletionRaw via `ValuativeRel.ofValuation (Valued.v)`.
- Skeleton fields remaining: `fNonarch : IsNonarchimedeanLocalField NativeFCompletion`, `baseNonarch : IsNonarchimedeanLocalField NativeBaseCompletionRaw`, `extension : Nonempty (ValuativeExtension base F)`.
- I-A actual: `S2564FCompletionIsNontrivial` and `S2564BaseCompletionIsNontrivial` via `Valued.v` RankOne/Compatible; both IsNontrivial actual. Updated S2564 SHA C1A2C8AC..., olean 68152 B SHA EA5ECDB7...
- Remaining first errors: no `IsValuativeTopology`, no `LocallyCompactSpace` for either completion; no `ValuativeExtension` instance.

## C4 SourceWitnessedOutputData
Fields: place : C1PlaceData, pilot : C3ThetaPilotData, ind : IndActionData Y PaperLabel.
IndActionData fields: ind1/ind2 maps to Equiv.Perm, ind3_nonarch/inclusion, ind3_arch/surjection.
c4DataOfInd is conditional actual; C4IndObligation is exact named gap. Trivial identity Ind action is not source-faithful, must not be used.

## measure / Borel / Haar
SourceAllowedOutput requires [MeasurableSpace tensor], [BorelSpace tensor], mu : Measure tensor, [IsAddHaarMeasure mu].
C6ActualIQData.actual is actual given these. No p-adic tensor Haar measure constructor is present in tree. Exact missing donor: a Measure on ArithmeticTensorTupleBlock with IsAddHaarMeasure plus Borel instances (or an actual finite-tensor Haar construction).

## Already actual subitems
C2: C2Actual.sourceLogKummerDataActual, zero sorry.
T11: T11Actual.thetaIQInterfaceActual from C3.
C6: C6ActualIQData.actual given measure/addHaar.
Witness: Witness is Sigma over SignedLabel; constructible once n/x chosen; no extra source axiom.

## P6SourceClosure
Fields: chainA, chainB, hull, readout(frozen), sheInd, tensor, alphaIndex, comparison, sourceExists.
Readout replacement affects one field only; remaining named obligations stay.
No fake.