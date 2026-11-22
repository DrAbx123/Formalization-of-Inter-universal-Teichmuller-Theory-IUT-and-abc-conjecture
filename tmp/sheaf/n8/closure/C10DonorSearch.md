# R49 C10 donor search

Status: C10DonorSearch.lean compiles exit 0 with exactly one reduced named
obligation.  No NativeOldC1Bridge inhabitant is constructed; the full bridge is
reduced to the native contract supply, and the remaining index/R/fiber gaps are
listed below.

## Search results

### 1. SourceDefinition31Data production constructors

- SourceDefinition31RootLemmas.lean:3807
  StageConstructionTrace.toSource : StageConstructionTrace -> SourceDefinition31Data.
  It needs a complete StageConstructionTrace input.  No concrete
  StageConstructionTrace is constructed from SourceNativeInitialThetaData.
- SourceUnitRegionHaarDataActual.lean:348
  sourceHaarActualOriginalInput (S : SourceDefinition31Data) : OriginalInput ...
  This consumes S; it does not construct S.
- SourceDefinition31NativeContractBridgeReduction.lean:183
  NativeContractRecordBridge : Prop, an existential gate
  (exists Phi : native -> contract, arithmetic preserving).  It is not a
  function and supplies no record.
- SourceDefinition31NativeContractBridgeReduction.lean:188
  SourceContractRootSupply : Prop; conditional relation to the bridge.
- SourceDefinition31NativeContractBridgeReduction.lean:151
  NativeContractPartitionFragment.ofNative : only a partition fragment
  (selected/bad carriers and bad inclusion), not SourceDefinition31Data.
- SourceDefinition31NativeContractBridgeReduction.lean:263
  ContractRootSignQuotientSupply : Prop; another gate, not a constructor.

Exact gap: no production declaration
  SourceNativeInitialThetaData -> SourceDefinition31Data.

### 2. OriginalInput index_equiv

- SourceOriginalInput.lean:41 OriginalInput fields:
  initial, family, index_equiv : family.index ≃ Int × Int,
  arithmetic_alignment.
- The only production OriginalInput constructor found is
  sourceHaarActualOriginalInput S with V = Unit and index_equiv := refl.
- NativeLattice carries family and arithmetic_alignment only; no index_equiv
  for X.family.index.

Exact gap: no native index equivalence X.family.index ≃ Int × Int.

### 3. Old C1 placeEquiv/R/fiber

- Production has no SourcePlaceRealization or SourceInputBinding declarations
  at all (they are tmp C1 interface types).
- Found donor: NativeC1.nativePlaceIndexEquiv gives
  NativePlaces X.S ≃ NumberFieldPlaceIndex.
- Found donor: NativeC1.badPlace gives the selected native place.
- sourceHaarActualImageRealization constructs an R only for V = Unit and
  q = 1; it is not a native-place R.
- No fiberMonEquiv declaration exists in production.

Exact gap: SourceImageRealization for the native selected place and the
prime-strip fiberMonEquiv are missing.  They are not filled with arbitrary R.

## Reduced named obligation

C10DonorSearch.lean:

    def NativeContractSupply (X : N8NativeInput l) : Prop :=
      exists initial : SourceDefinition31Data.{0} l,
        initial.arithmetic = X.S.arithmetic

    theorem nativeContractSupply (X : N8NativeInput l) :
        NativeContractSupply X := by
      sorry

This is the only named sorry in this file.  It replaces the full
NativeOldC1Bridge sorry by the smallest missing production donor: the native
contract record over the native arithmetic root.  It does not assert
index_equiv, R or fiberMonEquiv.

Found actual donors kept in the file:

    nativePlaceEquivDonor (X) :
      NativePlaces X.S ≃ NumberFieldPlaceIndex

    nativeSelectedPlaceDonor (X) : NativePlaces X.S := badPlace X

Conditional bridge construction remains in C10BridgeProof:

    nativeOriginalInputOfDonors  (needs contract supply + index_equiv)
    sourceInputBindingOfPlaceDonors (needs placeEquiv/selected/R/fiber)
    nativeOldC1Bridge_of_donors

No arbitrary V and no arbitrary selected R are introduced.

## Exact no-go

Without nativeContractSupply, no SourceDefinition31Data over X.S exists by any
production declaration.  Without index_equiv no OriginalInput l (NativePlaces
X.S) exists.  Without native R/fiberMonEquiv no SourceInputBinding over that
OriginalInput exists.  Therefore NativeOldC1Bridge is not constructible from
the native root with current production donors.

## Evidence

- C10DonorSearch.lean: exit 0; one named sorry (nativeContractSupply).
- C10DonorSearch.lean SHA256: see build report.
- No old N8Closure.lean edit.

## Concurrent note

C10BridgeProof.lean had been concurrently appended with
nativeOriginalInputDonors_nonempty and nativePlaceBindingDonors_nonempty named
sorries plus nativeOldC1BridgeExists_proof.  Those statements claimed donor
nonemptiness for arbitrary X/I and conflicted with the no-arbitrary-R rule.
They were removed during this round; C10BridgeProof now has no named sorry and
contains only the conditional donor construction plus the exact no-go.  R49
does not use arbitrary donors.
