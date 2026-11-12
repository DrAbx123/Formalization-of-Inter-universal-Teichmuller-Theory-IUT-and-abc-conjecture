# C1 singleton native selection semantics audit

Date: 2026-10-28

## Question

Does `nativeD11PlaceSelection` / `badNativeD11Fintype` satisfy the intended native C1 contract semantics?

## Definitions inspected

- `NativeContractDatumExists X := ∃ initial : SourceDefinition31Data.{0} l, initial.arithmetic = X.S.arithmetic` (C1BridgeProof.lean).
- `C6ContractSupply X` is the same existential condition over the native arithmetic root.
- `C1ActualDataComponents.contractSupply : C6ContractSupply X`.
- `NativeOldC1Bridge X` contains only an arbitrary `OriginalInput l (NativePlaces X.S)` and a `SourceInputBinding`; its `OriginalInput.initial` is not required to be the native tuple source.
- The native tuple source `X.S.tuple.source` is a `SourceSignQuotientData X.S.arithmetic`, not a `SourcePlaceSelection`.
- `SourceDefinition31Data.selectedPlaces/badPlaces` are bare Type fields, not tied to `X.S.tuple.source.V/V_mod_bad`.

## Finding

`nativeD11PlaceSelection = SourcePlaceSelection.singleton (nativeBadBasePlace X) ...` is an actual `SourcePlaceSelection` with the native bad base place as its singleton bad set and a constructed Fintype.

It satisfies the *weak* interface `NativeContractDatumExists X` and `C6ContractSupply X`, because those only require the contract arithmetic root to equal `X.S.arithmetic`.

It does NOT establish the paper-level native contract: the selected bad set is a singleton, not the full native `V_mod_bad`, and the contract is not tied to the native tuple source. The missing native full partition/Fintype is exactly the earlier `NativePartitionFintypeGap`; the singleton construction bypasses it by choosing a smaller source selection.

## Consequence

- Keep the singleton construction only as a weak-interface API / consistency check, not as the paper-level C1 contract closure.
- For paper-level C1, the contract must be reconstructed with the full native source selection (or the target must explicitly state the weaker arithmetic-root interface).
- The genuine C1 binding equivalence and the P6 donor route remain valid conditional results; they do not depend on the singleton selection.

## Verdict

The singleton route is semantically insufficient for the paper-level target. It is admissible only under the current weak `NativeContractDatumExists` interface.