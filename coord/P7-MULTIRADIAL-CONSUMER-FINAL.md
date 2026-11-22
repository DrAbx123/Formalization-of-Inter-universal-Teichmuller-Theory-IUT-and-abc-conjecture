# #4 MULTIRADIAL / A5 final consumer (2026-11-14)

Status: **ACTUAL INDEX + FIXED-PLACE IND1 + IND3 TENSOR INCLUSION GREEN; GENERAL-PLACE IND1 IS AN EXACT GAP.**

This note is the single consumption entry for the A5/#4 chain. It does not claim the paper xi-e/xi-f production `n, oR_LGP` is constructed; it records the actual capsule/log-shell carriers and the precise remaining Ind1 condition.

## Green Lean chain

1. `tmp/sheaf/xif/paper/Mzk1A5CapsulePositionActual.lean` (GREEN 21:44:15Z)
   - `CapsulePosition Va := Sigma Va` — dependent-sum procession index at one p and one level j.
   - `capsuleLabelSucc : Capsule j → Capsule (j+1)` and `capsuleLabelSucc_injective` — adjacent m columns.
   - `actualCapsuleLogShellFamily places := arithmeticLogShellFamilyDependent places`.
   - `actualCapsuleTensorPacket_eq_arithmetic places : arithmeticDependentTensorPacket places = ArithmeticPacketTensor places`.
   - `capsulePositionEquiv e φ : CapsulePosition Va ≃ CapsulePosition Va`, `capsulePositionEquiv_fst` — Ind1 index action.
   - `capsuleTensorLogLink_subset places : arithmeticDependentTensorLogRegion places ⊆ arithmeticTensorLogRegion places` — Ind3 tensor inclusion.
   - `Ind1ShellTransport places`, `Ind1ShellTransportGap places := Nonempty (Ind1ShellTransport places)`.
   - `ind1ShellTransport_of_place_fixed places φ h` for `h : ∀ i v, places i (φ i v) = places i v`.
   - `ind1ShellTransportGap_holds_of_place_fixed places φ h : Ind1ShellTransportGap places`.

2. `tmp/sheaf/xif/paper/Mzk1A5Ind1Ind3ConsumerActual.lean` (GREEN 21:53:05Z)
   - `SourceMultiradialInd1Ind3Interface places`:
     `ind1Transport : Ind1ShellTransport places`;
     `ind3LogLink : arithmeticDependentTensorLogRegion places ⊆ arithmeticTensorLogRegion places`.
   - `SourceMultiradialInd1Ind3InterfaceRequired places := Nonempty (SourceMultiradialInd1Ind3Interface places)`.
   - `sourceMultiradialInd1Ind3Interface_of_place_fixed places φ h`.

3. `tmp/sheaf/xif/paper/Mzk1A5MultiradialConsumerActual.lean` (GREEN 22:24:24Z)
   - `MultiradialA5ConsumerData places := SourceMultiradialInd1Ind3Interface places`.
   - `multiradialA5ConsumerData_of_place_fixed places φ h`.
   - `multiradialA5ConsumerData_required places` (iff form).

## How #4 / 3.12 consumes it

```lean
-- fixed one actual rational prime p, one level j, one actual place family
variable (places : (i : Capsule j) → Va i → FinitePlaceAtPrime K p)

-- Ind3 (unconditional actual inclusion):
#check capsuleTensorLogLink_subset places

-- Ind1, fixed-place actual case:
#check ind1ShellTransport_of_place_fixed places φ h
#check sourceMultiradialInd1Ind3Interface_of_place_fixed places φ h
#check multiradialA5ConsumerData_of_place_fixed places φ h

-- general case: consume the exact gap, do not fake it
#check Ind1ShellTransportGap places
```

The consumer object is `SourceMultiradialInd1Ind3Interface places`; the #4 alias is `MultiradialA5ConsumerData places`. Its only non-unconditional field is the Ind1 transport. Ind3 is actual and unconditional.

## Exact remaining gap (do not fill with toy data)

For an arbitrary place permutation `φ : ∀ i, Va i ≃ Va i` (or the label/place permutation in `Ind1ShellTransport`), there is no actual source theorem/field giving
```text
shellEquiv : ∀ i v,
  CommonPrimeCompletion (places i v)
    ≃ₗ[ℚ_[p]]
  CommonPrimeCompletion (places (labelPerm i) (placeEquiv i v))
```
Different places have different completions; this is not definitional equality. The fixed-place hypothesis `h : ∀ i v, places i (φ i v) = places i v` is the currently handled case. Do **not** fill the general case with `LinearEquiv.refl` or a one-point carrier.

## What is NOT claimed

- No construction of the paper output `n, oR_LGP`.
- No arbitrary-place Ind1 tensor equivalence.
- No old C3 inhabitant, no `IsEmpty`, no new axiom/sorry.
- Ind3 is only the tensor log-region inclusion at one p/j; the paper's full Ind3 log-link inclusion for all p/j and infinite places remains outside this file.

## Next concrete action

Either:
1. prove an actual completion equivalence from real place equality / an explicit field isomorphism, and fill `Ind1ShellTransport`; or
2. keep `Ind1ShellTransportGap` as the precise interface and connect the A6/A1 comparison consumer conditionally on it.

Doc owner: stepxi. Date: 2026-11-14.

## Definition-level check of the general Ind1 gap (2026-11-14 T06:30Z)

Checked the definitions: `Ind1ShellTransport`/`capsulePositionEquiv` take an arbitrary `e : Capsule j ≃ Capsule j` and `φ : ∀ i, Va i ≃ Va (e i)`; the place family `places` is an arbitrary source argument. There is no definitional or `simp` equality `places (e i) (φ i v) = places i v` for general `e, φ`. Therefore no canonical completion equivalence follows from the definitions; only the identity permutation has a definitional inhabitant.

Added the exact specified-permutation interface:
- `Ind1ShellTransportFor places e φ` with `shellEquiv`;
- `Ind1ShellTransportForRequired places e φ := Nonempty (Ind1ShellTransportFor places e φ)`;
- `ind1ShellTransportFor_refl` (identity only).

The bare `Ind1ShellTransportGap` is trivially inhabited by identity and is not sufficient for a nontrivial procession automorphism; consumers should use `Ind1ShellTransportForRequired` with the actual `e, φ`. This is the one explicit source input still needed for general-place Ind1.

## Consumer rule (must read)

For a real procession automorphism, consumers MUST pass the actual label/place permutation `e, φ` and use `SourceMultiradialInd1Ind3InterfaceFor places e φ` / `SourceMultiradialInd1Ind3InterfaceForRequired places e φ` (or the A5 `Ind1ShellTransportForRequired`). The bare `Ind1ShellTransportGap` is only the identity-level existence statement and must NOT be used as a substitute for nontrivial Ind1.

Construction from an actual transport:`sourceMultiradialInd1Ind3InterfaceFor_of_transport places e φ h`.

