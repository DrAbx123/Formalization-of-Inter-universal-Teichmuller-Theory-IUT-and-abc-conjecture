# A5 Ind1/Ind3 consumer interface (#4 MULTIRADIAL → 3.12)

Status: A5 actual capsule/log-shell index + fixed-place Ind1 transport + Ind3 tensor inclusion implemented; general place permutation remains an exact gap.

## Lean entry points

File `tmp/sheaf/xif/paper/Mzk1A5CapsulePositionActual.lean`:
- `CapsulePosition Va := Sigma Va` — one p, one level j dependent-sum procession index.
- `capsuleLabelSucc : Capsule j → Capsule (j+1)` and `capsuleLabelSucc_injective` — adjacent m columns.
- `actualCapsuleLogShellFamily places := arithmeticLogShellFamilyDependent places`.
- `actualCapsuleTensorPacket_eq_arithmetic places : arithmeticDependentTensorPacket places = ArithmeticPacketTensor places`.
- `capsulePositionEquiv e φ : CapsulePosition Va ≃ CapsulePosition Va` for `e : Capsule j ≃ Capsule j`, `φ : ∀ i, Va i ≃ Va (e i)`; label component is `e` (`capsulePositionEquiv_fst`).
- `capsuleFactorLogLink_subset places i : arithmeticLogShellFactorRegion places i ⊆ completionPacketLogRegion (places i)` — Ind3 at one factor.
- `capsuleTensorLogLink_subset places : arithmeticDependentTensorLogRegion places ⊆ arithmeticTensorLogRegion places` — Ind3 at the tensor packet.
- `Ind1ShellTransport places`: fields `labelPerm`, `placeEquiv`, and the missing actual transport
  `shellEquiv : ∀ i v, CommonPrimeCompletion (places i v) ≃ₗ[ℚ_[p]] CommonPrimeCompletion (places (labelPerm i) (placeEquiv i v))`.
- `Ind1ShellTransportGap places := Nonempty (Ind1ShellTransport places)`.
- `ind1ShellTransport_of_place_fixed places φ h` when `h : ∀ i v, places i (φ i v) = places i v`.
- `ind1ShellTransportGap_holds_of_place_fixed places φ h : Ind1ShellTransportGap places`.

File `tmp/sheaf/xif/paper/Mzk1A5Ind1Ind3ConsumerActual.lean`:
```lean
structure SourceMultiradialInd1Ind3Interface (places) where
  ind1Transport : Ind1ShellTransport places
  ind3LogLink :
    arithmeticDependentTensorLogRegion (p := p) places ⊆
      arithmeticTensorLogRegion (p := p) places

def SourceMultiradialInd1Ind3InterfaceRequired places : Prop :=
  Nonempty (SourceMultiradialInd1Ind3Interface places)

def sourceMultiradialInd1Ind3Interface_of_place_fixed
    (places) (φ : ∀ i, Va i ≃ Va i)
    (h : ∀ i v, places i (φ i v) = places i v) :
    SourceMultiradialInd1Ind3Interface places
```

## How #4 / 3.12 consumes it
1. Fix one actual rational prime `p`, one capsule level `j`, and the actual place family `places : (i : Capsule j) → Va i → FinitePlaceAtPrime K p`.
2. The tensor packet is `arithmeticDependentTensorPacket places`; Ind3 gives it inside `arithmeticTensorLogRegion places` via `capsuleTensorLogLink_subset places`.
3. For an Ind1 automorphism whose place permutation fixes the actual place values (or whose `placeEquiv` is accompanied by an actual completion equivalence), use `ind1ShellTransport_of_place_fixed`; otherwise pass `Ind1ShellTransportGap places` as the exact remaining input.
4. The combined structure `SourceMultiradialInd1Ind3Interface places` is the single consumer object: Ind1 transport + Ind3 inclusion. It is inhabited in the fixed-place case; general case requires the missing `shellEquiv`.

## Exact remaining gap
No actual source field/theorem provides
`CommonPrimeCompletion (places i v) ≃ₗ[ℚ_[p]] CommonPrimeCompletion (places i (φ i v))`
for an arbitrary place permutation `φ`. This is not a definitional identity: different places give different completions. Therefore do NOT fill the gap with `LinearEquiv.refl`/a toy equivalence; keep `Ind1ShellTransportGap` as the precise interface until an actual place-equality or a proved completion isomorphism is supplied.

## No fake closure
No old C3, no `IsEmpty`, no new axiom/sorry. The fixed-place inhabitant is a genuine conditional construction, not a claim that arbitrary Ind1 is handled.
