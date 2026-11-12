# S1203: second joint — SourceCapsulePacketRealization / capsule→tensor

Date: 2026-10-30.  Read: `S1154HDDPreauditActual.lean`,
`S1156CapsuleTensorAuditActual.lean`, `S1169CapsulePacketBridgeActual.lean`,
`S1176CapsulePacketBridgeAttemptActual.lean`, `PrimeStripLogShellActual.lean`,
`C3LogShellTensorPacketActual.lean`, `FinitePadicTensorLogShellRealization.lean`.
`S1162` is not present in the tree (nearest is S1156).

## 1. Actual donors found

* `PrimeStripLogShellActual.actualDFPrimeStripCapsule`: actual D/F prime-strip
  capsule from `I.primeStripAt 1 0`, with `dStrip = fStrip.toDPrimeStrip` rfl.
* `PrimeStripLogShellActual.actualC3LogShellDatum` / `actualC3LogShell`: actual
  local `SourceLogShellDatum` at each C3 tensor place; logShell is the actual
  integralLogShell (`actualC3LogShell_eq_integralLogShell`).
* `C3LogShellTensorPacketActual.actualC3LogShellTensorPacket`: actual tensor
  packet with `region = actualC3LogShellTensorRegion`, compactness
  (`actualC3LogShellTensorRegion_compact`), IQ span
  (`actualC3LogShellTensorIQ`), actual additive Haar and Haar log-volume.
* `OriginalInput.H2FProcession.canonical`: actual H2 procession.
* `LocalFieldPadicTensor.exists_realized_tensorLogShell_hull`: actual finite
  field-product log-shell hull with Haar positivity/finiteness/log.

## 2. What is still absent

There is no declaration `SourceCapsulePacketRealization` in the tree.
More importantly, the actual C3 tensor packet is indexed by
`C3.tensorIndex`, not by the reduced algorithm `Choice`; and there is no
choice-indexed map

```text
Choice → SourceLogShellActualIQTensor D
```

with actual nonzero tensor points.  S1176 constructs the capsule index part
(`Choice → H2FProcession I`, constant canonical) but its tensor half is exactly
the gap `S1176TensorPointGap` (exists tensorPoint in integral tensors, nonzero
for every c).  S1169's `SourceCapsulePacketActualBridge` leaves both
`capsuleIndex` and `tensorPoint` as fields; S1172's constant zero tensor point
is degenerate and is not a source construction.

## 3. Concrete finite case

A concrete C3 packet can be made actual **only conditionally on the C3 donor**
`SourcePilotRegionDonors` (via `actualC3OfDonors`, then
`actualC3LogShellTensorPacket`).  That donor itself contains the tensor landing
field and has no production inhabitant in the tree; `C3` is not unconditional.
Even with that donor, no map `Choice → C3.tensorIndex` and no
`PrimeStripC3PlaceComparison` exists, so the capsule/tensor realization still
does not land on the reduced Choice output.

## 4. Exact first gap

There are two equivalent first objects, depending on which side is taken:

1. Source/strip side:

```text
PrimeStripC3PlaceComparison (V := V) (I := I) C3 :=
  indexEquiv : V ≃ C3.tensorIndex
  stripPlace : V → FinitePlaceAtPrime I.initial.arithmetic.Fmod C3.p
  stripPlace_eq : ...
```

2. Tensor side:

```text
choiceIndexedTensorPoint :
  Choice → SourceLogShellActualIQTensor D
```

with each point in `sourceLogShellActualIntegralTensors D` and nonzero (the
nondegenerate form required by S1176).  Neither object is constructed by the
current actual donors.

Consumer: `SourceCapsulePacketRealization` → HDD readout / capsule-tensor
consumers (`SourceCapsulePacketActualBridge`, `SourceHDDReadout`).  The actual
C3 packet supplies region/measure/log for its own `C3.tensorIndex` only; it
does not supply the reduced-choice point map.

## 5. Verdict

```text
actual D/F capsule                         yes (PrimeStripLogShellActual)
actual C3 local log-shells                  yes
actual C3 tensor packet                     yes (conditional on C3 donor)
C3 donor / tensorLanding                     no inhabitant in tree
SourceCapsulePacketRealization              absent
Choice -> SourceLogShellActualIQTensor      absent
nondegenerate tensor point                  absent
first gap                                   PrimeStripC3PlaceComparison
                                            or choiceIndexedTensorPoint
no Lean wrapper written                      yes: exact gap only
```

No weak `compatible` Prop, `Nonempty` gate, `True`, `PUnit`, arbitrary
`Classical.choice` map, or field-shifting wrapper is written.
