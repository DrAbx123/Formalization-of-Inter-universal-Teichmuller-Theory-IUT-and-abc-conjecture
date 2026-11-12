# S2813 / SG3a — theta-hull upper gap transport

Date: 2026-11-07
Status: **ACTUAL reduction**, plus one precise missing packet identity.

## File

`tmp/sheaf/xif/paper/S2813SG3aHullDeterminantTransportActual.lean`

```text
src 5392 B
SHA256 354fc21cf855e933856338c56628a91bd37a88afbb777984a1f0447941f39b42
olean 84712 B
SHA256 810e0e9ee266da3bbeea4b1de8042095a62b6f31f8d15cc63bebbe7d78e25e79
EXIT=0
AXIOMS [propext, Classical.choice, Quot.sound]
QUEUED
```

## SG3a-1: theta hull = negative C3 tensor log-volume

```lean
theorem S2813_thetaHull_eq_neg_tensorLogVolume :
    S2717ThetaHullLogVolume ... places tuple nu D =
      - actualC3LogShellTensorLogVolume (S2717C3 ... D)
```

This is the packet-level form of S2807; proof rewrites the SG1 identity and
closes definitionally.

## SG3a-2: upper gap = scalar inequality

```lean
theorem S2813_upperGap_iff_tensorLogVolume
    (logQ dmod dFpd fFpd eStar etaPrm : Real) :
    S2717UpperGap ... logQ dmod dFpd fFpd eStar etaPrm ↔
      - actualC3LogShellTensorLogVolume (S2717C3 ... D)
        ≤ CThetaPaper fiveLabel logQ dmod dFpd fFpd eStar etaPrm *
            paperQAbsLog fiveLabel logQ
```

So the entire S2717 upper gap is now one scalar inequality on the actual
C3 log-shell tensor log-volume.

## SG3a-3: reduce to packet identity + scalar inequality

```lean
theorem S2813_upperGap_of_packetScalar
    {label : Type} [Fintype label]
    (packet : PositivePacket label)
    (hpacket : actualC3LogShellTensorLogVolume (S2717C3 ... D) =
      packetLogVolume packet)
    (hscalar : -packetLogVolume packet ≤
      CThetaPaper fiveLabel logQ ... * paperQAbsLog fiveLabel logQ) :
    S2717UpperGap ... logQ ...
```

Given the packet identity and the scalar inequality, the upper gap follows.
Axioms trio.

## SG3a-4: actual finite packet determinant identity

```lean
theorem S2813_packetLogVolume_eq_matrixLogDet
    {label : Type} [Fintype label] [DecidableEq label]
    (packet : PositivePacket label) :
    packetLogVolume packet =
      matrixLogDet (packetDiagonalMatrix packet)
```

Reuses `HullDeterminantLogVolumeReduction.packetLogVolume_eq_matrixLogDet`.
The determinant/tensor/rescaling/tensor-power identities in that file are
actual finite-packet identities (`packetLogVolume_eq_log_det`,
`packetDet_tensor_via_det_kronecker`, etc.).

## 4. Exact missing packet identity

The actual tree has **no** theorem of the form

```lean
actualC3LogShellTensorLogVolume (S2717C3 ... D)
  = packetLogVolume packet
```

for any `PositivePacket packet`.  Reasons:

1. `actualC3LogShellTensorLogVolume` is defined directly as
   `(haarLogVolume (actualC3LogShellTensorHaar C3)
      (actualC3LogShellTensorRegion C3)).toReal`.
   It is a Haar measure of an arbitrary finite tensor integral region, not a
   finite diagonal packet.
2. `HullDeterminantLogVolumeReduction` proves determinant/log-volume identities
   only for the finite `PositivePacket` model (diagonal matrices and their
   Kronecker/tensor powers).  It explicitly says the paper's IQ carrier,
   `det (x) M` operation, and source log-volume normalization are cards, not
   constructed objects.
3. `actualC3LogShellTensorPacket` records the same real number as a field
   `logVolume_eq : logVolume = actualC3LogShellTensorLogVolume`; it does not
   decompose it into local packet scales or a determinant.
4. No theorem in the tree identifies the C3 tensor integral region's Haar
   volume with a product/Kronecker determinant of local log-shell volumes.

Therefore SG3a reduces the upper gap to:

```text
(packet identity: V_C3 = packetLogVolume packet)
+ (scalar inequality: -packetLogVolume packet ≤ CThetaPaper * paperQAbsLog)
```

The scalar part is available in principle from the source q-normalization; the
packet identity is the exact missing transport.

## 5. What would close SG3a

Either:

- construct a genuine `PositivePacket` (or a determinant bookkeeping object) from
  the C3 local log-shell data, with scales equal to the local Haar volumes and
  `packetLogVolume packet = actualC3LogShellTensorLogVolume C3`; or
- prove the Haar product formula for
  `tensorIntegralRegion` / `FinitePadicTensor` directly and identify the sum
  of logs with `matrixLogDet` of the resulting diagonal matrix.

Until then, do not assert the packet identity.  No fake packet, no axiom.

## 6. Relation to SG1

SG1 (`S2807_thetaHullVolume_eq_haarRegion`) gives
`S2717ThetaHullLogVolume = -haarLogVolume region`.
SG3a replaces `haarLogVolume region` by the named actual C3 tensor log-volume
and reduces the gap to a packet identity + scalar inequality.
