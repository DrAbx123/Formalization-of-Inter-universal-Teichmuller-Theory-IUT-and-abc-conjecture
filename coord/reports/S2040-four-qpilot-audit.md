# S2040 four q-pilot identifications / paperO / FirstMissing audit

Date: 2026-11-02. Layer: **O** (original Theta-link, IUT III Cor 3.12, Step xi-f).
No target change, no fake, no new axiom.

## Files read

- `tmp/sheaf/xif/paper/S2040ActualThetaLink312.lean` (520 lines, SHA256
  `E53A19EE604CD91DF38E0879196AEB7E183714EBBEC7F6A5712538CDD9092F42`)
- `tmp/sheaf/xif/paper/S2040ActualThetaLinkActual.lean` (144 lines, SHA256
  `0DABDCD7F3B28B2B96B2A7CBE30B2C80E70EE5F3B4CFA615F985CD3068F72648`)
- `coord/reports/S2040-actual-theta-link.md`
- `tmp/sheaf/xif/paper/ThetaLinkActual.lean` (four-field definition)
- `tmp/sheaf/xif/paper/ThetaLinkLogKummerActual.lean` (actual one-column q)
- `tmp/sheaf/xif/paper/OrigXiFPaperQPilotObjectActual.lean` (concrete object)
- `tmp/sheaf/xif/paper/OrigXiFPaperLineBundleActual.lean`,
  `OrigXiFPaperLineBundleODActual.lean`, `OrigXiFPaperLogKummerActual.lean`
- `tmp/sheaf/xif/paper/ConcreteQPilotLogIdentificationActual.lean`
- `tmp/sheaf/xif/paper/S2040RootStackThetaPilotActual.lean`

## Source object and domain

- Source object: `PaperQPilotObject` (frozen O-layer data) and
  `S2038PaperOActual` (actual one-column q, (1,0)/(0,0) strips, four paper
  identifications).
- Consumer target: `S2040ThetaLink312` and
  `s2040_paper312_of_firstMissing : S2040FirstMissing -> -|log Opaper.q| <=
  P.signedHullLogVolume`.
- Domain: original-text O/Theta-link data; not the normalized model, not
  SourceDefinition31Data/D4-D9, not reduced S1880/S1905/S1944 routes.

## Exact four identifications

`thetaLinkQPilotPaperIdentifications O` is definitionally

```text
O.paper_strip_identification
∧ O.paper_lineBundle_identification
∧ O.paper_logKummer_identification
∧ O.paper_qPilot_log_identification
```

| # | Field | Current actual object / concrete shadow | Paper target / exact missing |
|---|---|---|---|
| 1 | `paper_strip_identification : OrigXiFPaperStripIdentified boundary strip` | `OrigXiFPaperQPilotObjectActual` proves `strip = sourceQPilotStrip boundary` and `boundary.target_q = boundary.theater.thetaPacket.q` | F^boxplus-triangleright-x-mu-prime-strip at (1,0); the concrete field is only the source strip anchor, not the paper poly-isomorphism. |
| 2 | `paper_lineBundle_identification` | actual O(-D) carrier exists in `OrigXiFPaperLineBundleActual` / `ODActual`, conditional on `OrigXiFPaperLineBundleData` | the frozen concrete object uses the completion-localized trivial carrier; paper target is the actual fractional-ideal O(-D) carrier. Exact first field: native totalization `X.S.arithmetic = I.initial.arithmetic` (`arithmetic_root_eq`). |
| 3 | `paper_logKummer_identification` | actual reduced `SourceKummerArrow`; its x-mu layer satisfies Definition 4.9(i) invariant-image and degree preservation | paper log-Kummer representation of q-pilot on `1,circ U_Q`; the reduced arrow does not identify with it. Exact first field: `FPrimeStripEquiv envStrip (sourceQPilotStrip boundary)` (vertical coricity). |
| 4 | `paper_qPilot_log_identification` | actual scalar `O.qPilotLogVolume = sourceQPilotSignedLog I.initial = -OrigXiFPaperBadQAbsLog` | paper scalar `-|log C3.q|`; exact missing `ConcreteSourceQIdentification`: `sourceQPilotSignedLog I.initial = localSignedLog C3.q`. |

Important: `OrigXiFPaperQPilotObjectActual.origXiFPaperQPilotObjectActualFrozen_identifications`
does prove the **four frozen Prop fields** for the concrete finite model. That is
a kernel-checked inhabitation of the frozen fields, but S2040 itself records that
these are concrete shadows (source strip anchor, trivial/completion carrier,
reduced Kummer arrow, bad-place absolute-log scalar), not the paper objects. It
must not be used as the paper target without the four bridges above.

## `O.qPilotLogVolume = Real.log Opaper.q`

Actual chain:

1. `O.qPilotLogVolume = sourceQPilotSignedLog I.initial` (actual field
   `qPilotLogVolume_eq`; see `ConcreteQPilotLogIdentificationActual`).
2. `I.qPilotSignedLogVolume = -|Real.log I.oneColumnQAtZero|` (rfl in
   `ThetaLinkLogKummerActual`), with `oneColumnQAtZero_pos` proved.
3. For `q = I.oneColumnQAtZero` and `0 < q < 1`,
   `s2040_signedLog_eq_log` gives `-|log q| = log q`.

The equality is **not** automatic from the actual object. It needs both:

- the contracting condition `q < 1` (an explicit field of
  `S2038PaperOActual`, not proved from bare `OriginalInput`);
- the source-scalar comparison `sourceQPilotSignedLog I.initial =
  localSignedLog C3.q` (exact first missing
  `ConcreteSourceQIdentification`), which is a q-pilot/one-column source
  identification, not a definitional equality.

Thus `qPilotLogVolume = log Opaper.q` is a **conditional** component, not a
first constructible one.

## Displacement conditions

`S2040ThetaLinkDisplacement Opaper` contains:

1. `unitsMu : S2040UnitsMuLink`: actual groups U,V, equivalence e, subgroups
   mu/nu, and `carries_mu`. Exact missing: paper local O^x/O^x-mu ambient
   carrier and completion bridge (`S2040CompletionBridgeRequired`,
   `S2040CompletionLayersActual`: ring equiv, integral-units equiv, S2046 norm
   bridge).
2. `thetaPilotStrip = I.primeStripAt 0 0`, `qPilotStrip = I.primeStripAt 1 0`:
   actual strip fields can be filled definitionally.
3. `rootStackTheta = s2040Theta l Opaper.q` and
   `rootStackTheta^(2l) = Opaper.q`: scalar root/power is proved
   unconditionally; the actual root-stack object
   `S2040RootStackThetaPilotObject` exists on the hodgeTwoLthRoot carrier
   conditionally on native `T`, but the paper O^x/O^x-mu ambient is missing.
4. `ambientQ/ambientTheta`, embeddings, integer/real degree maps,
   injectivity, unit-degree, generators and their log/degree conditions:
   these require the actual paper local O^x/O^x-mu/ambient value groups and
   log-degree readouts; exact missing above.
5. `S2040HullNormalization Opaper P D`: `P.signedHullLogVolume =
   log D.rootStackTheta`; exact first missing `RootThetaHullNormalizationGap` /
   `PaperRootHullFormulaGap` (procession normalization xi-d/xi-e).

## Which can be constructed first, and what depends on 3.11/Eta

Ordering proposed (no target change):

1. **First executable, not yet paper-faithful:** fill the `S2038PaperOActual`
   strip fields from `I.primeStripAt 1 0` / `0 0`, and q from
   `I.oneColumnQAtZero` with `q_pos` actual and `q_lt_one` as an explicit
   hypothesis. This is a real construction of the interface skeleton but does
   not close the four paper identifications.
2. **First genuine missing object (independent of 3.11/Eta):**
   `OrigXiFPaperLineBundleData` native totalization
   (`arithmetic_root_eq`), then the actual O(-D) carrier and its identification.
   This is the line-bundle component; it does not need 3.11 or Eta.
3. **Depends on 3.11:** log-Kummer component. `FPrimeStripEquiv envStrip
   (sourceQPilotStrip boundary)` and the paper representation on `1,circ U_Q`
   require the Theorem 3.11 one-column vertical Kummer/1-column log-Kummer
   input (`OneColumnLogKummerData` is a structure with no inhabitant on the
   target path).
4. **Depends on 3.11 (source q comparison):** q-pilot scalar identification
   `O.qPilotLogVolume = log Opaper.q`; needs `ConcreteSourceQIdentification`
   plus `q < 1`.
5. **Depends on Eta / Theta-pilot / 3.12:** displacement root-stack Theta,
   paper O^x/O^x-mu units and hull normalization
   (`P.signedHullLogVolume = log rootStackTheta`). The scalar root exists, but
   the actual Θ-pilot/Eta normalization and O^x ambient carriers are missing.

## Exact first missing

```text
S2040FirstMissing O Opaper P
  = fourIdentifications
    ∧ S2040QPilotLogIdentification O Opaper
    ∧ ∃ D : S2040ThetaLinkDisplacement Opaper,
        S2040HullNormalization Opaper P D
```

For an executable next step, do **not** claim the concrete four fields close
the paper target. The first missing subgoal with the least target-coupling is:

```text
S2040PaperOStripSkeleton:
  q = I.oneColumnQAtZero, 0 < q, q < 1,
  qPilotStrip = I.primeStripAt 1 0,
  thetaPilotStrip = I.primeStripAt 0 0
```

followed by

```text
OrigXiFPaperLineBundleData:
  X : N8NativeInput l,
  X.S.arithmetic = I.initial.arithmetic
```

The paper log-Kummer scalar/representation and displacement/hull normalization
must wait for the 3.11/Eta inputs above.

## New Lean audit artifact

`tmp/sheaf/xif/paper/S2040FourQPilotAuditActual.lean`

```text
EXIT=0
olean=YES
lines=77
SHA256=642A1A21D0AFB26A888486E33F7E8C62DC7A5826A51489CC8F659652455ED245
olean path=.lake/build/lib/lean/tmp/sheaf/xif/paper/S2040FourQPilotAuditActual.olean
axioms: propext, Classical.choice, Quot.sound
```

It defines the four-field name, the definitional decomposition
`s2040FourQPilotIdentifications_iff`, the exact `S2040PaperOConstructionRequired`
interface, and aliases for `S2040DisplacementRequired`,
`S2040QPilotLogRequired`, `S2040HullNormalizationRequired`. No inhabitant of
the paper object or first-missing chain is asserted; no target is changed.

## Consumer

`s2040ThetaLink312_of_firstMissing`, `s2040_inclusion_of_firstMissing`,
`s2040_paper312_of_firstMissing`; the derived theorem
`S2040ThetaLink312.paper312_inequality` remains the actual consumer of a
future inhabitant.

## Reports read

`coord/reports/S2040-actual-theta-link.md` (superseding milestone; remaining
gaps: root-stack Theta, O^x/O^x-mu, hull normalization, four paper O
identifications); `ConcreteQPilotLogIdentificationActual` header (exact
`ConcreteSourceQIdentification`); `OrigXiFPaperLineBundleActual` header
(native totalization first field); `OrigXiFPaperLogKummerActual` header
(vertical coricity first field).
