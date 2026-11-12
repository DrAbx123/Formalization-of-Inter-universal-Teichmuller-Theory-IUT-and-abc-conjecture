# S2807 — Route to `S2717UpperGap`

Date: 2026-11-07. Audit of `S2717Cor312FullTargetActual.S2717_full_iff_hupper`.
This is a route decomposition, not a proof of the upper gap and not an ABC
hypothesis.

## 0. Exact objects

```lean
S2717UpperGap := S2717ThetaHullLogVolume ≤ CThetaPaper * paperQAbsLog

S2717ThetaHullLogVolume :=
  - (globalThetaHullInterface.logVolume globalThetaHull).toReal

CThetaPaper := ((l+1)/4 / paperQAbsLog) * cThetaBracket - 1
paperQAbsLog := (1/(2l)) * logQ
```

`S2717_full_iff_hupper` (ACTUAL) reduces `PaperCor312Full` to this gap *given*
the actual q normalization and the xi-f containment:
`hq : log q ≠ 0`, `habs : |log q| = paperQAbsLog`, `hqPilot`, `hxi`.

## 1. Subgoals

### SG1 — Concrete theta-hull volume identity (likely mechanical, FIRST TARGET)

Claim: `S2717ThetaHullLogVolume` equals the actual Haar log-volume of the C3
log-shell tensor region:

```lean
S2717ThetaHullLogVolume ...
  = - (haarLogVolume (actualC3LogShellTensorHaar C3)
        (actualC3LogShellTensorRegion C3)).toReal
```

Evidence available: `globalThetaHullInterface` is defined with
`logVolume := globalThetaLogVolume = haarLogVolume actualC3LogShellTensorHaar`;
`globalThetaHull = actualHolomorphicHull actualC3LogShellTensorRegion`, and
`globalThetaHull_eq_imageSet` + `actualUnitRegion = actualC3LogShellTensorRegion`
identify the hull with the actual region.

Status: **ACTUAL**. `S2807ThetaHullVolumeIdentityActual.lean` proves
`S2807_thetaHullVolume_eq_haarRegion` (olean 65168 B,
SHA CB428FCE8621AC97D5F1DC3A9395C22E7A5B46109B823901B2110D22FA5DDFA7;
axioms trio). SG1 is closed. It was proved by unfolding
`S2717ThetaHullLogVolume`, simplifying the interface/logVolume projections,
and rewriting `globalThetaHull_eq_imageSet`.

### SG2 — CTheta algebra (ACTUAL)

`S2715CThetaPaperScaleActual` is ACTUAL and supplies:
`CThetaPaper_def_eq`, `cThetaPaperFactor_pos`, `CThetaPaper_ge_neg_one_iff`,
`CThetaPaper_lowerBound_of_thetaHull_upper`, `CThetaPaper_lowerBound_of_paperAbsLog`.
These reduce the CTheta lower-bound side to the upper inequality; they do not
prove the upper inequality.

### SG3 — Analytic hull-volume comparison (MISSING, main gap)

After SG1 and SG2, the remaining inequality is the IUT IV estimate

```lean
- (haarLogVolume actualHaar actualRegion).toReal
  ≤ CThetaPaper * paperQAbsLog
```

Equivalently a lower bound on `CThetaPaper` via the actual region volume.
Current actual files (`HullDeterminantLogVolumeReduction`, `S2725`, S2742)
provide determinant/packet identities and the hull construction, but NOT this
comparison for the S2717 theta hull. This is the missing analytic object.

#### SG3a — packet reduction (ACTUAL)

`S2807SG3aActual.lean` is ACTUAL (olean 68800 B,
SHA 6090BAB780B7DAFA900B70406D70114099B2E6C703E994E99B78CD213AFAB4A7;
axioms trio) and proves:

```lean
S2807_thetaHullVolume_eq_neg_tensorLogVolume :
  S2717ThetaHullLogVolume ... = - actualC3LogShellTensorLogVolume C3

S2807_upperGap_iff_neg_tensorLogVolume :
  S2717UpperGap ... ↔
    - actualC3LogShellTensorLogVolume C3
      ≤ CThetaPaper * paperQAbsLog
```

#### SG3b — scalar reduction (ACTUAL conditional)

`S2807SG3bScalarActual.lean` is ACTUAL (olean 60032 B,
SHA C005563CD8A31487B830839E4379DEB2233FAF31FB4931EBC1F499C7917A09D2;
axioms trio) and proves:

```lean
S2807_upperGap_of_packetLogVolume_le
  (hpacket : actualC3LogShellTensorLogVolume C3 = packetLogVolume)
  (hscalar : -packetLogVolume
      ≤ CThetaPaper fiveLabel logQ ... * paperQAbsLog fiveLabel logQ) :
  S2717UpperGap ...
```

So after the packet identity, the remaining scalar target is exactly
`-packetLogVolume ≤ CThetaPaper * paperQAbsLog`; `S2715`'s actual
`CThetaPaper_ge_neg_one_iff` converts the CTheta side to the bracket inequality.

#### Exact missing packet

The audit of `HullDeterminantLogVolumeReduction`, `S2725`, `S2742`, `S349`:

- actual: `packetLogVolume_eq_matrixLogDet`, `packetDiagonalMatrix_tensor`,
  `packetLogVolume_tensorPower`, `profileArithmeticDegree_*` (generic packet/det
  identities);
- actual: `globalThetaHullInterface` and the S2742 source-hull measure transport
  (on `OriginalInput`, not the C3 tensor block);
- actual: S349 `actualC3LogShellTensorRegion_eq_tensorLogShellRegion` and the
  tensor lattice region compactness/positivity;
- NOT present: a formula computing the actual C3 tensor log-volume from the
  local log-shell data.

Exact missing packet:

```lean
S2807C3TensorPacketLogVolumeFormula (C3) :
  actualC3LogShellTensorLogVolume C3
    = profileArithmeticDegree
        (fun i : C3.tensorIndex =>
          (haarLogVolume (Measure.addHaar : Measure (C3LogShellFiber C3 i))
            (actualC3LogShell C3 i)).toReal)
```

or an equivalent determinant/log-volume identity. Only after this packet identity
can SG3b's `hpacket` be discharged; it is the precise missing packet.

### SG4 — Actual q normalization / pointwise q identification (PARTIAL)

`S2717_full_iff_hupper` requires `hq`, `habs`, `hqPilot`. `S2691` gives the
normalization `paperQAbsLog = (1/(2l)) logQ`; the actual `q_Tate` identification
and `hqPilot = -|log qParameter|` remain object-level inputs. `S2708`/`S2711`
multi-place q-pilot data are actual, but the S2717 `hqPilot` identification is
not supplied here.

### SG5 — xi-f containment `hxi` (PARTIAL/actual consumers)

`hxi : S2717QPilotLogVolume ≤ S2717ThetaHullLogVolume`. The xi-f consumer side
is represented by the actual S2711 multi-q object; a direct instantiation for
the S2717 source data is still to be checked. This is not the analytic upper gap.

## 2. Actual vs missing

| subgoal | status |
|---|---|
| SG1 concrete theta-volume identity | **ACTUAL** (`S2807_thetaHullVolume_eq_haarRegion`) |
| SG2 CTheta algebra | ACTUAL (S2715) |
| SG3 analytic hull-volume comparison | SG3a packet reduction ACTUAL; SG3b scalar reduction ACTUAL conditional; missing packet identity |
| SG4 q normalization/q_Tate identification | PARTIAL (S2691 actual; q_Tate missing) |
| SG5 xi-f containment | PARTIAL consumers; direct S2717 instantiation missing |

## 3. First executable target

**SG1 is DONE (actual).** SG3 is now cleanly isolated as the single analytic
inequality:

```lean
- (haarLogVolume actualHaar actualRegion).toReal
  ≤ CThetaPaper * paperQAbsLog
```

SG3a and SG3b are ACTUAL reductions. Next attack the exact missing packet
`S2807C3TensorPacketLogVolumeFormula` (actual C3 tensor log-volume = arithmetic
degree of local log-shell log-volumes), then the scalar bracket inequality.
Do not use ABC or pointHeightDictionary.

## 3b. ATheta carrier status

The minimal source ATheta carrier `S2736SourceAThetaCarrierActual` is now ACTUAL
(src 17077FD4..., olean 226192 B, SHA 738A607E09E75B118A2D46361F776D9C6A86D661FB3861AF0F2ABC7D2E7295B6;
axioms trio). It is no longer BROKEN. The six ATheta geometric/data objects still
remain missing.

## 4. Non-assumptions

- No ABC conjecture or `ABCHeightWeightAdditiveBoundV2` is assumed.
- No pointHeightDictionary is used.
- No claim that `S2717UpperGap` is proved.
