# S2804 — IUT III Corollary 3.12 actual-object inventory

Date: 2026-11-07
Scope: reusable actual objects for Cor 3.12; no ABC hypothesis assumed.
Evidence: declaration inspection + existing `.olean` presence under
`.lake/build/lib/lean/`. This is an inventory, not a new proof or a kernel audit.

## 0. Verdict in one paragraph

Cor 3.12 currently has a **real reduction to one analytic inequality**, not a proof:
the paper target `PaperCor312Full` is definitionally equivalent (under the actual
q-normalization) to the single IUT IV upper estimate `S2717UpperGap`
(`S2717_full_iff_hupper`). Theta-pilot carrier/hull/log-volume, local log-shell
interfaces, H1/H2 constructions, and conditional Step-XI assemblies are actual.
The missing target is the upper gap itself, plus the geometric ATheta objects and
the D-Theta realization gate. The hweightvol inequality is now ACTUAL (see
`S2752FinalHweightvolActual` / `S2752_hweightvol`), so it is no longer a missing
target.

Do **not** claim "Cor 3.12 proved" or any ABC consequence from this inventory.

---

## 1. Actual reusable objects

### 1.1 Theta pilot

| Object | File | Main declarations | Status |
|---|---|---|---|
| Paper theta-pilot carrier | `tmp/sheaf/xif/paper/PaperThetaPilotCarrierActual.lean` | `PaperThetaPilotCarrier := (ZMod l.value)ˣ`; `paperThetaValue`; `paperPossibleImageSet`; `paperThetaPilotHull`; `paperPossibleImage_subset_hull`; `paperThetaPilotHull_candidate`; `globalPaperProcessionThetaLogVolume` | source present; no standalone olean in this build tree |
| Theta hull log-volume | `tmp/sheaf/xif/paper/PaperThetaPilotHullLogVolumeActual.lean` | `paperThetaPilotHullSet`; `paperThetaPilotHullVolume`; `paperThetaPilotHullLogVolume`; `PaperThetaPilotHullNormalizationData`; `PaperThetaPilotHullNormalizationRequired` | source present; no standalone olean |
| Global theta-pilot hull log-volume | `tmp/sheaf/xif/paper/GlobalThetaPilotHullLogVolumeActual.lean` | `globalThetaHullLogVolume`; `globalThetaImageLogVolume`; `globalQPilotLogVolume`; `thetaImageVolumeAt_le_hullVolumeAt`; `GlobalThetaPilotHullLogVolumeData` | **olean 177744 B** |
| Global theta image/hull interface | `tmp/sheaf/xif/paper/S2725GlobalThetaHullActual.lean` | `GlobalThetaCarrier`; `globalThetaImageSet`; `globalThetaHull`; `globalThetaUnitRegion`; `globalThetaLogVolume`; `globalThetaLogVolume_mono`; `globalThetaHullInterface : IQHullLogVolumeInterface` | **olean 129096 B** |
| Global theta-pilot object | `tmp/sheaf/xif/paper/ThetaPilotGlobalObjectActual.lean` | global theta-pilot object interface | source only / not audited here |
| Arithmetic theta divisor | `tmp/sheaf/xif/paper/ThetaPilotArithmeticDivisorActual.lean` | arithmetic divisor interface | source only / not audited here |
| Theta-pilot global product | `tmp/sheaf/xif/paper/ThetaPilotGlobalProductActual.lean` | product-formula interface | source only / not audited here |

Reusable now: `globalThetaHullInterface`, `globalThetaHull`, `globalThetaLogVolume`,
`thetaImageVolumeAt_le_hullVolumeAt`, `globalThetaPilotHullLogVolumeData`.

### 1.2 Log-shell

| Object | File | Main declarations | Status |
|---|---|---|---|
| Completion log-shell interface | `tmp/sheaf/xif/paper/S2718LogShellInterfaceActual.lean` | `S2718_completionLogShell_interface`: compact + open + contains completion integers + receives completion unit log + stable under integral p-adic scalars; `S2718_completionLogShell_eq_unitLog_range` | **olean 43744 B** |
| Source log-shell realization | `tmp/sheaf/xif/paper/S2600LogShellRealizationActual.lean` | `SourceImageRealizationLogShell` extends `SourceImageRealization` with `hdeg`; `S2600_sourceLocalLogDegree_thetaPilotPoint` | **olean 89536 B** |
| Log-shell port to rational points | `tmp/sheaf/xif/paper/S2601LogShellPortActual.lean` | `S2601_sourceLocalLogDegree`: `sourceLocalLogDegree v (point) = Real.log ‖pointMap‖` | **olean 26832 B** |
| Source log-shell carrier | `LeanFormal/IUT/IUTII/Kummer/SourceLogShellCarrier.lean` | source carrier / action compatibility base | **olean 495224 B** |
| Log-shell actual tensor span | `LeanFormal/IUT/IUTII/Kummer/SourceLogShellActualTensorSpan.lean` | tensor-span realization | **olean 137056 B** |
| Integral log-shell sharp bounds | `LeanFormal/IUT/Foundations/LocalFields/IntegralLogShellSharpBounds.lean` | local integral log-shell bounds | olean present (not re-audited here) |
| Finite p-adic tensor log-shell realization | `LeanFormal/IUT/Foundations/LocalFields/FinitePadicTensorLogShellRealization.lean` | local tensor log-shell | olean present |

Reusable now: `S2718_completionLogShell_interface`,
`S2601_sourceLocalLogDegree`.

Exact conditional: `S2600` requires a `SourceImageRealizationLogShell` whose
`hdeg` field is *supplied*; it does not construct that refinement from
`OriginalInput`.

### 1.3 H1/H2 and D-Theta

| Object | File | Main declarations | Status |
|---|---|---|---|
| Source H1/H2 construction | `LeanFormal/IUT/IUTIII/Theorem311/SourceH1H2Construction.lean` | `DThetaBridge`; `bridge`; `H1FamilyPackage`; `h1`; `h1_complete`; `H2FProcession` / `H2DProcession` / `H2SpokePermutation`; `H2ConstructionPackage`; `h2_complete_at_stage`; `h1_h2_source_closed`; `h1_h2_before_theorem311_output` | **olean 2944136 B** |
| Source H1/H2 original arrows | `LeanFormal/IUT/IUTIII/Theorem311/SourceH1H2OriginalArrows.lean` | `H1PrimeDProjection`; `H1LinkArrow`; `H1CoordinateWiring`; `H2ColumnSourceLedger`; `H2HorizontalSourceLedger`; `H2SpokeSourceLedger`; `H1H2SourceContract`; `DThetaRealizationGate` | **olean 1226584 B** |
| Source D-Theta construction | `LeanFormal/IUT/IUTIII/Theorem311/SourceDThetaConstruction.lean` | D-shadow construction; requires H1/H2 input | **no olean**; not currently actual |
| Sign-quotient geometric core | `LeanFormal/IUT/IUTI/InitialTheta/SourceSignQuotientConstruction.lean` | `SourceSignQuotientGeometricCore`; `toSourceCompletionSignQuotient`; `toSourceSignQuotientData` | **olean 560840 B** |
| Clause assembly / unit reduction | `LeanFormal/IUT/IUTI/HodgeTheater/SourceClauseAssemblyUnitsReduction.lean` | `SourceClauseELocalFamilyUnit`; `SourceClauseFBoundaryUnit`; `clauseAssemblyOfUnits`; `sourceClauseAssemblySupply_of_unitChain`; `GeometricCoreStackUnit` | **olean 528048 B** |

Reusable now: `H1H2SourceContract`, `H1FamilyPackage`, `H2ConstructionPackage`,
`SourceSignQuotientGeometricCore`, `clauseAssemblyOfUnits`.

Missing target: an inhabitant of `DThetaRealizationGate`. The file explicitly
does not manufacture one. `SourceDThetaConstruction` has no olean and should not
be listed as actual without compiling/fixing it.

Do not rebuild these: they already exist; the inventory should be consumed, not
duplicated.

### 1.4 Cor 3.12 bound / final assembly

| Object | File | Main declarations | Status |
|---|---|---|---|
| Paper Cor 3.12 full target | `tmp/sheaf/xif/paper/S2717Cor312FullTargetActual.lean` | `S2717C3`; `S2717ThetaHullLogVolume`; `S2717QPilotLogVolume`; `S2717UpperGap`; `PaperCor312Full`; `S2717_hupper_of_full`; `S2717_full_of_hupper`; `S2717_full_iff_hupper` | **olean 91472 B**; target is a Prop, not proved |
| Multi-q Stage A | `tmp/sheaf/xif/paper/S2717StageAMultiQActual.lean` | `qProduct`; `qProduct_pos`; `qProduct_le_one`; `qProduct_lt_one_iff_nonempty`; `stageAQParameterSigned_multi`; `arithmeticTupleIQHullCertificateQ_multi`; `arithmeticTupleIQHullLinkEvidenceQ_multi`; `arithmeticTupleIQHullCor312ConclusionQ_multi` | **olean 167464 B** |
| Stage A signed q | `tmp/sheaf/xif/paper/S2716StageAQSignedActual.lean` | `S2716QParameter := exp(-qSigned)`; `S2716_qSigned_eq_neg_abs_log`; `S2716_qSigned_le_theta`; `S2716ComparisonData` | **olean 45040 B** |
| Final assembly, explicit inputs | `tmp/sheaf/xif/paper/S1000FinalCor312AssemblyActual.lean` | `S1000FinalInputs`; `s1000FinalCor312`; `s1000Cor312Conclusion` | **olean 328072 B** |
| Final assembly, direct link | `tmp/sheaf/xif/paper/S1024FinalCor312Actual.lean` | `s1024FinalCor312` | **olean 34272 B** |
| Cor 3.12 conclusion type | `LeanFormal/IUT/IUTIII/Corollary312/StepXI/Contract.lean` | `StepXIContract`; `Cor312Conclusion contract := contract.qSigned ≤ contract.thetaSigned`; `cor312_of_constructed_stepXI` | actual |
| Pointwise residual supply | `LeanFormal/IUT/ABCBridge/Bridge/Cor312PointwiseResidualSupply.lean` | `cor312Pointwise_spikeCarrier`; `Cor312PointwiseResidualData`; `cor312PointwiseResidualData_hptfin`; `cor312PointwiseResidualData_hpoint`; `cor312PointwiseResidualData_epsilonComparison` | **olean 327024 B** |
| q-pilot line bundle / hweightvol | `tmp/sheaf/xif/paper/S2736QPilotLineBundleHweightvol.lean`; ACTUAL via `tmp/sheaf/xif/paper/S2752FinalHweightvolActual.lean` | `S2736QPilotLineBundleLogVolume`; `S2736QPilotLineBundleHweightvol`; `S2752_hweightvol` | **S2752_hweightvol ACTUAL** (olean 139480 B, SHA 2318A7BF...); the Prop `S2736QPilotLineBundleHweightvol` itself is the interface, and its actual consumer/instance is S2752_hweightvol (S2752J = supportIdeal, via S2743 lower bound). NOTE: S2796 is an upper bound for the region bound, NOT an hweightvol input. |
| q-pilot line bundle | `tmp/sheaf/xif/paper/S2735QPilotLineBundleActual.lean` | `qPilotIdeal`; `qPilotLineBundle`; `qPilotLineBundleSource`; `qPilotIdeal_absNorm`; `qPilotFractional_absNorm` | actual (imported by S2736QPilot) |
| **Line-bundle Cor312 bridge** | `tmp/sheaf/xif/paper/S2800LineBundleCor312BridgeActual.lean` | `S2800Carrier`; `S2800LogVolume`; `S2800GlobalData`; `S2800EpsData`; `S2800EpsilonComparison`; `S2800Bridge : Cor312ToABCBridgeInterface` | **olean 83168 B; AXIOMS [propext, Classical.choice, Quot.sound]**; conditional on `S2800GlobalData` + `hg : ∀ eps > 0, S2800EpsData` |
| Source ATheta minimal carrier | `tmp/sheaf/xif/paper/S2736SourceAThetaCarrierActual.lean` | `SourceAThetaCarrier`; `sourceAThetaCarrier`; six-item list theorem | **ACTUAL** (src 17077FD4..., olean 226192 B, SHA 738A607E09E75B118A2D46361F776D9C6A86D661FB3861AF0F2ABC7D2E7295B6; axioms trio) |

Reusable now: `S2717_full_iff_hupper`, `S2717_hupper_of_full`,
`S2717_full_of_hupper`, `arithmeticTupleIQHullCor312ConclusionQ_multi`,
`s1000FinalCor312`, `s1024FinalCor312`, `Cor312PointwiseResidualData`,
`S2736QPilotLineBundleLogVolume`, `S2752_hweightvol` (ACTUAL),
`S2800EpsilonComparison`, `S2800Bridge` (ACTUAL conditional bridge).

Important: `s1000FinalCor312` and `s1024FinalCor312` are **conditional** on
explicit inputs: `S1000FinalInputs`, or `link` + `hlink` + `links` (finite
Step-XI link evidence) and the paper certificate data. They do not prove Cor
3.12 from Theorem 3.11 data alone.

The S2800 bridge is actual but likewise conditional: it consumes
`S2800GlobalData` (carrier, `IQHullLogVolumeInterface`, `logShellPoint`) and
`hg : ∀ eps > 0, S2800EpsData` (hregion + hheight). The bridge construction
itself has axioms trio; the missing part is producing `G` and `hg`, not the
bridge map.

## 2. Exact missing targets

1. **`S2717UpperGap`** — the IUT IV upper estimate
   `thetaHullLogVolume ≤ CThetaPaper · |log q|`.
   `PaperCor312Full` is equivalent to this gap under the actual q-normalization
   (`S2717_full_iff_hupper`); proving `S2717UpperGap` is the single remaining
   analytic target.
2. **Six ATheta geometric/data items** (exact list in
   `sourceThetaObjectMissingData`, from
   `SourceQlThetaObjectActual.lean`):
   - `arithmeticCurveLineBundle`
   - `thetaObjectATheta`
   - `geometricThetaDivisor`
   - `unitComparisonMqMTheta`
   - `muTwoLDeckRootAction`
   - `conjugateSynchronization`
3. **`DThetaRealizationGate` inhabitant** — `SourceH1H2OriginalArrows` states
   the gate but supplies no inhabitant by design; `SourceDThetaConstruction` is
   not currently compiled (no olean).
4. **`SourceImageRealizationLogShell` construction** — the log-shell refinement
   with `hdeg` is only consumed conditionally in S2600/S2601; it is not produced
   from `OriginalInput`.
5. **Full `StepXIContract` construction from source data** — `Cor312Conclusion`
   itself is only `qSigned ≤ thetaSigned`; the contract also contains
   `q_le_target`, `target_le_theta`, and ipl/she/apt evidence. S1000/S1024
   build it only from explicit link/certificate inputs.
6. **(RESOLVED) ATheta carrier actuality** — `S2736SourceAThetaCarrierActual` is
   now ACTUAL (src 17077FD409F29B67082A13272A2CCD17FFF5E3AD56335409170C484B4421EAB8;
   olean 226192 B, SHA 738A607E09E75B118A2D46361F776D9C6A86D661FB3861AF0F2ABC7D2E7295B6;
   axioms trio). It is no longer BROKEN and no longer a missing target. The six
   ATheta geometric/data items remain.

**Resolved, not missing:** the hweightvol inequality is ACTUAL via
`S2752FinalHweightvolActual.S2752_hweightvol` (olean 139480 B,
SHA `2318a7bf88e76069eef503c85c23b2bb0365e92079548be3dc5a6de8d2d0cb61`);
do not list it as a remaining target.

## 3. Dependency / route summary

```text
H1/H2 source constructions (actual)
  + SourceSignQuotientGeometricCore (actual)
  + SourceClauseAssembly units (actual)
        ↓
Step-XI finite certificate / link evidence (explicit inputs)
        ↓
S1000FinalCor312Assembly / S1024FinalCor312 (conditional actual)
        ↓
Cor312Conclusion  (qSigned ≤ thetaSigned)

Theta pilot: paperThetaPilotHull + globalThetaHullInterface (actual)
  + S2718 local log-shell interface (actual)
  + S2600/S2601 source log-shell port (conditional on hdeg)
  + S2752_hweightvol (actual hweightvol; uses S2743 explicit radical bound)
        ↓
S2717ThetaHullLogVolume vs S2717QPilotLogVolume
        ↓
S2717UpperGap  ← **analytic missing target on the S2717 route**
        ↓
PaperCor312Full (equiv to gap under q-normalization)
```

Alternative actual bridge route (S2800):

```text
S2752_hweightvol (actual)
  + S2800GlobalData (carrier + IQHullLogVolumeInterface + logShellPoint)
  + hg : ∀ eps > 0, S2800EpsData (hregion + hheight)
        ↓
S2800EpsilonComparison
        ↓
S2800Bridge : Cor312ToABCBridgeInterface
```

The S2800 route does not prove `S2717UpperGap`; it packages the needed
comparison into the frozen `Cor312ToABCBridgeInterface`. The missing inputs are
`S2800GlobalData` and the epsilon-family `hg`, not the bridge code.

**hdeg audit:** neither `S2717UpperGap` nor `S2800Bridge` depends on the
`SourceImageRealizationLogShell.hdeg` field. The S2810/S2812 no-go therefore does
not block either route; hdeg is needed only by S2600/S2601.  See
`coord/S2812_HDEG_BYPASS.md`.

## 4. Next executable steps

1. Do not rebuild the seven reusable families above.
2. Attack `S2717UpperGap` directly (the only analytic inequality separating
   the target from `S2717_full_of_hupper`). `S2752_hweightvol` already supplies
   the hweightvol side; do not reopen it.
3. For the S2800 route, do not rebuild `S2800Bridge`; construct
   `S2800GlobalData` and the epsilon-family `hg` (hregion/hheight).
4. Construct the six ATheta objects, starting with
   `arithmeticCurveLineBundle` and `thetaObjectATheta`; do not fake a theta
   structure. The minimal `SourceAThetaCarrier` is now ACTUAL and can be used as
   the carrier interface.
5. Compile `SourceDThetaConstruction` or leave it out of actual; the S2736 carrier
   itself no longer needs repair.
6. Produce `DThetaRealizationGate` inhabitant from `OriginalInput`; until then
   H1/H2 is construction-level but not a full Theorem 3.11 output.
7. If claiming a conditional Cor 3.12 assembly, state exactly which
   `S1000FinalInputs` / `link,hlink,links` hypotheses are supplied.

## 5. Status labels used

- **olean present**: build artifact exists; not re-kernel-audited here.
- **source only**: declaration text inspected; no olean, not claimed actual.
- **BROKEN**: attempted compile failed; first errors recorded.
- **target**: `Prop`/structure definition, no inhabitant proved.

No ABC assumption, no fake object, and no new `sorry`/axiom is introduced by this
inventory.
