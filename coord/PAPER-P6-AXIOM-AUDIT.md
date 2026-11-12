# Paper P6 full target — independent axiom/definition audit

Date: 2026-10-25. Auditor: independent audit pass (no Lean edits, no target changes).
Scope: `ChallengeFull`/`TargetsCheckFull` snapshots and `PaperP6FullTarget` proof chain.

## Verdict

- No `sorryAx` occurs in the target proof chain.
- No user `axiom`, `unsafe`, `native_decide`, or `admit` occurs in the target chain.
- The kernel axioms reported by `#print axioms` are only
  `[propext, Classical.choice, Quot.sound]`.
- No semantic circular dependency was found. The target proof uses component theorems; none of them refers back to `PaperP6FullTarget`.
- The only non-constructive choices are `Classical.choice`/`Classical.choose` used to select an actual bad place, its lift, the ClauseB q-parameter, and the actual C6 IQ interface/hull. These are choices from proved existences, not arbitrary data.
- Audit result: **clean for the candidate target**, but this is not `target_accepted` (see limitations).

## Evidence: snapshots

| file | SHA256 | compile result |
|---|---|---|
| `coord/targets/ChallengeFull.lean` | `3A069E6F42CDB6559DE06C929E2A71995F06EB06A8F16964DED2FD00EC47F011` | EXIT 0 |
| `coord/targets/TargetsCheckFull.lean` | `AEE822D909BA2FA4D8B2392D29AB21E475F6823776B9CE7AE27695544DF4E6EC` | EXIT 0 |
| `coord/targets/AxiomAudit.lean` | `5D62360773FE7874B72B5EFA8D753532AE691F7EE270BF334C3838146C9906B8` | EXIT 0 |

Commands:

```text
lake env lean -j1 -R D:/lean coord/targets/ChallengeFull.lean
lake env lean -j1 -R D:/lean coord/targets/TargetsCheckFull.lean
lake env lean -j1 -R D:/lean coord/targets/AxiomAudit.lean
```

`ChallengeFull` and `TargetsCheckFull` define the same frozen proposition:

```lean
def ChallengeFull : Prop :=
  ∀ S : SourceInitialThetaData l,
    LeanFormal.IUT.N8Closure.PaperP6FullTarget.PaperP6FullTarget S
```

## Evidence: axiom output

`AxiomAudit.lean` output (serial compile):

```text
'LeanFormal.IUT.N8Closure.PaperP6FullTarget.paperP6FullTarget_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'LeanFormal.IUT.N8Closure.PaperP6FullTarget.paperValuesBoundedTarget_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'LeanFormal.IUT.N8Closure.PaperP6Target2.paperP6Target_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

`TargetsCheckFull.lean` output:

```text
'LeanFormal.IUT.N8Closure.TargetsCheckFull.challengeFull_proved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

No `sorryAx` appears in either output.

## Target elaborated

`#print` of the frozen full target:

```lean
def LeanFormal.IUT.N8Closure.PaperP6FullTarget.PaperP6FullTarget :
  {l : PrimeGeFive} →
  (S : SourceInitialThetaData l) → Prop :=
fun {l} S =>
  PaperP6Target2.PaperP6Target S ∧
  PaperP6FullTarget.PaperValuesBoundedTarget S
```

Unfolded components:

```lean
PaperP6Target S :=
  ∃ qLog thetaLog : ℝ,
    qLog = Real.log ‖(qUnit S : PaperKf S)‖ ∧
    thetaLog = thetaLogVolume S ∧
    qLog ≤ thetaLog ∧
    (thetaLog : WithTop ℝ) < ⊤

PaperValuesBoundedTarget S :=
  ∀ T : Set (Block S),
    T ⊆ c6Hull S →
    Real.log ((c6UnitRefNormalizedData S T).toReal) ≤ thetaLogVolume S
```

## Definition-chain audit

### qUnit / q side

| definition | definition source | audit note |
|---|---|---|
| `qUnit` | `C7MassFormulaZeroSorry.qUnit` | `Units.mk0 qAtPrime` with actual nonzero proof |
| `qAtPrime` | `C7QPilotRegionActual.qAtPrime` | `q S` |
| `q` | `C7QPilotRegionActual.q` | `(qCandidate S).q` |
| `qCandidate` | `ClauseB.qParameter (pF S) (pF_bad S)` | actual source field, not an assumption |
| `p0` | `Classical.choose S.clauseB.bad_nonempty` | choice from an actual nonempty bad set |
| `pF` | `Classical.choose (comap_surjective ... (p0 S))` | choice from actual surjectivity |
| `e`, `eAlgPi`, `ePaperKf` | one-factor tensor equivalences | constructed; `ePaperKf_apply_eq_e` is `rfl` |

No `Classical.arbitrary`, no free q value, and no arbitrary unit is used.

### Theta side

| definition | definition source | audit note |
|---|---|---|
| `thetaLogVolume` | `C7MassFormulaZeroSorry.thetaLogVolume` | `Real.log (c6UnitRefNormalizedData c6Hull).toReal` |
| `c6UnitRefNormalizedData` | `C6UnitRefNormalized` | `(μ unitRef)⁻¹ • raw.mu`; actual unit-reference normalization |
| `unitRef` | `C6UnitRefNormalized.unitRef` | `arithmeticTupleCanonicalUnitReference` |
| `c6Hull` | `C6NormalizedTensorHaar.c6Hull` | actual C6 IQ interface hull |
| `rawData` | `c6TensorActualData` | actual tensor block, `borel` + `Measure.addHaar` |

`C6TensorActualData`/`C6ActualIQData.actual` use the actual arithmetic canonical interface; no arbitrary measure or shell is substituted.  The interface is obtained by `Classical.choose` from `exists_arithmeticTupleIQHullLogVolumeInterface`, whose characteristic properties are restored by `Classical.choose_spec` (hull/unit/log-volume identities).

### ValuesBounded side

| definition/theorem | source | note |
|---|---|---|
| `PaperValuesBoundedTarget` | `PaperP6FullTarget` | universal over all `T ⊆ c6Hull` |
| `paperValuesBoundedTarget_actual` | `PaperP6FullTarget` | uses `paperValueLog_le_theta_of_subset` |
| `paperValueLog_le_theta_of_subset` | `PaperValuesBoundedActual` | cases on zero/⊤ mass; actual measure and log monotonicity |

No chosen finite Values set and no arbitrary Real is used.

## Circularity check

- Import direction is acyclic (`PaperP6FullTarget` imports `PaperP6Target`, `PaperValuesBoundedActual`, `C6UnitRefNormalized`; none imports `PaperP6FullTarget`).
- Proof direction:
  - `paperP6FullTarget_actual` uses `paperP6Target_actual` and `paperValuesBoundedTarget_actual`;
  - `paperP6Target_actual` uses `paper_log_norm_le_thetaLogVolume` and `thetaLogVolume_lt_top`;
  - `paperValuesBoundedTarget_actual` uses `paperValueLog_le_theta_of_subset`;
  - none of these calls `paperP6FullTarget_actual` or `ChallengeFull`.
- No target statement is stored as a hypothesis and no target theorem is used to prove itself.

## Unreachable named sorries in imported modules

The module closure contains named sorries that are not on the target proof path:

| file | line | declaration | status |
|---|---|---|---|
| `C6UnitRefNormalized.lean` | 111, 114 | `unitRefImageTransport_obligation`, `qPilotUnitRefMassFormula_obligation` | not referenced by the target theorem |
| `C7QPilotMassActual.lean` | 71, 74 | `qPaperEqLogNorm_obligation`, `qPaperPerDegreeEqLogNorm_obligation` | not referenced by the target theorem |
| `C7QPilotMassTransport.lean` | 77, 80, 85, 89 | transport obligations | not referenced by the target theorem |

Evidence they are not on the proof path: the `#print axioms` outputs above contain no `sorryAx`.  This is an axiom-level check, not a claim that those unrelated modules are sorry-free.

## Limitations / non-claims

- This audit verifies the **candidate target** `ChallengeFull`; it does not establish the full paper Corollary 3.11/3.12 conclusion.
- `PaperValuesBoundedTarget` is a hull-only universal log-volume bound, not the actual C9Paper Values/ellOut provenance bridge; C9BridgeGap remains a separate gap.
- `SourceInitialThetaData` is used as the paper-qualified input; its clause semantics have only a self-review (`PAPER-P6-SOURCE-REVIEW.md`), not an independent source review.
- Comparator execution against the locked target was not available in this audit.
- `target_accepted = false`, `kernel_closed` for the candidate target = true modulo the above semantic caveats.

## Hash table of audited proof-chain files

| file | SHA256 |
|---|---|
| `tmp/sheaf/n8/closure/PaperP6FullTarget.lean` | `D79DAAAF389EA3D3BECF72D0E901E5E249F95DAA3A9CBEE0575986DBBD16ED49` |
| `tmp/sheaf/n8/closure/PaperP6Target.lean` | `D9981A009EF5398C4AE303AE29CCA807E927F8033BC30E8AEC9D7925B32D59AE` |
| `tmp/sheaf/n8/closure/PaperP6Final.lean` | `2F2B8884E72E25CDC9758E6D0762CAE3293C954520109448F8FA6E24838D9088` |
| `tmp/sheaf/n8/closure/PaperP6ComparisonActual.lean` | `7F207385ACE579442EAFEA2B0EAA4815EA6F87C009248522CD713511D2B4A440` |
| `tmp/sheaf/n8/closure/PaperValuesBoundedActual.lean` | `D507DD22BCBA45B4CC88F490B2AF8775C048B4FF22121117051C06CD84397CA1` |
| `tmp/sheaf/n8/closure/C7MassFormulaZeroSorry.lean` | `512164087CD748CF145C0ED730310F67B00405A7C5E0D90655E2EFCA8D09EE64` |
| `tmp/sheaf/n8/closure/C6UnitRefNormalized.lean` | `8DE672345F76D3D0BF4816DD7D63D6B04FF3B2B3C739AF0872379BA23F705779` |
| `tmp/sheaf/n8/closure/C6NormalizedTensorHaar.lean` | `EB6A70AE65D45FD36A26BC2E14400DA9CBB369C7FD90C077E0E1C233A91BC175` |
| `tmp/sheaf/n8/closure/C7QPilotRegionActual.lean` | `C54FD9103BCFA34C26A7E29B9372798888BE615640AC38095587D7974572734F` |

## Conclusion

The candidate `PaperP6FullTarget` proof is **axiom-clean at the kernel level except for the standard `propext`, `Classical.choice`, `Quot.sound`**. No `sorryAx`, no arbitrary conclusion, and no circular dependency was found. The remaining barriers are semantic/scope barriers (C9Paper provenance, full source semantics, comparator), not kernel axioms.

## Correction 2026-10-25 (Lead)

`PaperP6ToC9.C9BridgeGap` is false as originally defined; `c9BridgeGap_false`
proves its negation. The real C9 gap is provenance equalities of C9Paper's
QPaper/ThetaPaper, not existence of a volume bridge record. Target audit
conclusions are unchanged.
