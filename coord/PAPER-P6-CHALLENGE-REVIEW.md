# Paper P6 Challenge candidate review (2026-10-25)

## Challenge

```lean
def Challenge : Prop :=
  ∀ S : SourceInitialThetaData l,
    PaperP6Target S
```

where

```lean
def PaperP6Target (S) : Prop :=
  ∃ qLog thetaLog : ℝ,
    qLog = log‖qUnit S‖ ∧
    thetaLog = thetaLogVolume S ∧
    qLog ≤ thetaLog ∧
    (thetaLog : WithTop ℝ) < ⊤
```

## Proof

`paperP6Challenge.challenge_proved` is actual, zero sorry.

## Axiom audit

`#print axioms challenge_proved` => [propext, Classical.choice, Quot.sound]; no sorryAx.

## Input semantics

Input is `SourceInitialThetaData` (IUTI Definition 3.1 clauses A-F formalization), selected as paper-qualified initial Theta-data under GOAL.md.

Used actual fields:
- candidate.arithmetic, candidate.V, candidate.place, candidate.placeToMod
- clauseB.bad_nonempty, clauseB.qParameter at chosen bad F-place
- clauseA/ClauseD exact sequences used only through actual orbicurve/unit structure

Actual q: `qUnit = Units.mk0 qAtPrime`; `qAtPrime` is ClauseB qParameter at the chosen bad place.
Actual Theta: `thetaLogVolume` is log of the actual C6 unit-reference-normalized canonical hull from the same paper source.

## Not yet final acceptance

- independent source semantics review of every SourceInitialThetaData field;
- comparator execution against locked Challenge;
- C9Paper/QPaper/ThetaPaper and ValuesBounded bridge;
- C9BridgeGap remains recorded, not assumed.

target_accepted=false, kernel_closed=false.

## Update 2026-10-25: full target

Additional actual component:
```lean
def PaperValuesBoundedTarget : Prop :=
  ∀ T ⊆ c6Hull,
    Real.log ((c6UnitRefNormalizedData T).toReal) ≤ thetaLogVolume
```
Proved in `PaperValuesBoundedActual.lean` by cases on T-mass and log monotonicity.

Combined target:
```lean
def PaperP6FullTarget : Prop :=
  PaperP6Target S ∧ PaperValuesBoundedTarget S
theorem paperP6FullTarget_actual : PaperP6FullTarget S
```

Snapshots:
- `coord/targets/ChallengeFull.lean` EXIT=0
- `coord/targets/TargetsCheckFull.lean` EXIT=0
- `#print axioms challengeFull_proved => [propext, Classical.choice, Quot.sound]`
- serial dependency-chain compile all EXIT=0.

Comparator still unavailable; source semantics/independent review still pending. target_accepted=false.
