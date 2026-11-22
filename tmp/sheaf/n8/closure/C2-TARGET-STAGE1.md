# C2 native target types - stage 1

- Task: Round 42, C2 target design.
- Owner: logdescent.
- Lean: tmp/sheaf/n8/closure/C2Targets.lean.
- Compile: lake env lean -j1 -R D:/lean -> EXIT=0.
- Status: target types only; action/Kummer/archimedean are named sorry, K1K2 is an actual constructor. No full C2 closure claimed.

## Native datum

`nativeDatum : Unit -> SourceLogShellDatum := fun _ => C2Native.nativeLocalShell X`.

## 1. Native G_v action target

```lean
def nativeGvActionTarget
    (S : SourceLogShellXMuChainSupply (nativeDatum X) (nativeDatum X) (nativeDatum X)) :
    Prop :=
  Nonempty (SourceLogShellXMuChainActionCompatibility
    (nativeDatum X) (nativeDatum X) (nativeDatum X)
    (Equiv.Perm (NativePlaces X.S)) S)

theorem nativeGvActionTarget_obligation ... : nativeGvActionTarget X S := by sorry
```

Exact reuse: `SourceLogShellXMuChainActionCompatibility` and
`SourceLogShellXMuChainSupply`.  The chain supply `S` is an explicit parameter
because production only supplies it conditionally; `Equiv.Perm (NativePlaces X.S)`
is the actual native place-permutation group (no free Type).

Missing production declaration: there is no native C1-indexed action/descent
type constructed from `N8NativeInput`; only the conditional compatibility
structure exists.

## 2. Native Kummer/root-change target

```lean
def nativeKummerTarget : Prop := (C2Native.nativeLocalShell X).codomainKummerContained
theorem nativeKummerTarget_obligation : nativeKummerTarget X := by sorry
```

Exact reuse: `SourceLogShellDatum.codomainKummerContained`.
Missing production declaration: no native Kummer/root-change map type exists;
production has only the containment Prop and conditional chain supplies.

## 3. Native multi-place K1/K2 target

```lean
def nativeK1K2Target : Prop :=
  forall (p : Nat) [Fact p.Prime]
    (place : FinitePlaceAtPrime (X.S.arithmetic.Fmod) p)
    (u : principalUnits (K := SourceCompletion place)),
      completionIsometryEquiv place (principalUnitLog (K := SourceCompletion place) u) =
        principalUnitLog (K := TargetCompletion place)
          (ABCBridge.LogKummerK1K2.principalUnitMap place u)

theorem nativeK1K2Target_actual : nativeK1K2Target X := ... -- actual constructor
```

Exact reuse: the production consumer
`ABCBridge.LogKummerK1K2Consumer.logKummerK1K2_consumer` proves the target for
every finite place.  Actual constructor, no sorry.

## 4. Native archimedean target

```lean
def nativeArchimedeanTarget : Prop :=
  Nonempty { v : NativePlaces X.S //
    NumberFieldPlace.IsInfinite
      (NumberFieldPlace.comap (k := X.S.arithmetic.Fmod) v.1) }
theorem nativeArchimedeanTarget_obligation : nativeArchimedeanTarget X := by sorry
```

Exact reuse: `NativePlaces`, `NumberFieldPlace.IsInfinite`, `NumberFieldPlace.comap`.
Missing production declaration: no actual native archimedean source/log-shell
object exists; the target only records the selected infinite place that any
archimedean branch must start from.

## No free placeholders

No `Type`-valued free field, no `True` target, and no local arbitrary structure
is used.  The action target reuses the conditional production type; K1K2 is
actually proved; Kummer and archimedean targets are actual Lean propositions
with named sorry because the production objects are missing.

## Status

- statement_compiles: true (EXIT=0).
- proof_body_checked: K1K2 actual constructor; action/Kummer/archimedean are
  named target obligations, not proofs.
- target_accepted: target types only; full C2 remains partial.