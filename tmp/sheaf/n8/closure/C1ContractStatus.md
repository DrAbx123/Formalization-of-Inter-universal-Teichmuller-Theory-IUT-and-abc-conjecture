# C1 contract status — P6BridgeDonors / native contract datum

Task: Wave3 actual-construction attempt for current paper route.
Files: `tmp/sheaf/n8/closure/C1ContractAttempt.lean` (new), this record.
No old-layer objects recreated; no production edit.

## 1. Target types

```lean
abbrev P6SL l := N8NativeInput l
abbrev P6OldOriginalInput X := OriginalInput l (NativePlaces X.S)
structure P6BridgeDonors X where
  inputDonors : NativeOriginalInputDonors X
  bindingDonors : NativePlaceBindingDonors X
    (nativeOriginalInputOfDonors X inputDonors)
def P6BridgeDonorsExist X := Nonempty (P6BridgeDonors X)
```

## 2. Actual constructible part

`P6ActualPartial X` is constructed with zero sorry:
- `placeEquiv : NativePlaces X.S ≃ NumberFieldPlaceIndex (F := X.S.arithmetic.Fmod)`
  from `nativePlaceIndexEquiv`;
- `selected := badPlace X`;
- `selected_mem` and `selected_comap` from NativeC1.

This is the maximal actual place/selected data.  It does **not** give the old
`OriginalInput`, `SourceImageRealization selected`, or the fiber comparison.

## 3. Exact missing production objects

### D1: contract datum
```lean
NativeContractDatumExists X : Prop :=
  ∃ initial : SourceDefinition31Data.{0} l,
    initial.arithmetic = X.S.arithmetic
```
No native -> `SourceDefinition31Data` constructor:
- `StageConstructionTrace.toSource` needs a `StageConstructionTrace`, which
  requires `SourcePlacePartition` with `Fintype Bad`, selected/bad Nat labels,
  and reduction/torsion/orbicurve/sections/cusp clauses; native data supplies
  only the partial `NativeContractPartitionFragment` (bad inclusion +
  selectedNonempty), not the Fintype/labels or later clauses.
- `sourceHaarActualOriginalInput` requires an already supplied
  `SourceDefinition31Data`; it is not a constructor from native data.
Thus D1 remains a named obligation.

### D2: old place/R/fiber donor
```lean
NativeOldBindingDonorsExist X : Prop :=
  ∃ D : NativeOriginalInputDonors X,
    Nonempty (NativePlaceBindingDonors X (nativeOriginalInputOfDonors X D))
```
`NativePlaceBindingDonors` needs:
- a placeEquiv (available from NativeC1),
- a selected place (available),
- `SourceImageRealization selected` (not constructed),
- `fiberMonEquiv` (not constructed).
This is a named obligation; no arbitrary R/fiber is inserted.

## 4. Conditional exact no-go

Proved:
```lean
theorem no_p6BridgeDonors_of_empty_contract
    (X : N8NativeInput l) (h : IsEmpty (SourceDefinition31Data.{0} l)) :
    IsEmpty (P6BridgeDonors X)
```
If the contract type is empty, no donor package exists.  This is conditional;
no unconditional no-go is asserted because an inhabitant of
`SourceDefinition31Data` is not known to be impossible.

## 5. Compile status

- `C1ContractAttempt.lean`: `lake env lean -j1 -R D:/lean` exit 0; one
  theorem-level named sorry (`p6BridgeDonorsExist_attempt`).
- Reused named obligations from C1BridgeProof/P6BridgeActual: contract datum,
  old R/fiber, full donor attempt.
- No old layer/L0.2/L0.4 objects touched.

## 6. Next blocker

The next exact production object is a native -> `SourceDefinition31Data`
constructor.  It must supply at least the missing partition Fintype/labels and
the reduction/torsion/orbicurve/sections/cusp clauses; adding it as a free
field or arbitrary constant is rejected.