# S1214: PrimeStripC3PlaceComparison assembly audit

Date: 2026-10-30.  Read: `S1208ConcreteC3PlaceActual.lean`,
`S1203-capsule-tensor-audit.md`, `PrimeStripLogShellActual.lean`,
`tmp/sheaf/n8/closure/SourcePilotRegion.lean`,
`C3ActualThetaPacketWitnessConstruction.actualC3OfDonors`,
`ConcreteC3DonorActual` / `ConcreteC3DonorCompletionActual`.

## 1. What is already actual

`S1208ConcreteC3PlaceActual` constructs, for
`V = FinitePrimePlace 2 7`,

```text
concreteC3IndexEquiv : FinitePrimePlace 2 7 ≃ FinitePrimePlace 2 7
  := Equiv.refl
concreteC3StripPlace I place : FinitePrimePlace 2 7 →
  FinitePlaceAtPrime I.initial.arithmetic.Fmod p
  := fun _ => place
```

with `concreteC3IndexPlace_actual` (bijective index, constant strip place).
These are exactly the two non-C3 fields of a candidate
`PrimeStripC3PlaceComparison`.

## 2. Why assembly still stops

`PrimeStripC3PlaceComparison (V := FinitePrimePlace 2 7) (I := I) C3` requires:

```text
indexEquiv : FinitePrimePlace 2 7 ≃ C3.tensorIndex
stripPlace : FinitePrimePlace 2 7 →
  FinitePlaceAtPrime I.initial.arithmetic.Fmod C3.p
stripPlace_eq : ∀ v,
  stripPlace v = C3.tensorPlaces (indexEquiv v) (C3.tensorTuple (indexEquiv v))
```

`C3 : SourcePilotRegionData` has `tensorIndex : Type v` as an arbitrary field,
not a definitional `FinitePrimePlace 2 7`.  To use `concreteC3IndexEquiv` one
needs an actual equality `C3.tensorIndex = FinitePrimePlace 2 7` (a type
equality) and matching `tensorPlaces`; neither is produced by the current
actual data.

`actualC3OfDonors` only turns a supplied `SourcePilotRegionDonors` into a C3;
the donors are not actual.  In particular `SourcePilotRegionData` requires:

```text
roots : NatRootSystem qUnit
roots' : NatRootSystem qUnit
kummerClass : CyclotomicTower (CommonPrimeCompletion ...)
rootChange : CyclotomicTower (CommonPrimeCompletion ...)
rootChange_eq : rootChange = KummerClass.rootSystemDiff roots roots'
tensorIndex : Type v
tensorPlaceIndex : tensorIndex → Type w
tensorPlaces : ...
tensorTuple : ...
tensorUnit : (ArithmeticTensorTupleBlock ...)ˣ
tensorLanding : CommonPrimeCompletion ... → ArithmeticTensorTupleBlock ...
tensorLanding_q : tensorLanding q.q = tensorUnit
```

`ConcreteC3DonorActual`/`ConcreteC3DonorCompletionActual` record the exact
obstructions: `ConcreteRootSystemObstruction`, `ConcreteKummerClassObstruction`,
`ConcreteRootChangeObstruction`, `ConcreteTensorLandingObstruction`
(`ConcreteTensorLandingTarget` has `landing` and `landing_q`).  No production
inhabitant exists.

## 3. Exact first field

The first missing object is **not** `indexEquiv` or `stripPlace`: those are
actual in S1208.  It is the C3 donor field that prevents any C3 object with the
concrete tensor index:

```text
SourcePilotRegionDonors.roots / roots' / kummerClass / rootChange / tensorLanding
```

and in particular the source tensor landing:

```text
ConcreteTensorLandingTarget
  landing : CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place →
    ConcreteTensorBlock
  landing_q : landing q = concreteTensorUnit
```

or, invariantly, the exact `SourcePilotRegionData.tensorLanding` /
`tensorLanding_q` pair for the chosen concrete place.  Without it
`actualC3OfDonors` produces no C3, so there is no `C3.tensorIndex` to identify
with `FinitePrimePlace 2 7` and no `tensorPlaces` equality.

## 4. Concrete assembly status

```text
V = FinitePrimePlace 2 7                       yes
indexEquiv as Equiv.refl                      actual (S1208)
stripPlace constant supplied place             actual (S1208)
C3 : SourcePilotRegionData                     not actual
C3.tensorIndex = FinitePrimePlace 2 7          not available
C3.tensorPlaces equality                       not available
PrimeStripC3PlaceComparison                    not assemblable
first exact field                               C3 donor tensorLanding
                                                (plus roots/Kummer)
weak wrapper / Nonempty gate                    none written
```

## 5. What would close it

Construct one of:

1. the actual `SourcePilotRegionDonors` for the concrete place, including
   `roots`, `roots'`, `kummerClass`, `rootChange`, `tensorLanding`, and the
   required equations; then `actualC3OfDonors` gives C3, and S1208's
   `indexEquiv`/`stripPlace` can be compared once `C3.tensorIndex` is the
   concrete index; or
2. a direct actual C3 object with `tensorIndex` definitionally
   `FinitePrimePlace 2 7` and `tensorPlaces` constant; then assemble the
   comparison from S1208's fields by rfl.

Neither is supplied by the current tree.  No Lean wrapper is written; the
package stops at this first donor field.
