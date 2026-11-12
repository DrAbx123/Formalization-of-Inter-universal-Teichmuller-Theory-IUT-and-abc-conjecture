# S1283: ConcreteC3RootTensorActual / RootCompletion universe blocker

Date: 2026-10-30.  Read: `coord/reports/s1274-c3-roots-kummer-audit.md`,
`ConcreteC3RootTensorActual.lean`, `ConcreteC3RootCompletionActual.lean`,
`ConcreteC3DonorActual.lean`, `NatRootSystem.lean`,
`FinitePlaceCommonPrimeCompletion.lean`.

## Result: exact design blocker in the imported donor

The two requested files cannot compile to olean in isolation, and the errors
are not local to them: both import `ConcreteC3DonorActual`, which itself does
not compile.  `ConcreteC3DonorActual` is outside the two-file write scope
(and is not tensorUnit/HDD/Ind), so I did not edit it.

`lake env lean ConcreteC3DonorActual.lean` fails at:

```text
line 71: NatRootSystem (concreteQUnit I place)
line 76: ConcreteRootSystemCarrier applied to I
line 81: CyclotomicTower (CommonPrimeCompletion ... I.initial.arithmetic.Fmod)
line 85/90/94: same carrier/universe failures
line 110: ConcreteC3ActualFields I
```

## Root cause

The donor declares

```text
variable (I : OriginalInput.{ua, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
```

so `I.initial.arithmetic.Fmod : Type ua`.  But the concrete carriers are
declared as `Type` (universe 0):

```text
def ConcreteRootSystemCarrier : Type := NatRootSystem (concreteQUnit I place)
def ConcreteKummerClassCarrier : Type := CyclotomicTower (CommonPrimeCompletion ...)
def ConcreteRootChangeCarrier : Type := CyclotomicTower (CommonPrimeCompletion ...)
```

and `NatRootSystem`/`CommonPrimeCompletion`/`CyclotomicTower` terms are inferred
at universe 0 in those ascriptions.  This produces exactly the observed
mismatches:

```text
concreteQUnit : Units.{ua} (CommonPrimeCompletion place)
expected by NatRootSystem ascription: Units.{0} ?m
I.initial.arithmetic.Fmod : Type ua
expected by CommonPrimeCompletion application: Type 0
```

The later `ConcreteC3ActualFields I`/`Function expected` errors are cascades
from the failed carrier definitions, not independent errors.

## Minimal fix (all in the donor, one universe choice)

Use universe 0 for the concrete C3 source:

```text
variable (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
```

in `ConcreteC3DonorActual.lean` and the same in
`ConcreteC3RootTensorActual.lean` / `ConcreteC3RootCompletionActual.lean`,
then remove/relax the `: Type` ascriptions on
`ConcreteRootSystemCarrier`, `ConcreteKummerClassCarrier`,
`ConcreteRootChangeCarrier` (or make them `Type 0` explicitly).  With
`Fmod : Type 0`, `CommonPrimeCompletion place : Type 0`, `Units.{0}` and
`NatRootSystem` line up; the q/root objects and their equality fields are
unchanged.

An alternative is to make every carrier ascription universe-polymorphic
(`Type ua`) and ensure `CommonPrimeCompletion`/`NatRootSystem` are used at
that universe.  This is a larger change and must be checked across
`ConcreteC3DonorCompletionActual`, `ConcreteC3RootTensorActual`, and
`ConcreteC3RootCompletionActual`.

## Why the requested two files cannot be fixed alone

* They import `ConcreteC3DonorActual`; Lean requires its olean, and it does
  not exist because the donor fails elaboration.
* Re-declaring the donor's q unit/fields inside the root files would duplicate
  the source object and change the object dependency, contrary to the
  instruction not to change objects.
* The errors in the root files themselves, insofar as they are visible, are
  the same `OriginalInput.{ua,...}` vs `Type` ascription pattern; fixing only
  those two would still leave the import failure.

## Status

```text
ConcreteC3RootTensorActual        no olean (blocked at donor import)
ConcreteC3RootCompletionActual    no olean (blocked at root tensor)
ConcreteC3DonorActual             no olean (universe design error)
completion root fabricated        no
object changed                    no
files edited                      none
first exact compiler blocker      ConcreteC3DonorActual line 71/81 universe
                                  (I : OriginalInput.{ua,...} vs Type)
```

To make these two compile EXIT=0, the donor universe choice must be changed
(or the concrete C3 universe-0 restriction adopted consistently across the
three files).  I did not modify `ConcreteC3DonorActual` because it is outside
the stated two-file scope; if the Lead authorizes that one-line universe change,
the root tensor/completion files can then be adjusted consistently.
