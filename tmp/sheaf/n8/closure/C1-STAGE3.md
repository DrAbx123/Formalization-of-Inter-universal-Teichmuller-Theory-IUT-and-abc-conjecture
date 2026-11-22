# S3-C1 STAGE 3 — actual SourceInputBinding (strict closure attempt)

Target: construct `SourceInputBinding I` with `sourceInputBinding_nonempty`
**zero sorry**, using actual donors for `placeEquiv`, `selected`,
`selected_realization`, `fiberMonEquiv`.

Verdict: **the zero-sorry target is not reachable in the current tree.**  The
four fields have no production donor.  This record gives the exact missing
production declarations; no arbitrary equivalence, arbitrary selected place,
axiom, or named sorry is used in place of them.

## 1. File delivered

`tmp/sheaf/n8/closure/C1Actual.lean` — data-conditional construction only:

```lean
structure C1ActualData (I : OriginalInput l V) where
  placeEquiv : V ≃ NumberFieldPlaceIndex (F := I.initial.arithmetic.Fmod)
  selected : V
  selected_realization : I.SourceImageRealization selected
  fiberMonEquiv : ∀ (n m : Int) (v : V),
    (I.primeStripAt n m).Mon v ≃*
      SourcePlaceValueGroup (F := I.initial.arithmetic.Fmod) (placeEquiv v)

def C1ActualData.toPlaceRealization (D) : SourcePlaceRealization I
def sourceInputBindingOfActual (I) (D : C1ActualData I) : SourceInputBinding I
theorem sourceInputBinding_nonempty_of_actual (I) (D : C1ActualData I) :
  Nonempty (SourceInputBinding I)
```

This is honest: it asserts a `SourceInputBinding` only after the four actual
data are supplied.  It does not assert `Nonempty (C1ActualData I)`.

## 2. Exact missing production declarations

### C1-a: place equivalence
```lean
def sourcePlaceIndexEquiv (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    V ≃ NumberFieldPlaceIndex (F := I.initial.arithmetic.Fmod)
```
Reason missing: `V` is an arbitrary field of `OriginalInput`; no declaration
relates `V` to the finite/infinite places of `I.initial.arithmetic.Fmod`.
This must be added as a production-level source input/field, not chosen.

### C1-d1: selected place
```lean
def sourceSelectedPlace (I : OriginalInput.{ua, uv, upi, umon, ui} l V) : V
```
Reason missing: `OriginalInput` has no `Nonempty V`; `V` may be empty.  A
selected finite place is a source construction, not a free `Classical.choice`
on an arbitrary type.

### C1-d2: selected image realization
```lean
def sourceSelectedImageRealization (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    I.SourceImageRealization (sourceSelectedPlace I)
```
Reason missing: `SourceImageRealization` is a structure with actual fields
`posRealAction : Multiplicative Real →* I.ValueMonoidAt 0 0 v` and
`degree_of_q`; the current tree has no constructor or `Nonempty` theorem.

### C1-b: prime-strip fiber comparison
```lean
def sourceFiberMonEquiv (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (e : V ≃ NumberFieldPlaceIndex (F := I.initial.arithmetic.Fmod)) :
    ∀ (n m : Int) (v : V),
      (I.primeStripAt n m).Mon v ≃*
        SourcePlaceValueGroup (F := I.initial.arithmetic.Fmod) (e v)
```
Reason missing: `numberFieldPrimeStrip` is a concrete strip over
`NumberFieldPlaceIndex`, while `I.primeStripAt n m` is an arbitrary
`FPrimeStrip V`; no theorem compares their `Mon` fibers.

## 3. Dependency/consumer audit

- `SourcePlaceValueGroup` is the actual donor family: finite branch
  `finitePlaceValueGroup = Multiplicative ℤ`; infinite branch
  `archimedeanValueGroup = Multiplicative ℝ` (Example36PrimeStripBridge).
- Consumers C2/C3/C7 require actual `selected`/`R`/`fiberMonEquiv`; the
  conditional `C1ActualData` exposes them explicitly, so consumers can be
  written against `D : C1ActualData I` without inventing data.
- `SourceInputBinding` itself still has only the `place` field; no free
  Frobenioid or arbitrary equivalence was added.

## 4. Validation

- `lake env lean -j1 -R D:/lean tmp/sheaf/n8/closure/C1Actual.lean` → **EXIT 0**
- actual sorry = **0**
- named axiom = 0
- no production edit.

## 5. Status

- `sourceInputBinding_nonempty` zero-sorry: **not achieved** (exact missing
  production declarations above).
- conditional constructor: **achieved, zero sorry**.
- Next action: add the four production declarations (or a production-level
  `C1ActualData` provider) and then replace the conditional argument; do not
  use `Classical.choice`/arbitrary `Equiv`/`True` to close the target.
