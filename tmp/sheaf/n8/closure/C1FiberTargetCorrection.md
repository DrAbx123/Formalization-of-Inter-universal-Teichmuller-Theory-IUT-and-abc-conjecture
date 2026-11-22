# C1 fiber target correction (Wave12)

Date 2026-10-24. Based on the proved no-go in
`tmp/sheaf/n8/closure/C1FullUnitValueGroupNoGo.lean`.

## 1. Old target is not satisfiable

Old `C1FiberMonEquivData` (in `C1FiberMonEquivAttempt.lean`) required

```lean
fiberMonEquiv : ∀ n m v,
  (I.primeStripAt n m).Mon v ≃* SourcePlaceValueGroup (e v)
```

For the actual unit monoids this is impossible: `(v.adicCompletion F)ˣ` and
`(w.Completion)ˣ` contain the order-two element `-1`, while the value groups
`Multiplicative ℤ` and `Multiplicative ℝ` are torsion-free.  The no-go file
proves:

- `finiteUnit_not_mulEquiv_valueGroup`;
- `infiniteUnit_not_mulEquiv_valueGroup`;
- `placeUnitMonoid_not_mulEquiv_valueGroup`;
- `no_c1FiberMonEquivData_of_monEquivPlaceUnit` (conditional exact C1 no-go).

Therefore old `C1FiberMonEquivData` is **withdrawn as a satisfiable target**
and retained only as a no-go/historical record.

## 2. Corrected quotient-by-kernel target

The actual true comparison is by the kernel of the unit-to-value map:

- finite place: kernel `(v.adicCompletionIntegers F).units`, quotient is
  `Multiplicative ℤ`;
- infinite place: kernel `(infiniteUnitToValueGroup w).ker` (norm-one units),
  quotient is `Multiplicative ℝ`.

Actual equivalences:

- `finiteUnitQuotientEquivValueGroup`;
- `infiniteUnitQuotientEquiv_actual_closed`;
- assembled as `placeUnitQuotientEquivValueGroup` in `C1PlaceValueGroupActual`.

Corrected Lean target:

```lean
structure C1PlaceQuotientFiberData (F : Type u) [Field F] [NumberField F] where
  quotientEquiv : ∀ P : NumberFieldPlaceIndex (F := F),
    (PlaceUnitMonoid P ⧸ placeUnitKernel P) ≃*
      SourcePlaceValueGroup F P
```

Constructed by `c1PlaceQuotientFiberData F` from the actual finite/infinite
quotient equivalences (zero sorry).

## 3. What remains missing

1. A source-level identification of an arbitrary old
   `I.primeStripAt n m .Mon v` with the actual `PlaceUnitMonoid (e v)`.  Without
   it the corrected data cannot be transferred to arbitrary old `OriginalInput`.
2. A kernel on the old arbitrary `Mon` (or a proof that it is already the
   actual unit monoid); no kernel should be invented as a free field.
3. Full-unit `C1FiberMonEquivData` is not just unproved, it is false on the
   actual unit side; do not reinstate it.

## 4. Consumers

The corrected data is the C1 fiber target for C2/C3/C7 and C10.  Old C1 target
consumers must switch to `C1PlaceQuotientFiberData` plus the missing old-strip
identification above.

## 5. Status

- `C1QuotientFiberData.lean`: exit 0, zero sorry.
- old `C1FiberMonEquivData`: no-go, not satisfiable on actual units.
- no arbitrary equivalence/kernel field added.