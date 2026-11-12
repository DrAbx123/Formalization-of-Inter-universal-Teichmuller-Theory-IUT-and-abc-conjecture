# S1339: D9 compatibility from the actual D3/D4 and D7/D8 data

Date: 2026-10-30. New file + report; no D5-D8 clause fabricated.

## 1. Sources read

- `S1280SourceDefinition31Actual`: actual D3/D4 prefix: arithmetic, actual
  Gaussian selection, bad place, reduction cards and reduction clause;
- `S1320SectionsCuspActual`: actual D7a place-section prefix; D7b exact
  local-group supply; D8 cusp exact first field `epsilon`;
- `S1312D7LocalGroupActual`: D7b exact first field; actual bad local groups;
- `SourceDefinition31ArithmeticCompatibilitySlots`: the concrete D9 slot
  statements and their actual proof constructors.

## 2. D9 five slots

### (1) reduction

Concrete statement:

```lean
ArithmeticReductionCompatibility P C Q
```

with `P = S1280Selection`, `C = S1280ReductionCards`, and
`Q : BadPlaceQParameterCards P`.

Actual: `P`, `C`, `S1280ReductionClause`, q-proxy facts.

Exact first field: `BadPlaceQParameterCards (S1280Selection l)`.

Moreover `S1280_clauseC_refuted_at_five` proves this field is **impossible**
at `l = 5` for the actual S1280 selection (residue characteristic 5 is not
coprime to l=5).  So the reduction slot cannot be constructed from the
current actual Gaussian data at l=5.

### (2) torsion

Concrete statement:

```lean
ArithmeticTorsionCompatibility T
```

where `T : SourceTorsionClause l`.  Exact first field: `SourceTorsionClause`
itself; its first mathematical field is the rank-two basis of the actual
l-torsion (`S1298TorsionBasisType`), not supplied.

Conditional actual: if a `T` is supplied, `arithmeticTorsionCompatibility_of_clause`
proves the D9 torsion pair.  No D5 is fabricated here.

### (3) sections — ACTUAL

Concrete statement:

```lean
ArithmeticSectionCompatibility (S1280Selection l)
```

This depends only on the actual `SourcePlaceSelection`, not on D7b.  The
proof is actual:

```lean
theorem S1339D9Sections_proved :
    S1339D9SectionsProp (l := l) :=
  arithmeticSectionCompatibility_canonical (S1280Selection l)
```

This is one of the five D9 `(Prop, proof)` pairs actually constructed
(`S1339D9CompatibilityActual.lean`, EXIT=0).

### (4) orbicurve

Exact first field: the actual K-core orbicurve

```lean
X : Iut.HyperbolicOrbicurve (S1280Arithmetic l).K
```

with the K-core identification of Definition 3.1(d).  No compiled supplier
constructs it; the parked card is
`IUT-I.definition-3.1-D9-orbicurve-slot`.  S1320's sections/cusp data do not
supply this object.

### (5) cusp

Concrete global-origin statement:

```lean
ArithmeticCuspOriginCompatibility O
```

with `O : TorsionQuotientBoundaryOrigin l (S1280Arithmetic l) X`.

Actual: S1320 supplies the actual cusp point and the D8 cusp prefix, and
`ArithmeticCuspOriginCompatibility O` is provable **if** `O` is supplied.

Exact first field: `TorsionQuotientBoundaryOrigin` over an actual `X`; the
bad-place local generator half remains the parked card
`IUT-I.definition-3.1-D9-cusp-local-generator`.

## 3. New Lean file

`S1339D9CompatibilityActual.lean` (EXIT=0, no sorry):

- `S1339D9SectionsProp := ArithmeticSectionCompatibility (S1280Selection l)`;
- `S1339D9Sections_proved` actual;
- exact first-field aliases:
  `S1339D9ReductionFirstField`, `S1339D9TorsionFirstField`,
  `S1339D9OrbicurveFirstField`, `S1339D9CuspFirstField`;
- `S1339D9ReductionFirstField_impossible_at_five`.

## 4. Conclusion

- **Actual D9 pair constructed: sections** (1 of 5).
- **Exact first fields:**
  1. reduction: `BadPlaceQParameterCards` (impossible at l=5 for S1280);
  2. torsion: `SourceTorsionClause` (rank-two basis missing);
  4. orbicurve: actual K-core `HyperbolicOrbicurve` (no supplier);
  5. cusp: `TorsionQuotientBoundaryOrigin` (local generator parked).
- D5-D8 were not fabricated; S1320/S1312/S1298 exact gaps respected.
- EXIT=0.
