# S1355: D9 torsion/cusp pairs from supplied D5/D8 data

Date: 2026-10-30. New Lean file; no D5/D8 fabrication.

## 1. D9 torsion

Given `T : SourceTorsionClause.{0,0,0} l`, S1355 constructs the actual D9
torsion pair:

```lean
def S1355D9TorsionProp (T) : Prop := ArithmeticTorsionCompatibility T
theorem S1355D9Torsion_proved (T) : S1355D9TorsionProp T :=
  arithmeticTorsionCompatibility_of_clause T
```

`ArithmeticTorsionCompatibility` is the concrete slot statement from
`SourceDefinition31ArithmeticCompatibilitySlots` (imageContainsSL2 ∧
sixTorsionIndependent ∧ lTorsionCompatible ∧ 5 ≤ l ∧ Odd l), not a True
substitute.

Without a supplied `T`, the exact first field is `SourceTorsionClause`; its
first mathematical field is the actual rank-two l-torsion basis
(`S1298TorsionBasisType`), which the tree does not construct.  S1355 does
not fabricate it.

## 2. D9 cusp

Given an actual K-core orbicurve `X` and

```lean
O : TorsionQuotientBoundaryOrigin l (S1280Arithmetic l) X
```

S1355 constructs the actual D9 cusp pair:

```lean
def S1355D9CuspProp (O) : Prop := ArithmeticCuspOriginCompatibility O
theorem S1355D9Cusp_proved (O) : S1355D9CuspProp O :=
  arithmeticCuspOriginCompatibility_of_supply O
```

`ArithmeticCuspOriginCompatibility` is the Definition 3.1(f) global-origin
statement: the distinguished nonzero quotient class maps to the cusp and
generates the rank-one quotient.

## 3. Why D8 cusp data alone does not give D9 cusp

S1320/S1330 give:

- actual cusp point `S1320ActualCuspPoint`, coordinates `[0 : 1 : 0]`;
- actual q norm `1/5`;
- exact first field of `SourceCuspClause` is `epsilon : Real`, unconstrained;
- exact missing object `S1330RealCuspCoordinate`.

None of these is a boundary-origin datum.  `SourceCuspClause` has no
`originMap`, no distinguished quotient class, and no rank-one quotient.  The
exact first field for the D9 cusp pair is therefore

```lean
TorsionQuotientBoundaryOrigin l (S1280Arithmetic l) X
```

over an actual `X : Iut.HyperbolicOrbicurve (S1280Arithmetic l).K`.  S1355
records this type (`S1355D9CuspFirstField`) and does not manufacture a map
from `SourceCuspClause` to it.

## 4. Compile status

`tmp/sheaf/xif/paper/S1355D9TorsionCuspActual.lean`

```text
EXIT=0
```

70 lines, SHA256
`8C5829BA3D7FFD6738496E96DDA546218BB281213440EFCA4B271E89A7AAC5CF`, no
`sorry`.

## 5. Conclusion

- D9 torsion pair actual **conditional on a supplied D5 torsion clause**;
  exact first field `SourceTorsionClause` (rank-two basis missing).
- D9 cusp pair actual **conditional on a supplied boundary origin**; exact
  first field `TorsionQuotientBoundaryOrigin` over an actual K-core
  orbicurve.  D8 cusp point/clause alone is insufficient.
- No D5/D8 clause fabricated; no True/PUnit substitution.
- EXIT=0.
