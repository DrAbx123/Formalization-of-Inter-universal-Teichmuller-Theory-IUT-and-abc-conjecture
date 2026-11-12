# S1466: MulByInt degree/separableDegree port (Mathlib v4.32.2)

Date: 2026-10-31. New independent Lean file; no S1431 import.

## 1. Actual file

`tmp/sheaf/xif/paper/S1466MulByIntDegreeActual.lean`

```text
EXIT=0
SHA256 56AE717750C81D3AE6ED296FDB273DAB3693A29275F567710402539BE83843F1
olean  .lake/build/lib/lean/tmp/sheaf/xif/paper/S1466MulByIntDegreeActual.olean
olean SHA 50164E06597E93FD0518A5B84FF46415860B833D55B77D51E1FB11CFE8B75C47
```

No `sorry`/`axiom`; `#print axioms` for the three exported results is the
standard trio `propext, Classical.choice, Quot.sound`.

## 2. Ported actual layer

Definitions:

```lean
noncomputable def mulByIntX (W) (n) : RatFunc F :=
  algebraMap F[X] (RatFunc F) (W.Φ n) /
  algebraMap F[X] (RatFunc F) (W.ΨSq n)

isogenyDegree f := Module.finrank f.fieldRange W₂.toAffine.FunctionField
isogenySeparableDegree f := Field.finSepDegree f.fieldRange W₂.toAffine.FunctionField
isogenyInseparableDegree f := Field.finInsepDegree f.fieldRange W₂.toAffine.FunctionField
```

Actual theorems:

- `finrank_adjoin_mulByIntX`:
  `[F(x) : F(Φ_n/ΨSq_n)] = n.natAbs ^ 2` from
  `IsCoprime (W.Φ n) (W.ΨSq n)`;
- `isogenySeparableDegree_mul_inseparableDegree`:
  `sepDeg * insepDeg = degree`;
- `isogenySeparableDegree_eq_degree_of_isSeparable`:
  separable case `sepDeg = degree`;
- `isogenySeparableDegree_eq_natAbs_sq_of_degree`:
  `degree = n.natAbs^2` + separable ⇒ `sepDeg = n.natAbs^2`.

## 3. Exact first fields for `sepDeg [n] = n²`

The missing actual object is not a definition; it is the `[n]` function-field
endomorphism and its two inputs:

1. **`mulByIntFunctionField n`**: an actual
   `W.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField` whose pullback of
   the affine coordinate is `mulByIntX W n`.  Mathlib v4.32.2 has no
   multiplication-by-`n` isogeny on the function field (no `[n]` map, no
   `Isogeny`).
2. **`IsCoprime (W.Φ n) (W.ΨSq n)`**: TauCeti's `isCoprime_Φ_ΨSq`, obtained
   there through the ZSMul/elliptic-net closure; Mathlib v4.32.2 lacks the
   EDS theorem `IsEllipticNet (normEDS b c d)`.
3. **`Algebra.IsSeparable f.fieldRange W.toAffine.FunctionField`**: TauCeti
   derives it for `[n]` from the invariant differential; Mathlib v4.32.2 has
   no invariant differential on the Weierstrass function field.
4. **PrimeKernel layer**: kernel of `[p]`, `card_ker_le_separableDegree`,
   rational-kernel bounds are absent with the `Isogeny` API.

So `sepDeg[n] = n²` is **conditional** in S1466, not unconditional.  The
actual arithmetic degree `[F(x) : F(Φ/ΨSq)] = n²` and the separable-degree
factorisation are proved; the three exact fields above are not.

## 4. Relation to S1431

S1431 attempted the same theorem but currently does not compile (function-field
algebra instances/`RatFunc` tower errors at lines 154/163/170/182/256/275/301/
368/378/424/439) and its axiom report contains `sorryAx` for
`finrank_functionField`, `degree_mulByIntIsogeny`, and
`separableDegree_mulByIntIsogeny`.

S1466 does not import S1431 and does not use those broken declarations.  It
keeps only the arithmetic half that is actually kernel-closed.

## 5. Conclusion

- **actual**: `mulByIntX`, the three degree definitions, degree
  factorisation, separable-case equality, arithmetic `[F(x):F(Φ/ΨSq)]=n²`.
- **exact fields**: `mulByIntFunctionField` with pullback `Φ/ΨSq`,
  `IsCoprime Φ ΨSq`, `Algebra.IsSeparable` for `[n]`, PrimeKernel API.
- No fake `Isogeny`, `sorry`, or `axiom`; EXIT=0.
