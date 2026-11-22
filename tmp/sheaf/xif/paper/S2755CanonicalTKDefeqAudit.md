# S2755 — canonical T / K defeq audit for S2735Arithmetic

Date: 2026-11-07. Audit only; no source changes.

## 1. The K side of S2735Arithmetic

```lean
S2735Arithmetic (l) : InitialThetaArithmeticData l :=
  gaussianInitialThetaArithmeticData l
```

from S2735QPilotLineBundleActual.  `gaussianInitialThetaArithmeticData` sets

```lean
Fmod := GaussianField
F    := GaussianField
K    := GaussianField
```

(IUTI/InitialTheta/ConcreteArithmeticExample.lean).  Thus

```lean
(S2735Arithmetic l).K = GaussianField = QQ(i)   (definitional).
```

## 2. T candidates and defeq condition

A `SourceNativeInitialThetaData l` has

```lean
arithmetic : InitialThetaArithmeticData l
tuple : SourceInitialThetaTuple arithmetic
clauseA ... clauseF
```

For `T.arithmetic.K` to be defeq to `(S2735Arithmetic l).K`, one needs

```lean
T.arithmetic = gaussianInitialThetaArithmeticData l
```

(definitionally, or at least `T.arithmetic.K` defeq `GaussianField`).
When the equality holds, both K projections reduce to `GaussianField`, so
the defeq is `rfl`.

## 3. Actual T inventory

No concrete inhabitant of `SourceNativeInitialThetaData` is constructed in the
repository:

- `SourceNativeInitialThetaExists l` is only a `Prop`;
- `sourceNativeInitialThetaExists_iff_packaged` gives `Nonempty` from it, but
  no witness is produced;
- `SourceCompletion.toSourceNativeInitialThetaData` requires a supplied
  `SourceCompletion`;
- `NativeSourceAssemblyFields` is a conditional field package, not a T.

Therefore the actual candidate T list is EMPTY.  The only concrete arithmetic
data with the required K is `gaussianInitialThetaArithmeticData l` itself; it is
not a T, because no tuple/clauses A-F are constructed.

## 4. Candidate table

| candidate | has Gaussian K? | is actual T? | K defeq to S2735Arithmetic.K? |
|---|---|---|---|
| `gaussianInitialThetaArithmeticData l` | YES | NO (arithmetic only) | arithmetic-level K yes; no T |
| any T with `T.arithmetic = gaussian...` | YES | none constructed | yes (`rfl` on arithmetic) |
| `NativeSourceAssemblyFields`-derived T | not fixed | conditional | not established |
| `SourceCompletion`-derived T | not fixed | requires completion | not established |

## 5. Verdict

- S2735Arithmetic.K is definitionally `GaussianField` = QQ(i).
- A `SourceNativeInitialThetaData` T is a defeq candidate iff its arithmetic is
  `gaussianInitialThetaArithmeticData l`.
- No such actual T exists in the current tree; the candidate list is empty.
- Do not claim a canonical T/K defeq without constructing T and its clauses.

## 6. S2756 Haar/fundamentalDomain gate note

- S2756FractionalIdealHaarActual: actual `ZSpan.fundamentalDomain` + `volume`,
  actual Haar volume formula; NOT an indicator. PASS on Haar/fundamentalDomain.
- S2756LineBundleLatticeIQHullActual: `latticeLogVolume` is a supremum of
  covolume logs, not the `volume` of a fundamental domain; hull={1},
  scaleShift=id. It is not an indicator, but it is not the required actual
  Haar/fundamental-domain measure. Treat as INSUFFICIENT for the S2756 gate
  unless the actual S2756FractionalIdealHaarActual volume is used.
