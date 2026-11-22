# S1151: first joint diagram audit (Remark 3.10.2 / 3.11.1)

Sources read:

- `LeanFormal/IUT/IUTIII/Theorem311/SourceFTimesMuPrimeStripPolyIsomorphism.lean`
  - `SourceFTimesMuPrimeStripRem3102Diagram` at line 805
  - `iplLink` at line 845
  - `SourceFTimesMuPrimeStripEquivalence.canonicalLift` at line 343
  - `SourceFTimesMuPrimeStripPolyIsomorphismSquare` at line 717
- `LeanFormal/IUT/IUTIII/Theorem311/SourceH1H2Construction.lean`
  - `fPrimeStripAt` at line 52
  - `fLinkAt` at line 165

## 1. Eight strips

Bottom row `(n,m)`-level:

1. `bottomEnv`
2. `bottomGau`
3. `bottomLGP`
4. `bottomLgp`

Top row `(n,o)`-level:

5. `topEnv`
6. `topGau`
7. `topLGP`
8. `topLgp`

All eight are `SourceFTimesMuPrimeStrip V`, i.e. actual F-turnstile-times-mu-prime-strips.

## 2. Arrows

Lower horizontals:

- `lowerEnv : bottomEnv ≃ bottomGau` — induced evaluation iso of IUTchII Cor. 4.10(ii), first lower horizontal.
- `lowerGau : bottomGau ≃ bottomLGP` — Prop. 3.7(iii).
- `lowerLGP : bottomLGP ≃ bottomLgp` — Prop. 3.7(iv).

Upper horizontals:

- `upperEnv : topEnv ≃ topGau` — induced etale-like evaluation isomorphism, first upper horizontal.
- `upperGau : topGau ≃ topLGP` — Prop. 3.10(i).
- `upperLGP : topLGP ≃ topLgp` — Prop. 3.10(i).

Verticals:

- `verticalEnv : bottomEnv ≃ topEnv` — Kummer iso, Prop. 2.1(ii).
- `verticalGau : bottomGau ≃ topGau` — Prop. 3.10(i).
- `verticalLGP : bottomLGP ≃ topLGP` — Prop. 3.10(i).
- `verticalLgp : bottomLgp ≃ topLgp` — Prop. 3.10(i).

## 3. Commutative squares

The structure has three commuting squares, one per column:

- env square: `lowerEnv ≫ verticalGau = verticalEnv ≫ upperEnv` (`commEnv`);
- gau square: `lowerGau ≫ verticalLGP = verticalGau ≫ upperGau` (`commGau`);
- LGP square: `lowerLGP ≫ verticalLgp = verticalLGP ≫ upperLGP` (`commLGP`).

The abstract four-corner square is `SourceFTimesMuPrimeStripPolyIsomorphismSquare`, with `upperHorizontal`, `lowerHorizontal`, `leftKummer`, `rightKummer`, `commutes`, plus two-sided opposite-arrow existence; `ofUpperHorizontal` constructs a square from upper horizontal and two Kummer pairs.

`iplLink` is:

```lean
D.lowerGau.symm ≫ D.lowerEnv.symm ≫ D.verticalEnv ≫ D.upperEnv ≫ D.upperGau ≫ D.upperLGP
```

with actual cancellation lemmas `lowerEnv_symm_verticalEnv_upperEnv` and `lowerGau_symm_verticalGau_upperGau`.

## 4. Which upperEnv arrow is the actual evaluation?

The actual evaluation should be identified with:

> `upperEnv : topEnv → topGau` (first upper horizontal),

the induced etale-like evaluation isomorphism of Remark 3.10.2, not `lowerEnv`.
`lowerEnv` is the induced version of the *evaluation* of IUTchII Cor. 4.10(ii); `upperEnv` is its etale-like upper-row counterpart.  The paper's evaluation isomorphism in the first joint figure is the upper-row one; `iplLink` uses `D.upperEnv` explicitly after `verticalEnv`.

## 5. Reusable actual arrows

Actual, reusable:

- `I.fPrimeStripAt n m` and `I.fLinkAt n m n' m'` (SourceH1H2Construction) — actual source F-strips and links.
- `SourceFTimesMuPrimeStripEquivalence.canonicalLift (I.fLinkAt ...)` — actual full poly-isomorphism between canonical times-mu strips.
- `SourceFTimesMuPrimeStripPolyIsomorphismSquare.ofUpperHorizontal` — actual square assembly from an upper horizontal and Kummer inverse pairs.
- `iplLink` itself — actual full poly-isomorphism once the diagram data are supplied.

## 6. Exact gap

Not actual in the tree:

- the diagram's eight vertices as an algorithm-indexed family inside the Theorem 3.11 construction;
- source-level Kummer/evaluation strip arrows themselves (the file's dependency cone has no algorithm-indexed strip family);
- therefore no inhabitant of `SourceFTimesMuPrimeStripRem3102Diagram` is constructed from `I`.

The file records the diagram as exact supplied data (lines 799-804): consumers supply it; `iplLink` and the commutativity/cancellation laws are actual conditional on that data.

Related exact source-level layers:

- `ThetaLinkLogKummerActual.ThetaLinkFactorizationData` / `ThetaLinkSquareData` — exact structures wrapping `SourceLinkFactorization` and `SourceKummerEvaluationSquare`, no inhabitant asserted.
- `ThetaLinkLogKummerActual.qPilotStripAtOneZero = I.primeStripAt 1 0` — actual anchor, but `QPilotLinkIdentification.qPilotStrip_eq` remains an explicit field.

## 7. Conclusion

- Actual: eight-strip shape, all arrow types, three commutativity laws, `iplLink`, `canonicalLift`, `fPrimeStripAt`, `fLinkAt`, square assembly.
- Exact: the diagram data themselves and the algorithm-indexed source evaluation/Kummer arrows; the actual evaluation corresponds to `upperEnv : topEnv → topGau`.
- No fake inhabitant of the diagram; no wrapper of S1073.

