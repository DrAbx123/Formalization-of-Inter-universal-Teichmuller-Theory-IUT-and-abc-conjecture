# S1185: KappaOrbitUnitsActionPairDatum / non-refl layer — exact first failure

Date: 2026-10-30. No new wrapper; report plus exact first failure.

## 1. Search result

There is no `S1184*.lean` file on disk.  No declaration named
`S1184KummerIso` or similar exists.  The closest actual construction is
`ThetaLinkKummerObjectsActual.lean`, which attempts to build the pair datum
from an actual strip equivalence; it does not compile (see below).

## 2. Actual production pieces that do work

`KappaOrbitPairActual.lean`:

- `LowerKappaDonor upper lower :=
  `∀ v, TimesMuKummer.Isomorphism
    (FPrimeStrip.pairUnitsActionUpper upper lower v)
    (FPrimeStrip.pairUnitsActionLower upper lower v)`;
- `pairOfLowerKappa` actual constructs
  `KappaOrbitUnitsActionPairDatum (pairGroup upper lower) upper lower`
  with
  `sourceUnits := (upper.Mon v)ˣ`,
  `sourceAction := pairUnitsActionUpper`,
  `factorUpper := pairFactorizationUpper`,
  `factorLower := pairFactorizationLower`,
  `kappaUpper := TimesMuKummer.Isomorphism.refl`,
  `kappaLower := donor`;
- `pairS00S01`/`pairS01S11` conditional on the donor;
- `kappaPairActual_status` records the conditional existence.

`KummerEvaluationArrowsActual2.lean`:

- `kummerOfPair D` actual: upper->lower `TimesMuKummer.Isomorphism`
  with `equiv := (D.kappaUpper).equiv.symm.trans (D.kappaLower).equiv`;
- `layerOfPair D` actual `SourceTimesMuKummerLayer G upper lower`;
- `evalPortionOfPair`, `kummerArrowOfPair`, `evaluationArrowOfPair` actual
  conditional on PairDatum.

Thus **if** a `LowerKappaDonor` is supplied, the PairDatum and the non-refl
`SourceTimesMuKummerLayer` are already actual.

## 3. The attempted S1184 path and its first failure

`ThetaLinkKummerObjectsActual.lean` attempts to build the donor from an actual
strip equivalence `e : FPrimeStripEquiv upper lower`:

- `transportedLowerAction := (lower.unitsAction v).comp
    ((e.isoPi v).toMonoidHom.comp pairFactorizationUpper)`;
- `xMuQuotientEquiv := TimesMuQuotient.congr (Units.mapEquiv (e.isoMon v))`;
- `kappaLowerOfStripEquiv` tries to turn this into
  `TimesMuKummer.Isomorphism pairUnitsActionUpper transportedLowerAction`;
- `pairDatumOfStripEquiv` uses `factorLower := e.isoPi.comp factorUpper` and
  then `kappaLowerOfStripEquiv`.

Compilation fails first at `xMuQuotientEquiv_equivariant`
(ThetaLinkKummerObjectsActual.lean:104): after quotient induction the target
uses the quotient representative directly, and the rewrite pattern
`TimesMuQuotient.congr ?e (quotientMap ?u)` does not match; the subsequent
`invariantImage` proof also fails at lines 141/153 because it tries to prove a
unit-level fixed-point law from a quotient-level `invariantImage_fixed`,
which is not sufficient.

Even if repaired, the mathematical mismatch remains: the actual strip link
only relates the graph of `e.isoPi`; `pairUnitsActionLower` on the independent
product component is not the transported lower action.  This is exactly the
obstruction recorded in `LowerKappaDonorActual.lean`.

## 4. Exact first missing object

```text
LowerKappaDonor upper lower :=
  ∀ v : V, TimesMuKummer.Isomorphism
    (FPrimeStrip.pairUnitsActionUpper upper lower v)
    (FPrimeStrip.pairUnitsActionLower upper lower v)
```

for the actual pairs `(S00,S01)` and `(S01,S11)`, or equivalently a
link-compatible common group `LinkedCommonGroup upper lower link` with a
lower Kappa representative on the linked actions.

`LowerKappaDonorActual.lean` proves the structural obstruction: the production
pair group is `(Pi_upper × Pi_lower)`; upper action depends only on the upper
component and lower action only on the lower component.  An F-prime-strip link
relates the two components only on the graph of `e.isoPi`; it does not identify
the independent product factors.  The missing object is a graph/diagonal
subgroup carrying both actions, or an explicit `kappaLower` on such a group.

## 5. Consequences

- `KappaOrbitUnitsActionPairDatum` for the actual pairs: not actual; conditional
  on `LowerKappaDonor`.
- `SourceTimesMuKummerLayer` from `layerOfPair`: conditional; without donor only
  the self layer `selfKummerLayer` is actual, and its `kummer` is
  `TimesMuKummer.Isomorphism.refl` (not non-refl).
- No actual non-refl layer over distinct strips; no wrapper was written.

## 6. Consumer

Direct consumers of the desired pair datum:

- `KummerEvaluationArrowsActual2.kummerOfPair` / `layerOfPair`;
- `KummerEvaluationArrowsActual2.kummerArrowOfPair` / `evaluationArrowOfPair`;
- downstream `SourceKummerArrow` / Kummer-evaluation square.

Supplying `LowerKappaDonor` would remove exactly the donor premise from these
consumers; nothing else changes.

## Verdict

- actual: `pairOfLowerKappa`, `layerOfPair`, `kummerOfPair` conditional on the
  donor; actual strip links and pair factorization data.
- exact first failure: `LowerKappaDonor` for the actual product pair, requiring
  a linked common group; no S1184 Kummer iso exists.
- no new file/wrapper; EXIT=0 report.
