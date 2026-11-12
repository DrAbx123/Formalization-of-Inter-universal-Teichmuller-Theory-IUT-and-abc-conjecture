# D5 target strength: pair transitivity vs (10,2) cycle type

Date: 2026-11-06. Sources: S2445D5LargeImageChainActual, S2447D5GateIntegrationActual, S2449D5FinalStatusActual, S2440RangePairTransitiveSubagentActual.

## Consumer chain

1. S2445 defines:

```lean
def S2445RangePairTransitive : Prop := S2203RangePairTransitiveRequired S1982Basis
def S2445RangeCycleType     : Prop := S2203RangeCycleTypeRequired S1982Basis
def S2445ExactFirstMissing  : Prop :=
  S2445RangePairTransitive ∧ S2445RangeCycleType ∧
    S2445RangeDetSurjective ∧ S2445DegreeEqImageOrder
```

2. The D5 target consumer is:

```lean
theorem S2445D5LargeImageFive_of_pair_cycle
    (hpair : S2445RangePairTransitive)
    (hcycle : S2445RangeCycleType) :
    S1987D5LargeImageFive
```

It requires BOTH pair transitivity AND cycle type (10,2).

3. S2447/S2449 separate the refuted degree target and keep:

```lean
S2447D5ExactFirstMissing = S2445GroupRouteExact
S2449D5ExactFirstMissing = S2445GroupRouteExact
```

which is still the pair+cycle package. The corrected D5 theorem from exact missing is `S2449D5LargeImageFive_of_exact`.

## 12-cycle status

```lean
S2447PairTransitive_of_twelveCycle :
  S2440TwelveCycleInputRequired → S2445RangePairTransitive
```

So the 12-cycle input implies ONLY the pair-transitivity half. It does not imply `S2445RangeCycleType` (10,2).

There is no theorem of the form

```lean
S2440TwelveCycleInputRequired → S2445RangeCycleType
```

and none can be expected: a 12-cycle has cycle type {12}, not {2,10}.

## Conclusion

- Paper/D5 consumer needs BOTH pair transitivity and (10,2) cycle type.
- 12-cycle is a legitimate SUFFICIENT certificate for the pair half only.
- 12-cycle alone is NOT sufficient for D5.
- 12-cycle is not exactly overstrong for pair transitivity? It is sufficient but not necessary; however as a route it is a valid concrete certificate.
- It is INSUFFICIENT, not incorrect, as a D5 package: the (10,2) cycle-type input remains missing.

## Exact remaining D5 inputs

1. S2445RangePairTransitive (can be supplied by S2440TwelveCycleInputRequired or S1725ImageTail).
2. S2445RangeCycleType = (10,2) cycle type, still an independent missing arithmetic input.
3. Det surjectivity/degree were refuted/target-corrected and are not part of the final D5 exact missing.

## Status

No new Lean proof; audit only. All cited definitions/theorems are actual in S2445/S2447/S2449.
