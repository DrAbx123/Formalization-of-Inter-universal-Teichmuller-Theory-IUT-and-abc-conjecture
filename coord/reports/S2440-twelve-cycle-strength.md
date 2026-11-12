# S2440TwelveCycleInputRequired: strength audit

Date: 2026-11-06. Sources: S2440RangePairTransitiveSubagentActual, S2460PairTransitiveFinalActual, S2375RangePairTransitiveActual.

## Exact equivalence

YES: the two 12-cycle formulations are exactly equivalent in the tree.

```lean
theorem S2460TwelveCycleInput_iff_root :
    S2440TwelveCycleInputRequired ↔ S2460RootTwelveCycleRequired
```

`S2440TwelveCycleInputRequired` (S2440, line 277) is a 12-cycle in the actual range; `S2460RootTwelveCycleRequired` (S2460, line 419) is the corresponding root-cycle formulation. Both directions are proved; not a one-way implication.

## Sufficiency for pair transitivity

```lean
S2440RangePairTransitive_of_twelveCycle :
  S2440TwelveCycleInputRequired → S2375RangePairTransitiveRequired

S2440PairTransitive_of_cycleType12 :
  (12-cycle subgroup) → PairTransitive H
```

So 12-cycle is a sufficient condition for pair transitivity.

## Is it necessary?

NO evidence in the tree. There is no theorem of the form

```lean
PairTransitive range → S2440TwelveCycleInputRequired
```

The only equivalence around pair transitivity is under the separate (10,2) cycle-type input:

```lean
S2440RangePairTransitive_iff_imageTail_of_cycleType102 :
  S2203RangeCycleTypeRequired → (PairTransitive ↔ S1725ImageTail)
```

That is not a 12-cycle equivalence.

## Strength conclusion

- 12-cycle ⇒ pair transitivity: proved.
- pair transitivity ⇒ 12-cycle: not proved, and generally false for arbitrary subgroups (a pair-transitive subgroup need not contain a 12-cycle).
- Therefore 12-cycle is a SUFFICIENT but NOT NECESSARY condition for the paper's pair-transitivity target. It is stronger than the target.
- For the full D5 large-image input, pair transitivity alone is also not enough: the separate `S2203RangeCycleTypeRequired` (cycle type 10,2) is still needed. The 12-cycle route and the (10,2) route are different sufficient packages.

## Paper target strength

The paper target is pair transitivity (plus the other D5 inputs). A 12-cycle is a concrete certificate that implies it; it is not equivalent to it. Using 12-cycle as the sole target would be overstrong and does not replace the cycle-type input.

## Status

All cited `iff`/implication theorems are in the S2440/S2460 files; no new Lean proof was written in this audit.
