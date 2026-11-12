# Stackification requirement for A6 quotient (deep-audit note)

Date: 2026-11-07. For kummer/B route 3. Not a proof, a precise construction target.

## 1. What S2882A6Q is

`S2882A6Q` is the strict pointwise functor

```text
U |-> ActionCategory SignGroup (U-points of X)
```

where `X = S2844X` and `SignGroup` acts by `alphaOverS2844` (order two).
`S2882A6PFunctor.map_comp := rfl`; `.toPseudofunctor'` gives the pseudofunctor.

## 2. Why it is only a prestack

At each test object, Q(U) is the action groupoid: objects P, morphisms g with
g.P = Q. This sees only the trivialized sign-torsor. A descent datum for a
covering sieve can contain a nontrivial SignGroup-torsor; the pointwise action
groupoid has no object representing that torsor. Hence effective descent fails:
Q is not a stack. S1971 section 4 states exactly this: the pointwise colimit is
only a prestack; stackification is a separate input.

Consequence: `hQ : S2882A6Q.IsStack` is likely FALSE, not merely unproved.
Do not prove it; replace it by the correct quotient stack.

## 3. Correct quotient stack (route 3 target)

Over the etale site of `SchemeOverField K`, define `[X/SignGroup]` by

```text
U |-> { (T -> U, f : T -> X) }
  T is a SignGroup-torsor over U,
  f is SignGroup-equivariant (f(g.t) = g.f(t)).
morphisms: cartesian squares over U compatible with f.
```

Properties to prove:
1. this is an etale stack (torsors are a stack; equivariant maps glue);
2. its fiber at a trivialized torsor is equivalent to ActionCategory;
3. the natural map X -> [X/G] is a SignGroup-torsor/sign-invariant quotient;
4. the bicategorical quotient universal property (S2870QuotientWitnessData).

This is the mathematical stackification of the pointwise action groupoid, but
constructed as the **stack of torsors**, which is a concrete object, not an
abstract stackification.

## 4. Exact A6 route-3 construction steps

1. Define `S2882A6TorsorStack` as a `Pseudofunctor (LocallyDiscrete (SchemeOverField K)^op) Cat`
   (or a `Iut.EtaleStackPseudofunctor K`).
2. Prove `S2882A6TorsorStack.IsStack etaleTopology` using Mathlib's
   `Pseudofunctor.IsStackFor`/`IsStack.of_isStackFor` and the fact that torsors
   satisfy effective descent.
3. Prove pointwise equivalence to `S2882A6PointwiseQuotient` at trivial torsors.
4. Feed this Q (not S2882A6Q) into `S2870CF`/`S2870QuotientWitnessData` and
   the corrected core.

Consumer change: all current `hQ : S2882A6Q.IsStack` parameters in
S2892/S2905/S2908/S2927/S2928/S2934 must be re-pointed to the torsor stack.
That is a real interface change, not a local patch; route 2 remains interim.

## 5. If route 3 is too large

Fallback 3b: generic stackification of a Cat-valued prestack via descent data.
Mathlib has `Pseudofunctor.DescentData` and `IsStackFor`, but NO stackification
construction (searched Mathlib 2026-11-07); building it is larger than the
torsor-stack route. Do not claim either as done without a compiling stack.

## 6. Why this is not a gap-shift

The target is a concrete category of torsors with equivariant maps and the
actual IsStack proof; it does not assume the corrected A6 core or the quotient
witness. The witness/universal property remains a separate field (S2870).
