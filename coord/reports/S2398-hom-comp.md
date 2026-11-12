# S2398: representable composition equation and local cancellation

Date: 2026-11-03. Layer: **O** (D6(c) finite-etale input).
No target change, no fake.

## Files read

- `tmp/sheaf/xif/paper/S2388PostcompCancellationActual.lean`
- `tmp/sheaf/xif/paper/S2380PresentationCancellationActual.lean`
- `tmp/sheaf/xif/paper/S1742TwoYonedaActual.lean`
- `tmp/sheaf/xif/paper/S2089StackCancellationActual.lean`
- reports `S2388-postcomp-cancellation.md`, `S2380-presentation-cancellation.md`

## Source object / domain / direction

- Source object: the representable composition equation for
  `vcomp (S1742StrongTransOfHom a0) (S1742StrongTransOfHom g0)`.
- Domain: original O-layer D6(c); no S2130/S2185/S2269.
- Direction: prove the composition equation, derive the scheme-level comparison
  `S2388HomEqOfIso`, and then local postcomposition cancellation under
  `Mono g0`.

## Deliverable

`tmp/sheaf/xif/paper/S2398HomOfStrongTransCompActual.lean`

```text
EXIT=0
olean=YES
lines=51
SHA256=089C306E5F62541AF885B4344206319BCEDE0642D273D8C01E247587E58559FF
olean path=.lake/build/lib/lean/tmp/sheaf/xif/paper/S2398HomOfStrongTransCompActual.olean
axioms: propext, Classical.choice, Quot.sound
```

## PROVED / actual

1. `S2398HomOfStrongTrans_vcomp`:

```text
S1742HomOfStrongTrans
  (vcomp (S1742StrongTransOfHom a0) (S1742StrongTransOfHom g0))
  = a0 ; g0
```

This is the missing representable-composition computation. Proof unfolds
`S1742HomOfStrongTrans` at the identity section, uses `StrongTrans.comp_app`
and `S1742App_obj` on the two representable components, then cancels identity
composition.

2. `S2398HomEqOfIso g0 : S2388HomEqOfIso (S := S) g0`:

```text
Iso (a0 ; g0) (b0 ; g0) -> a0 ; g0 = b0 ; g0
```

Proof: apply `S1742HomOfStrongTrans_congr` to the 2-isomorphism and rewrite
both sides with `S2398HomOfStrongTrans_vcomp`.

3. `S2398PostcompRequired [Mono g0] : S2388PostcompRequired (S := S) g0`:

```text
Iso (a0 ; g0) (b0 ; g0) -> Iso a0 b0
```

Proof: `S2398HomEqOfIso` plus monic cancellation
(`S2388Postcomp_of_homEq`, `cancel_mono`), then `eqToIso`.

## Exact remaining condition

The local cancellation is now actual for every representable map
`S1742StrongTransOfHom g0` with `Mono g0`. The remaining exact condition for
an arbitrary cover map `g.map` is:

```text
represent g.map as S1742StrongTransOfHom g0
and prove Mono g0
```

or otherwise provide a local non-representable cancellation/corrected apex.
Neither strong/coherent cover structure nor arbitrary weak cover structure is
known to supply `Mono g0`; this remains an extra condition. No concrete
weak-cover counterexample to `Mono` or to local cancellation is produced.

## What is not claimed

- No global `S2380PostcompSupply` is constructed.
- No arbitrary weak cover is asserted to be representable/monic.
- No S2130/S2185/S2269 target is used.
- No terminal/point/metadata substitution is used.

## Consumer

`S2398PostcompRequired` feeds the local construction in S2380. With the
remaining representability+`Mono` condition (or corrected apex), one obtains
f's presentation, then `S2089StackPresentationStatement`, stack cancellation,
and the S2086 finite-etale input, without false S2130.

## Next executable subgoal

For the actual cover maps of interest, prove:

```text
exists g0 : T ⟶ U,
  g.map = S1742StrongTransOfHom g0 ∧ Mono g0
```

or isolate a concrete non-representable/non-monic weak cover where local
cancellation fails.

## Reports read

`coord/reports/S2388-postcomp-cancellation.md`,
`coord/reports/S2380-presentation-cancellation.md`, and S1742/S2089
definitions.
