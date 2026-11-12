# S2388: local postcomposition cancellation for representable maps

Date: 2026-11-03. Layer: **O** (D6(c) finite-etale input).
No target change, no fake.

## Files read

- `tmp/sheaf/xif/paper/S1742TwoYonedaActual.lean`
- `tmp/sheaf/xif/paper/S2380PresentationCancellationActual.lean`
- `tmp/sheaf/xif/paper/S2089StackCancellationActual.lean`
- `tmp/sheaf/xif/paper/S2090StackCancellationObstructionActual.lean`
- `tmp/sheaf/xif/paper/S2291UniformGraphCompatActual.lean` (refutation datum,
  only for non-interference)
- reports `S2380-presentation-cancellation.md`, `S2377-stack-presentation.md`

## Source object / domain / direction

- Source object: local postcomposition cancellation for representable maps
  `S1742StrongTransOfHom a0` and `S1742StrongTransOfHom g0`.
- Domain: original O-layer D6(c); no false S2130/S2185/S2269 target.
- Direction: prove the local cancellation for representable g0 when g0 is
  monic, or record the exact scheme-level comparison still missing.

## Deliverable

`tmp/sheaf/xif/paper/S2388PostcompCancellationActual.lean`

```text
EXIT=0
olean=YES
lines=55
SHA256=8AE313BDCF8B720CC6012ECE3AC227708E4BD9BD2EB26DB19037393AC234ABE6
olean path=.lake/build/lib/lean/tmp/sheaf/xif/paper/S2388PostcompCancellationActual.olean
axioms: propext, Classical.choice, Quot.sound
```

## BUILT

1. `S2388HomEqOfIso g0`: exact scheme-level comparison
   `Iso (a0 ; g0) (b0 ; g0) -> a0 ; g0 = b0 ; g0` for representable
   strong transformations.
2. `S2388PostcompRequired g0`: local cancellation target,
   `Iso (a0 ; g0) (b0 ; g0) -> Iso a0 b0`.
3. `S2388Postcomp_of_homEq`: if `S2388HomEqOfIso g0` holds and
   `Mono g0`, then `S2388PostcompRequired g0`.
   Proof: scheme-level equality plus monic cancellation
   (`cancel_mono`), then `eqToIso` of representable strong transformations.

No inhabitant of `S2388HomEqOfIso` is asserted.

## Exact first missing

```text
S2388HomEqOfIso g0
  = forall {a0 b0},
      Iso (vcomp (S1742StrongTransOfHom a0) (S1742StrongTransOfHom g0))
          (vcomp (S1742StrongTransOfHom b0) (S1742StrongTransOfHom g0)) ->
      a0 ; g0 = b0 ; g0
```

S1742 supplies the reverse mapping from a strong transformation to its
underlying scheme map and proves it is well-defined on 2-isomorphism classes
(`S1742HomOfStrongTrans_congr`). What is still missing is the identification of
the underlying scheme map of `vcomp (S1742StrongTransOfHom a0)
(S1742StrongTransOfHom g0)` with `a0 ; g0` (and similarly for b0), i.e. the
representable-composition computation. Without that, the 2-isomorphism after
postcomposition does not yet yield the scheme equality needed for
`cancel_mono`.

## Strong/coherent condition

The local route applies to any representable map `g0` that is:

1. `Mono` as a scheme morphism;
2. satisfies the scheme-level comparison `S2388HomEqOfIso g0`.

Strong/coherent target covers are not automatically monic; this is an extra
condition, not a consequence of the cover structure. The exact condition is
the pair above.

## Weak-cover failure

No concrete counterexample to `S2388HomEqOfIso` or to local postcomposition
cancellation is produced. S2291 refutes the S2130 two-pullback target, not this
local cancellation; it is not used as a false cancellation counterexample.

## Consumer

If `S2388HomEqOfIso g0` and `Mono g0` hold,
`S2388PostcompRequired g0` feeds the local construction in S2380; then the
S2089 presentation statement and stack cancellation can be assembled. No
S2130/S2185/S2269 target is used.

## Next executable subgoal

Prove the representable-composition computation

```text
S1742HomOfStrongTrans
  (vcomp (S1742StrongTransOfHom a0) (S1742StrongTransOfHom g0))
  = a0 ; g0
```

then `S1742HomOfStrongTrans_congr` gives `S2388HomEqOfIso g0`. Alternatively,
prove the local cancellation for a concrete non-monic/weak cover, or exhibit a
counterexample.

## Reports read

`coord/reports/S2380-presentation-cancellation.md`,
`coord/reports/S2377-stack-presentation.md`, and the S1742/S2089/S2090
definitions above.
