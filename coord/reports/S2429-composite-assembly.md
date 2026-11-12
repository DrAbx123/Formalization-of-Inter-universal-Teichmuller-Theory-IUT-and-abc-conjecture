# S2429: cast-composition and composite Mono CLOSED; map iso exact

Date: 2026-11-03. Layer: **O** (D6(c) finite-etale input).
No target change, no fake.

## Deliverable

`tmp/sheaf/xif/paper/S2429CompositeAssemblyActual.lean`

```text
EXIT=0
olean=YES
lines=116
SHA256=B220AB8ED37AA8D2A7C103A3370475645DD5C9CB264D0824A1A5DFF121122C7C
olean path=.lake/build/lib/lean/tmp/sheaf/xif/paper/S2429CompositeAssemblyActual.olean
axioms: propext, Classical.choice, Quot.sound
```

## PROVED / actual

1. `S2429CastComp_general`: general type-level cast-composition lemma.
2. `S2429CastComp_holds : S2429CastComp`: instantiation to fiber equalities.
3. `S2429MonoCastComp`: general Mono of `a ≫ (h ▸ b)` from `Mono a`,
   `Mono b`, by `cases h; inferInstance`.
4. `S2429CompositeMap_mono`: `Mono (S2429CompositeMap H)`, actual.
5. `S2429CompositeMap H := H.R1.g0 ≫ (H.middle_eq ▸ H.R2.g0)`, actual.
6. `S2424CompositeOfMapIso H h : S2424CompositeRepresentable H` from only
   the composite map iso `h`; Mono is no longer an assumption.
7. `S2424CompositionRequired_of_mapIso H h : S2424CompositionRequired H`.

## Exact first missing

```text
S2429CompositeMapIsoRequired H
  = Nonempty (Iso
      (S2403CastHom H.R1.source_fiber_eq H.R2.target_fiber_eq
        (S1641CoverMapComp g1 g2).map)
      (S1742StrongTransOfHom (S2429CompositeMap H)))
```

This is the sole remaining gap for S2424 composition.

## Why the attempted direct construction failed

The natural proof decomposes:

1. `S1641CoverMapComp_map` and `S2429CastComp_holds` to rewrite the cast
   composite to a vcomp of two casts;
2. `R1.map_iso`, `R2.map_iso` and `whiskerRightIso`/`whiskerLeftIso` to
   compose;
3. `S2398HomOfStrongTrans_vcomp` and `S1742StrongTransIsoOfHom` to identify
   the result with `S1742StrongTransOfHom (S2429CompositeMap H)`.

The blocker is step 2/3 after `rcases H with ⟨R1,R2,hmid⟩; cases hmid`:
Lean fails dependent elimination because `R2`'s scheme fields depend on the
middle equality (`R2.1 = R1.2`). A direct `cases` on `H.middle_eq` is not
accepted. This is the exact structural obstruction; no axiom or fake iso is
inserted.

## Status

- S2429CastComp: actual.
- Composite map: actual.
- Composite Mono: actual.
- Composite map iso: exact missing.
- S2424CompositionRequired: conditional only on this iso.
- S2086StackCancellation / S2089PresentationStatement: still open.
- No S2130/S2185/S2269, no global cancellation.

## Next executable subgoal

Construct `S2429CompositeMapIsoRequired H` by:

- transporting R2's map_iso along `H.middle_eq` without dependent elimination
  (explicit `eqToIso`/cast of the S2403 data), or
- generalizing the composite-iso statement to arbitrary scheme equalities and
  proving it by type-level `cases`, as was done for CastComp and Mono.

No conditional apex or handwave cancellation is used.
