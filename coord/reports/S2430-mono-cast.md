# S2430: Mono of the cast composite CLOSED

Date: 2026-11-03. Layer: **O** (D6(c) finite-etale input). No target change, no fake.

## Deliverable

`tmp/sheaf/xif/paper/S2430MonoCastActual.lean` (58 lines; imports
`tmp.sheaf.xif.paper.S2429CompositeAssemblyActual`).

```text
EXIT=0
olean=YES
olean path=.lake/build/lib/lean/tmp/sheaf/xif/paper/S2430MonoCastActual.olean
olean size=28624 bytes
SHA256(source)=6879CDF5C65B947FB58697C6FE44241C347B64D43BB501F20489175D1C5B1B4E
SHA256(olean)=2AF1458D3F15936D1F0B8E2EF3B303BEBA97FC2012ECCAEB81AB155D07516838
axioms: propext, Classical.choice, Quot.sound
toolchain: leanprover/lean4:v4.32.2
```

Exact build command (as specified):

```text
cd D:/lean; lake env lean -j1 -R 'D:/lean' -o '.lake/build/lib/lean/tmp/sheaf/xif/paper/S2430MonoCastActual.olean' 'tmp/sheaf/xif/paper/S2430MonoCastActual.lean'
```

Dependency version used and re-verified from source (own build, EXIT=0):

```text
tmp/sheaf/xif/paper/S2429CompositeAssemblyActual.lean
116 lines, mtime 2026-11-03 03:07:54
SHA256=B220AB8ED37AA8D2A7C103A3370475645DD5C9CB264D0824A1A5DFF121122C7C
```

The S2429 source hash was unchanged before/after the verification run
(`S2429_STABLE=True`). Only build artifacts (`.olean`) were refreshed; no
existing source file was modified by this task.

## PROVED / actual

### General Mono-cast-composition lemma (type generalization)

`S2430MonoCastComp_general` (file lines 33-41):

```text
{S1 S2 S2' S3 : SchemeOverField S1726K}
(a : S1 ⟶ S2) (b : S2' ⟶ S3)
(ha : Mono a) (hb : Mono b) (h : S2 = S2') :
  Mono (a ≫ (h ▸ b))
```

Proof: `cases h`, after which the transport `h ▸ b` is definitionally `b` and
the goal is `Mono (a ≫ b)`; `haveI` installs `ha`, `hb` and
`infer_instance` uses Mathlib's `instance mono_comp` (Mathlib's
`Mathlib/CategoryTheory/Category/Basic.lean`, by `to_dual` from `epi_comp`).

Because `S1 S2 S2' S3` are arbitrary objects and `h` is a standalone
hypothesis, the dependent elimination is structural. This is the Mono analogue
of `S2429CastComp_general`.

### Target instantiation

`S2430CompositeMap_mono` (file lines 50-55):

```text
{A B C : S1728Cover} {g1 : S1728CoverMap A B} {g2 : S1728CoverMap B C}
(H : S2424ComposableRepresentable g1 g2) :
  Mono (S2429CompositeMap H)
```

Proof:

```text
unfold S2429CompositeMap
exact S2430MonoCastComp_general H.R1.g0 H.R2.g0 H.R1.mono H.R2.mono H.middle_eq
```

`#check @S2430CompositeMap_mono` confirms the type is exactly the target
`Mono (S2429CompositeMap H)` (with the same implicit `A B C g1 g2`).

## Why direct `cases H.middle_eq` fails

`H.middle_eq` is an index field of the structure `H`; the goal mentions
`H.R1.g0 ≫ (H.middle_eq ▸ H.R2.g0)` where both endpoints and both maps are
projections of the same `H`. Dependent elimination of the equality would have
to generalize the whole structure, which is not structural. Moving the
statement to arbitrary scheme objects makes the equality an ordinary variable
and the elimination structural — exactly the S2429 `S2429CastComp_general`
trick. No `Eq.ndrec`/`cast` massage, no extra hypothesis.

## Verification status

```text
statement_compiles : yes (EXIT=0, exact command above)
proof_body_checked : yes (olean emitted; no sorry/admit/axiom token in file)
kernel_closed      : yes (both theorems: axioms = propext, Classical.choice, Quot.sound)
target_accepted    : sub-lemma accepted (Mono of the composite map);
                     the parent target S2424CompositionRequired still needs
                     S2429CompositeMapIsoRequired (map iso), untouched here.
```

Axiom check probe (scratch file, deleted after the run):

```text
'...S2430MonoCastActual.S2430MonoCastComp_general' depends on axioms: [propext, Classical.choice, Quot.sound]
'...S2430MonoCastActual.S2430CompositeMap_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## CONCURRENCY NOTE (important for the parent)

While this task ran, `S2429CompositeAssemblyActual.lean` was rewritten by
another agent: it was 100 lines when first read at task start, 113 lines at
03:04:12, and 116 lines at 03:07:54. The current version already contains

- `S2429MonoCastComp` (the same general lemma), and
- `S2429CompositeMap_mono` (the same target statement),

and it changed the consumer signatures: `S2424CompositeOfMapIso` and
`S2424CompositionRequired_of_mapIso` no longer take an `hmono` argument (they
use the file-local mono proof).

This task did **not** edit S2429's source; it only rebuilt its `.olean` from the
current source. `S2430CompositeMap_mono` is proved independently and has the
same type as the concurrent `S2429CompositeMap_mono` (`#check` on both), so it
is a drop-in replacement for the old `hmono` premise; there is no name clash
(different namespaces).

If the old 100-line S2429 is restored, S2430 still compiles: it depends only on
`S2429CompositeMap`, whose definition is identical in both versions.

## Exact first missing (unchanged by this task)

```text
S2429CompositeMapIsoRequired H
  = Nonempty (Iso
      (S2403CastHom H.R1.source_fiber_eq H.R2.target_fiber_eq
        (S1641CoverMapComp g1 g2).map)
      (S1742StrongTransOfHom (F := S1726K) (S2429CompositeMap H)))
```

## Next executable subgoal

Compose the two `map_iso` fields through the middle representable schemes, then
identify `vcomp (S1742StrongTransOfHom g1.g0) (S1742StrongTransOfHom g2.g0)`
with `S1742StrongTransOfHom (S2429CompositeMap H)` via
`S2398HomOfStrongTrans_vcomp` and `S1742StrongTransIsoOfHom`; that closes
`S2429CompositeMapIsoRequired H` and, with `S2430CompositeMap_mono`,
`S2424CompositionRequired H`.
