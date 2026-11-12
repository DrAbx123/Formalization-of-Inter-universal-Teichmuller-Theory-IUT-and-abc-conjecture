# S2004: iso-comma effectivity -- push-forward of descent data and the middle comparison

Date: 2026-11-01

## Artifacts

- Lean file: `tmp/sheaf/xif/paper/S2004IsoCommaEffectivityActual.lean`
  - SHA256 `CE4C9FD458DDB91C2F354853CBE255883B8416E3EC7B8A7602529737798AAEDA`
  - 419 lines
  - `lake env lean` EXIT=0 (0 warnings, no `sorry`, no `axiom`)
- olean: `.lake/build/lib/lean/tmp/sheaf/xif/paper/S2004IsoCommaEffectivityActual.olean`
  - 1,150,896 B, SHA256 `DC1DCD2EAFBFFAC71DFAD102BCC4FF6A2E7E473CDEDEE8ADA36256A2F9150CD6`
- Axioms of every declared result: exactly `propext`, `Classical.choice`, `Quot.sound`
  (`#print axioms` block at the end of the file).

## Status against the task

The target `S1956IsoCommaEffectivity f g` is **not** proved and is **not** faked.
No `sorry`, no new axiom, no change of target, no `Shrink`/`ULift`/`PUnit`.

Proved in the file (all with the axiom trio only):

1. `S2004Push_coherence` -- the two-legged componentwise coherence of the naturality
   comparison of an arbitrary strong transformation `α : F ⟶ G` of pseudofunctors
   `LocallyDiscrete Siteᵒᵖ ⟶ Cat`.  It is the two-legged generalization of
   `S1988HComponent_pullHom` (S1988 is the one-legged case; the descent-data axiom
   needs two *different* restriction legs).  The proof assembles the two S1935
   component coherences `natCompInvApp_comp_mapComp'`, `natCompHomApp_comp_mapComp'`
   and the naturality of the comparison itself, by an explicit associativity and
   cancellation computation.
2. `S2004PushDescentData` -- a strong transformation sends descent data to descent
   data: for `D : F.DescentData (fun i => i.obj.hom)` the transported
   `G.DescentData`, with all three axioms `pullHom_hom`, `hom_self`, `hom_comp`
   proved (from 1 and from the unit/cancellation laws of the comparisons).
3. `S2004Fst_pullHom_raw`, `S2004FstDescentData` and their `Snd` analogues -- the
   A- and B-side descent data underlying a descent datum of the iso-comma
   pseudofunctor, extracted through the two jointly faithful iso-comma projections
   (using the `rfl`-strict projection lemmas `S1956Fst_mapComp'`, `S1956Fst_map`, ...,
   of S1956).
4. `S2004MidF`, `S2004MidG` -- the `f`-side and `g`-side `C`-descent data of `D`.
5. `S2004MidComparison` (`S2004MidF f g D ≅ S2004MidG f g D`) -- **the middle
   comparison**: the comma structure isomorphisms `(D.obj i).obj.hom` are a morphism
   of `C`-descent data.  The proof shows that the `comm` condition is *equivalent* to
   the comma condition `(D.hom q f₁ f₂).hom.w` after conjugation by the two
   comparison isomorphisms `S1864SiteComparisonLeft/Right` (and `S1998ObjHom`), and
   then performs the cancellation.

## Exact first missing

`S2004ComparisonStatement` (a `Prop`, no inhabitant): for every descent datum `D` of
the iso-comma pseudofunctor and every effective `A`-descent datum
`a` with `(A.toDescentData _).obj a ≅ S2004FstDescentData f g D` (supplied by the
`A`-stack) there is an isomorphism of `C`-descent data

  `(C.toDescentData _).obj ((f.map.app _).obj a) ≅ S2004MidF f g D`.

After it, two further unformalized steps remain: the same statement on the `g`-side,
then the reassembly: fullness of `C.toDescentData` (the `C`-stack is a prestack)
produces `(f.map.app _).obj a ≅ (g.map.app _).obj b`, and the resulting iso-comma
object `(a, b, h)` must then be shown to map to `D` under `toDescentData`
(`DescentData.isoMk` with the `A`/`B` components and the comma condition at each
index).  Only (b) is stated (`S2004ComparisonStatement`); (c) is not even stated.

Consequently `S1956IsoCommaStack f g` is still open as well (S1998's consumer
`S1956IsoCommaEffectivity f g → S1956IsoCommaStack f g` stays conditional).

## Technical notes for the continuation

- The file sets `set_option backward.isDefEq.respectTransparency false` **globally**:
  several of the coherence computations (`S2004Push_coherence`, `S2004MidComparison`)
  need it, while the `pullHom_hom`/`hom_comp` proofs of `S2004PushDescentData` need
  the default transparency.  Both work in the same file only because the conflicting
  steps use `erw` and full `simp` (see below).
- Pointwise cancellation of two adjacent comparison components often fails with `rw`
  because the target is not type-correct at the `instances` transparency level
  (`Cat` vs `Bundled Category.{0,0}`); `erw` and full `simp` succeed there.
- `S1998ObjHom` must be applied with an explicit `have` whose type is written with the
  concrete restriction `f₁.op.toLoc` (a direct `rw [S1998ObjHom ...]` does not match
  because of the `Opposite.unop (Opposite.op ...)`/`Over.mk` bookkeeping).
- The candidate for `S2004ComparisonStatement` is the family
  `(S1864SiteComparisonLeft f (i.op.toLoc)).hom.app a`; its `comm` condition is the
  compatibility of the comparison isomorphisms with the descent hom `ofObj` formula
  (`DescentData.ofObj`), the same kind of computation as in `S2004MidComparison`.

## Untouched

`coord/STATE.md`, `coord/queue.md`, `AUDIT_LEDGER.md` were not modified by this
package; the parent agent owns the integration.
