# S2012: the comparison of the pushed-forward descent data with the C-side comparison

Date: 2026-11-01

## Artifacts

- Lean file: `tmp/sheaf/xif/paper/S2012EffectivityComparisonActual.lean`
  - SHA256 `4C5137DA829F7F5913F2C745F679FCEC02A62E1E7503C50EB30FECF54A761AFE`
  - 19,968 B, 340 lines
  - `lake env lean` EXIT=0 (no warnings, no `sorry`, no `axiom`)
- olean: `.lake/build/lib/lean/tmp/sheaf/xif/paper/S2012EffectivityComparisonActual.olean`
  - 273,760 B, SHA256 `84C260247FB49BCDEB8C1B8CB77F62598DEC1AEC4040E7BEAA3BCDBC025E391D`
- Axioms of every declared result: exactly `propext`, `Classical.choice`, `Quot.sound`
  (`#print axioms` block at the end of the file).

## Status against the task

`S2004ComparisonStatement` is **not** proved and is **not** faked.  No `sorry`,
no new axiom, no change of target, no `Shrink`/`ULift`/`PUnit`.

Proved in the file (all with the axiom trio only):

1.  `S2012mapComp'_hom_app` -- the component formula for the flexible comparison
    `mapComp'`: it is the `mapComp` comparison preceded by the `map₂` adjustment
    along the equation of arrows.
2.  `S2012natComp_nat2_hom` / `S2012natComp_nat2_inv` -- the componentwise
    2-naturality of the strong naturality comparison with respect to a 2-cell of the
    site (`hom` and `inv` forms).
3.  **The primed pasting identities** `S2012natCompInvApp_comp'` and
    `S2012natCompHomApp_comp'` -- the versions of the S1935 componentwise coherences
    `natCompInvApp_comp` / `natCompHomApp_comp` for `mapComp'`, i.e. exactly the
    coherences needed when the `DescentData.ofObj` hom (which is built from
    `mapComp'`) is compared with the push-forward hom (which is built from
    `α.naturality`).  Each is derived from the S1935 lemma for `mapComp` plus 1 and 2.
4.  The candidate comparison components, i.e. the inverse of the S1864/S1998
    comparison `S1864SiteComparisonLeft` read at the object
    (`S2012toNatIso_symm_app_hom/inv`), and the componentwise push comparison
    `S2012PushComponent` (with its `hom` formula).
5.  **The reduction** `S2012Comparison_of_statements`: the two general statements
    `S2012PushToDescentDataStatement` and `S2012PushFunctorialityStatement` imply
    `S2004ComparisonStatement`.  This is the mathematically meaningful content of
    step (b'): the desired iso is
    `(C.toDescentData _).obj ((f.map.app _).obj a)`
      `≅ S2004PushDescentData f.map ((A.toDescentData _).obj a)`  (the general comparison)
      `≅ S2004PushDescentData f.map (S2004FstDescentData f g D) = S2004MidF f g D`
      (the push-forward of the iso supplied by the `A`-stack).

## Exact first missing

`S2012PushToDescentDataStatement`: for every strong transformation `α : F ⟶ G` of
pseudofunctors `LocallyDiscrete Siteᵒᵖ ⟶ Cat` and every `M : F.obj (U S)`, an
isomorphism of `G`-descent data

  `(G.toDescentData _).obj ((α.app (U S)).obj M) ≅ S2004PushDescentData α (F.toDescentData _ M)`

with the components (4).  The single proof obligation is the compatibility of these
components with the `hom` fields, i.e. the commutativity of

  `(G.map f₁).map (e i₁).hom ≫ (G.mapComp' φ₂ f₂ q).hom
      = (G.mapComp' φ₁ f₁ q).inv ≫ (G.map f₂).map (e i₂).hom`

in the orientation `D₁ = (G.toDescentData _).obj M`, `D₂ = S2004PushDescentData α _`
(notation `φ_i = (f i).op.toLoc`, `φ_i ≫ f_i.op.toLoc = q.op.toLoc`).

Second missing: `S2012PushFunctorialityStatement` -- the push-forward is functorial
in the descent datum (an iso `D₁ ≅ D₂` induces `S2004PushDescentData α D₁ ≅
S2004PushDescentData α D₂`).  It needs no `mapComp'` manipulation; a full paper
proof was worked out (the two naturalities of `α.naturality` at `e.hom.hom i₁` and
`e.hom.hom i₂`, then `e.hom.comm` and `Functor.map_comp`), and the componentwise
construction is already in the file as `S2012PushComponent`; only the final
associativity bookkeeping of the `comm` field did not close in the time available.

## Technical findings for the continuation

- The proof of the `comm` field is a four-fact computation:
  (i) the naturality of `(α.naturality f₁).inv` at `e.hom.hom i₁`,
  (ii) the naturality of `(α.naturality f₂).hom` at `e.hom.hom i₂`,
  (iii) the primed pasting identities of this file (both directions), and
  (iv) the cancellation `(α.app _).map (FC.hom) ≫ (α.app _).map (FC.inv) = 𝟙` for
  the `f`-side comparison (and the analogous cancellation for `(G.map f₂).map e₂`).
- The *forward* orientation (`D₁ = push`, `D₂ = toDescentData`) needs an
  **inversion** of the primed pasting identity (`S2012natCompInvApp_comp'` with
  `map (e i₁).hom` and `GC₁.inv`); the *reverse* orientation instead needs the
  insertion `≫ (F.mapComp' φ₂ f₂ q).hom ≫ (F.mapComp' φ₂ f₂ q).inv` before applying
  `S2012natCompHomApp_comp'`.  The reverse orientation is the one needed by
  `S2004ComparisonStatement` and is the one to pursue.
- The obstruction that stopped this package is the `Cat`-versus-`Bundled Category`
  transparency issue of the `𝟙`-typed unit laws: `rw [Category.comp_id]`
  (pattern `?f ≫ 𝟙 ?X`) fails with "Application type mismatch: the argument
  `G.obj (U Y)` has type `Cat` but is expected to have type `Bundled Category`",
  and `erw`/full `simp` rewrite but leave the object-form mismatch
  `(α.app (U Y)).obj ((F.map q).obj M)` versus
  `((F.map q ⋙ α.app (U Y)).obj M)` unsolved (these are `rfl`-equal when the
  transparency option is not disabled, but the project's
  `backward.isDefEq.respectTransparency false` is needed for the `simpa` steps of
  `S2012natComp_nat2_hom`, so the two cannot be used in the same declaration as is).
  Suggested next move: state the cancellations in the `Iso.hom_inv_id_assoc` form
  (with an explicit trailing factor, e.g. `AMAPF1H ≫ AMAPF1I ≫ AMAPF2H = AMAPF2H`)
  so that the `𝟙` never has to be transported across the two object forms.

## Untouched

`coord/STATE.md`, `coord/queue.md`, `AUDIT_LEDGER.md` were not modified by this
package; the parent agent owns the integration.
