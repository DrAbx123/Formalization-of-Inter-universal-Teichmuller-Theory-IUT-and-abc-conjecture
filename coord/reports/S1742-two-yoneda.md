# S1742: actual 2-Yoneda comparison for representable etale pseudofunctors

Layer: O / representability of category-valued etale stacks.
Source object: `Iut.schemeRepresentableEtalePseudofunctor F S`
(`Iut/Foundations/Orbicurve.lean`, `schemeRepresentableFiberFunctor` lifted by
`Functor.toPseudofunctor'`).
Domain: actual Mathlib `Pseudofunctor.StrongTrans`, `Cat`, `Discrete`,
`LocallyDiscrete`; no cover category, no smallness assumption, no `Shrink`,
no `ULift` coercion of the data.
Direction: closes the 2-Yoneda comparison that S1733 listed as one of its three
exact missing interfaces (S1733 lines 38-42).

## Question

For a field `F` and `S T : Over (Spec F)`, construct both directions of

```
Pseudofunctor.StrongTrans (schemeRepresentableEtalePseudofunctor F S)
  (schemeRepresentableEtalePseudofunctor F T)   (up to 2-iso)
<->  S ⟶ T     (in Over (Spec F))
```

and prove them mutually inverse.

## Built (actual, no sorry / no axiom)

File: `tmp/sheaf/xif/paper/S1742TwoYonedaActual.lean`,
namespace `LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual`.

- `S1742YS`: abbreviation for the representable pseudofunctor.
- `S1742YS_map`, `S1742Fiber_map_obj`, `S1742Comp_toFunctor_obj`: the three
  definitional unfolding lemmas (`rfl`) for `toPseudofunctor'` of the
  representable fiber functor and for composition in `Cat`.
- `S1742App f`: `app` component at `U` is
  `Discrete.functor (fun P : U ⟶ S => Discrete.mk (P ≫ f))`, i.e. postcomposition
  with `f`.
- `S1742Nat f`: strong naturality 2-isomorphism in `Cat`, an `eqToIso` of
  functors whose object comparison is `Category.assoc`; the coherence fields
  (`naturality_naturality`, `naturality_id`, `naturality_comp`) are the actual
  `StrongTrans` fields, closed by subsingleton arguments on `Discrete`
  categories (they are not assumptions).
- `S1742StrongTransOfHom : (S ⟶ T) → StrongTrans (repr S) (repr T)`.
- `S1742HomOfStrongTrans eta`: the underlying scheme morphism, the image of the
  identity section `𝟙 S` under `eta.app` at `S`
  (`((eta.app (op S)).obj ⟨𝟙 S⟩).as : S ⟶ T`), with the definitional computation
  rule `S1742HomOfStrongTrans_def`.
- `S1742HomOfStrongTrans_strongTransOfHom`: the round trip is strict for scheme
  morphisms (`𝟙 S ≫ f = f`).
- `S1742Key`: strong naturality at the identity section forces
  `((eta.app a).obj ⟨P⟩).as = P ≫ S1742HomOfStrongTrans eta` for every test
  object `a` and section `P`. This is the substantive direction: it uses the
  strong naturality 2-isomorphism of the given `StrongTrans` at the map
  `P.op` of the site, evaluated at `𝟙 S`.
- `S1742AppEq`: consequently every `app` component is that of
  `S1742StrongTransOfHom (S1742HomOfStrongTrans eta)`.
- `S1742StrongTransIsoOfHom`: the reverse round trip is an actual 2-isomorphism
  `S1742StrongTransOfHom (S1742HomOfStrongTrans eta) ≅ eta` (an `Iso` in the
  category of strong transformations, built with
  `Pseudofunctor.StrongTrans.isoMk`).
- `S1742HomOfStrongTrans_congr`: the reverse direction is well defined on
  2-isomorphism classes.
- `S1742TwoYoneda_comparison`: the packaged conjunction of both round trips.
- Section 6 has target-locked `example`s whose types are written out with
  `Iut.schemeRepresentableEtalePseudofunctor F S` and
  `Iut.schemeRepresentableEtalePseudofunctor F T`, so the match with the S1733
  statement is checked by elaboration.

## Evidence

Lean: `tmp/sheaf/xif/paper/S1742TwoYonedaActual.lean` (220 lines).

- command: `lake env lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1742TwoYonedaActual.olean tmp/sheaf/xif/paper/S1742TwoYonedaActual.lean`
- EXIT=0
- SHA256 `13B06077D3D9C219D64611EB254F4F6C081469BEE00224349976BE1FD603D0B4`
- olean `D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S1742TwoYonedaActual.olean`
  (177600 bytes, 2026-11-01 00:25:44).
- axiom audit (`tmp/sheaf/xif/paper/_S1742AxiomCheck.lean`, EXIT=0):
  `S1742StrongTransOfHom`, `S1742HomOfStrongTrans_strongTransOfHom`,
  `S1742Key`, `S1742AppEq`, `S1742StrongTransIsoOfHom`,
  `S1742HomOfStrongTrans_congr`, `S1742TwoYoneda_comparison` all depend only on
  `propext`, `Classical.choice`, `Quot.sound`.

## Exact missing

None for this comparison: both directions and both round trips are constructed.
The 2-isomorphism direction is an `Iso` of strong transformations; there is no
residual coherence obligation.

## Honest boundary

- This is the 2-Yoneda comparison for two *representable* pseudofunctors, i.e.
  for the full subcategory of `Hom(S, -)`. It is not the general 2-Yoneda lemma
  for an arbitrary target pseudofunctor, which is not needed for S1733.
- It does not identify strong transformations with actual S1728 cover maps, and
  does not prove essential smallness of the cover category; those remain S1733's
  separate missing theorems `S1733AffineCoverModelMissing` and
  `S1733CoverSliceEquivalence`.
- `S1742HomOfStrongTrans` uses `Classical.choice` only through Mathlib's
  `Discrete`/`Cat` API; no data is chosen by hand.

## Consumer

S1733 (2-Yoneda comparison item) and any later use of representability of the
representable etale stack (S1674-type stack lifts, S1728/S1733 cover category
comparison). It removes the "2-Yoneda comparison from strong transformations of
representable stacks to scheme morphisms" gap listed verbatim in S1733.
