# S1641: actual cover-map composition — constructed; Category still missing

Date: 2026-10-31
Lean: `tmp/sheaf/xif/paper/S1641CoverMapCompositionActual.lean`
EXIT=0 (composition constructed; no Category/skeleton inhabitant)
SHA256 `D2EBCC3ACF65CB9F5A4813502D2EB6A16BC71F91E547E599281199EB76B15D02`
olean: `D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S1641CoverMapCompositionActual.olean`

## Constructed (actual, no fake data)

For `Iut.OrbicurveFiniteEtaleCover X` over any `X : HyperbolicOrbicurve F`:

* `S1641CoverMapAssociator f g`:
  `Iso (vcomp (vcomp f.map g.map) C.map) (vcomp f.map (vcomp g.map C.map))`,
  the `Pseudofunctor.StrongTrans.associator` of the three strong transformations.
* `S1641CoverMapWhisker f g`:
  `Iso (vcomp f.map (vcomp g.map C.map)) (vcomp f.map B.map)`,
  `Bicategory.whiskerLeftIso f.map g.commutes`.
* `S1641CoverMapCompCommutes f g`:
  the trans of the two, then `f.commutes`, i.e.
  `(S1641CoverMapAssociator f g) ≪≫ (S1641CoverMapWhisker f g) ≪≫ f.commutes`.
* `S1641CoverMapComp f g : OrbicurveFiniteEtaleCoverMap A C` with
  `map = vcomp f.map g.map` and `commutes = S1641CoverMapCompCommutes f g`.
  This inhabits the exact S1631 missing composition.
* `S1641CoverMapId A : OrbicurveFiniteEtaleCoverMap A A` with
  `map = StrongTrans.id`, `commutes = StrongTrans.leftUnitor A.map`.
* `S1641CoverMapComp_commutes_hom_app` / `_inv_app` (both `rfl`):
  the composite commuting 2-cell is componentwise
  `(α_ f.map.app a g.map.app a C.map.app a).hom ≫
     (f.map.app a ◁ g.commutes.hom.as.app a) ≫ f.commutes.hom.as.app a`
  (and the inverse formula in reverse order).  This is the target 2-cell
  exchange: the composite comparison is exactly the associator plus the two
  old comparisons.
* `S1641CoverMapComp_commutes_decomposition` (`rfl`): the target
  decomposition into associator / whiskered `g.commutes` / `f.commutes`.

## Category attempt — exact first missing

`S1641CoverCategoryStruct : CategoryStruct (OrbicurveFiniteEtaleCover X)` with
`Hom := OrbicurveFiniteEtaleCoverMap`, `id := S1641CoverMapId`,
`comp := S1641CoverMapComp` is written.  The three law targets are

* `S1641IdCompLaw`, `S1641CompIdLaw`, `S1641AssocLaw` (`: Prop`).

No inhabitant is produced.  Any proof would force, on the `map` fields,

* `S1641StrictLeftUnitor`:  `vcomp (StrongTrans.id A.source.fiber) f.map = f.map`,
* `S1641StrictRightUnitor`: `vcomp f.map (StrongTrans.id B.source.fiber) = f.map`,
* `S1641StrictAssociator`:  `vcomp (vcomp f.map g.map) h.map =
                              vcomp f.map (vcomp g.map h.map)`.

The implications are proved (`S1641IdCompLaw_strictLeftUnitor`,
`S1641CompIdLaw_strictRightUnitor`, `S1641AssocLaw_strictAssociator`).
These strict equalities are 1-morphism equalities; Mathlib supplies only the
associator/unitor *2-isomorphisms*, so the bicategory data does not give them
(and the full laws would additionally need the corresponding `commutes`
comparison coherence).  This is the exact first missing coherence; no Category,
skeleton, `Shrink`, `ULift`, or fake carrier is inserted.

The original 0/1 interface has a second, independent obstruction:
`OrbicurveFiniteEtaleCoverMap : Type 1`, while `Category.{0,1}` needs a Type 0
Hom carrier.  `S1641SmallHomData` records exactly that missing carrier;
`S1641Category01Required` is `Category.{0, u+1}` and
`S1641Category11Required` is `Category.{u+1, u+1}` (for the paper field,
`Category.{0,1}` and `Category.{1,1}` respectively).

## S1631 specialization

`S1641Paper.S1641S1631Composition (l : PrimeGeFive) :
  S1631CompositionRequired (l := l)`

is an actual inhabitant of S1631's missing composition functional for the
S1522/S1562 paper orbicurve.  `S1641Paper.S1641S1631Id_eq` proves (by `rfl`)
that the identity constructed here is S1631's `S1631Id` (the S405 `idMap`).

## Axioms

`#print axioms` on `S1641CoverMapComp`, `S1641CoverMapComp_commutes_hom_app`,
`S1641IdCompLaw_strictLeftUnitor`, `S1641Paper.S1641S1631Composition`, and
`S1641Paper.S1641S1631Id_eq` reports only
`propext, Classical.choice, Quot.sound`.  No `sorry`/`admit`/new axiom.

## Remaining gap / next step

1. For `Category.{1,1}` with the raw cover maps: prove or refute the strict
   unitality/associativity equalities above (equivalently, strictify the
   Cat-valued pseudofunctor bicategory at these objects), or replace `Hom` by
   the 2-cell quotient so the laws hold on the nose (this changes
   `coverMorphism_bijective` to a section/quotient statement).
2. For `Category.{0,1}`: a Type 0 Hom carrier equivalent to `CoverMap`
   (`S1641SmallHomData`), which is not available without `Shrink`/`ULift`.
