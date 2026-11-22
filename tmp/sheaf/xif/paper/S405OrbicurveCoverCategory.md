# S405: orbicurve finite-etale cover category attempt

Date: 2026-10-29. No paper claim. No fake category/coherence.

## Actual data

* Objects: OrbicurveFiniteEtaleCover X.
* Hom: OrbicurveFiniteEtaleCoverMap source target, with
  map : source.source.Hom target.source and
  commutes : Iso (StrongTrans.vcomp map target.map) source.map.

## Constructed

idMap A : OrbicurveFiniteEtaleCoverMap A A:
* map := StrongTrans.id A.source.fiber;
* commutes := StrongTrans.leftUnitor A.map (after the local
  EtaleStackPseudofunctor homCategory instance).
This is an actual identity morphism.

## Exact missing

A composition
  compMap f g : OrbicurveFiniteEtaleCoverMap A C
must have
  map := StrongTrans.vcomp f.map g.map
and a commutes Iso obtained by whiskering/composing g.commutes and
f.commutes through the StrongTrans associator.  The pseudofunctor
StrongTrans bicategory supplies associator/left/right unitors only as
isomorphisms, not as the strict equalities required by Category
(id_comp, comp_id, assoc).  Moreover the cover-map commutes fields are Isos,
so even a CategoryStruct needs a chosen strictification/coherence.

Recorded exact requirement:
OrbicurveCoverCategoryGap X:
* categoryStruct : CategoryStruct (OrbicurveFiniteEtaleCover X);
* id_comp, comp_id, assoc : Prop.
OrbicurveCoverCategoryRequired X := Nonempty gap; no inhabitant.

No category instance, composition, tau, completion root or L is fabricated.
