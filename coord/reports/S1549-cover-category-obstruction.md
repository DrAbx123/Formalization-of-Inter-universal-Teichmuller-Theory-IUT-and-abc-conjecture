# S1549: cover category universe obstruction / exact first missing

Date: 2026-10-31
Lean: tmp/sheaf/xif/paper/S1549OrbicurveCoverCategoryProofActual.lean
EXIT=0 (missing/exact; no Category inhabitant).
SHA256 E80CCEFD39174A4F4F7678DFEA491E895DF47AD4B0F342B742D356613579C76A
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S1549OrbicurveCoverCategoryProofActual.olean

## Actual

S1549Cover l = OrbicurveFiniteEtaleCover (S1419Orbicurve l) : Type 1;
S1549CoverMap A B = OrbicurveFiniteEtaleCoverMap A B : Type 1.
S1419 orbicurve actual nonterminal, once-punctured signature.

## Obstruction

The S1522/S1529 field is
  Category.{0,1} (OrbicurveFiniteEtaleCover X),
so its Hom family must live in Type 0.  The actual over-map type
OrbicurveFiniteEtaleCoverMap lives in Type 1.  A Category instance cannot
use the literal over-map type as Hom; it needs a small Hom carrier with an
equivalence to the over-map type, plus the unitors/associators coherence.

## Exact first missing

S1549SmallHomFirstMissing l:
  Hom : Cover -> Cover -> Type
  homEquiv : forall A B, Hom A B ≃ CoverMap A B.
No inhabitant.

S1549CoverCategoryFirstMissing l := Category.{0,1} (S1549Cover l).
No inhabitant.

No group product model, l-torsion sequence, terminal or point fiber is used.
The naive id/comp attempt was not inserted as a fake Category.