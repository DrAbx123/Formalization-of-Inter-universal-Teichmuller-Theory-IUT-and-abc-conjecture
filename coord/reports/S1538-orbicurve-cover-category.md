# S1538: Orbicurve cover category exact first missing

Date: 2026-10-31
Lean: tmp/sheaf/xif/paper/S1538OrbicurveCoverCategoryActual.lean
EXIT=0; SHA256 8EEDBF37CFFB45F338120596B3A98B57DECD9BD96256F137133BF8BAA0817832
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S1538OrbicurveCoverCategoryActual.olean

## Actual

S1538Cover l := S1529Cover l = OrbicurveFiniteEtaleCover (S1419Orbicurve l),
with the actual over-map object structure (source, map, finiteEtale).
The S1419 orbicurve is actual nonterminal with once-punctured signature.

## Exact first missing

S1538CoverCategoryFirstMissing l := Category.{0,1} (S1538Cover l).
No inhabitant.  The identity/composition coherence of
OrbicurveFiniteEtaleCoverMap (its commutes 2-isomorphism) is exactly the
missing category structure; the cover type itself is actual.

S1538CategoryStructOfCategory C exposes only the CategoryStruct component
of a hypothetical Category, not an inhabitant.

S1538GaloisCategoryRemainingRequired l :=
forall C, S1529GaloisCategoryRemaining l C (Prop), no inhabitant.

## Not used

No group product model, l-torsion sequence, terminal or point fiber is used.
No group-level projection is inserted.

This is a missing package: coverCategory construction is not claimed.