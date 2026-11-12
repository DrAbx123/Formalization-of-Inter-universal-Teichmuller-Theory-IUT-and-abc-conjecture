# Cover category for S2482/S2495: ACTUAL

## BUILT (EXIT=0)
S2511CoverCategoryActual.lean:
- S2511CoverCategory : Category.{1,1} (OrbicurveFiniteEtaleCover S2482Orbicurve).
- S2511CoverCategoryCF : Category.{1,1} (OrbicurveFiniteEtaleCover S2495cF).
Via S1728CoverCategory11 (2-iso quotient of cover maps).
Axioms: propext, Classical.choice, Quot.sound; no sorryAx.

## Important universe caveat
The source OrbicurveEtaleFundamentalGroup field asks for `Category.{u} (OrbicurveFiniteEtaleCover X)`,
whereas the actual 2-iso-quotient category is Category.{u+1,u+1}. For S2482/S2495 we get Category.{1,1}.
So filling the source field directly needs a universe correction/relabelling, not fake data.

## Still missing
GaloisCategory, baseScheme/basePoint, fiber, fiberFunctor, coverMorphism, action, isFundamentalGroup;
then xFGroups/cFGroups/fGroupInclusion.
No fake.

## Artifacts
Lean: tmp/sheaf/xif/paper/S2511CoverCategoryActual.lean
EXIT=0; SHA256 21EDEF831BFDFD393C77AD43D8A250CE5C60B5EAB8AEFA8B9A787860AF3AFF1C
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2511CoverCategoryActual.olean
olean SHA256: 1DE53CD6CD031872AD61E356A940DC335D5488DD78A3F39EE1ACA462394E2AC0
axioms: trio