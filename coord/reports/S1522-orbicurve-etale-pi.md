# S1522: OrbicurveEtaleFundamentalGroup first missing

Date: 2026-10-31
Lean: tmp/sheaf/xif/paper/S1522OrbicurveEtalePiActual.lean
EXIT=0; SHA256 71CDF9C5707D566D5C3331833F2DDA4940C4EE46F26AE80D6DD03DB25B3278B4
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S1522OrbicurveEtalePiActual.olean

## Actual

S1522Orbicurve l := S1419Orbicurve l : HyperbolicOrbicurve (S1348K l),
actual nonterminal and once-punctured elliptic signature.

S1522GroupDataRequired l := S1511OrbicurvePiExactFirstField l:
OrbicurveFundamentalGroupData (S1419Orbicurve l) (AbsoluteGaloisProfinite (S1348K l)).

## Exact first missing structure

S1522GaloisCategoryFirstMissing l where
  coverCategory : Category (OrbicurveFiniteEtaleCover (S1522Orbicurve l));
  galoisCategory :
    letI := coverCategory;
    @GaloisCategory (OrbicurveFiniteEtaleCover (S1522Orbicurve l)) coverCategory.

No inhabitant is asserted.  The full certificate type is retained as
S1522EtalePiRequired l G := OrbicurveEtaleFundamentalGroup (S1522Orbicurve l) G.

Every full certificate gives the first missing structure by projection:
S1522GaloisCategoryFirstMissing_of_etalePi D.

## Group-level projection (not certificate)

S1490ModelProjection l is surjective onto AbsoluteGaloisProfinite (S1348K l),
but it is the product model G_K x freeProfiniteGroupTwo, not a finite-etale
certificate and not inserted into the group data.

No l-torsion/terminal/point fiber substitute.