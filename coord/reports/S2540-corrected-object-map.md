# S2540 corrected object map/functor: ACTUAL

## BUILT (EXIT=0)
S2540CorrectedObjectMapActual.lean:
- S2540ObjectMap : CommAlgCat.FiniteEtale S2482CoordinateRing -> OrbicurveFiniteEtaleCover S2482Orbicurve.
  via S2538AffineCoverEquiv.inverse then S2519InvFunctor.obj.
- S2540Functor : (FiniteEtale S2482CoordinateRing)^op ⥤ OrbicurveFiniteEtaleCover S2482Orbicurve
  = S2538AffineCoverEquiv.inverse ⋙ S2519InvFunctor.
Axioms trio; no sorryAx.

## Correction
The previous S2533 domain FiniteEtale F is not the correct algebra side for the base cover:
base change along F -> S2482CoordinateRing can lose F-structure. The correct domain is
FiniteEtale S2482CoordinateRing, matching S2538.
No fake.

## Artifacts
EXIT=0; SHA256 74935B21BD422D4961740A7C600FE0C9FE0CE76C93FFF564E31B7C20E9577D8F
olean SHA256: 5268C663672A3CC4EA2AB5AE6004D4B1FD390EFCAAAA79E0BBA88B89BF521AA4
axioms: trio