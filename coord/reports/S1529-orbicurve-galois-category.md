# S1529: Orbicurve Galois category exact first missing

Date: 2026-10-31
Lean: tmp/sheaf/xif/paper/S1529OrbicurveGaloisCategoryActual.lean
EXIT=0; SHA256 32CD492A8184D25FD653E2BB43A82A2E23D9B361897F0614E29D17BAC5FB8F21
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S1529OrbicurveGaloisCategoryActual.olean

## Exact first missing

S1529CoverCategoryFirstMissing l:
  coverCategory : Category.{0,1} (OrbicurveFiniteEtaleCover (S1522Orbicurve l)).
No inhabitant asserted.

Remaining exact inputs for that category:
S1529GaloisCategoryRemaining l C with
  sourceG2 : SourceG2 l C (all finite-group SingleObj colimits),
  otherInputs : terminal/pullbacks/finite coproducts/mono-direct-summand,
  fiberFunctor : exists F : S1529Cover l -> FintypeCat.{0}, FiberFunctor F.

## Conditional actual construction

S1529GaloisCategory l C R :
  @GaloisCategory.{1,0} (S1529Cover l) C.coverCategory,
from the PreGaloisCategory fields and fiberFunctor.

S1529S1522FirstMissing l C R :
  S1522GaloisCategoryFirstMissing l.

## Scope

The actual cover type is the S1419 OrbicurveFiniteEtaleCover.  The category
instance on it is still the missing input; no group product model, l-torsion,
or terminal/point fiber is used.  The group-level product projection of S1490
is not used here.

Lemmas are conditional; no inhabitant of the cover category is claimed.