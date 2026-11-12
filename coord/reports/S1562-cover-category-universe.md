# S1562: coverCategory universe audit

Date: 2026-10-31
Lean: tmp/sheaf/xif/paper/S1562CoverCategoryUniverseActual.lean
EXIT=0 (audit/exact; no Category inhabitant).
SHA256 1CCC2579D46632AD4ACD776C4DE4FC7B79167FD989D125F7AB5518AA9A384F67
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S1562CoverCategoryUniverseActual.olean

## Source comparison

Local Iut/Foundations/Orbicurve.lean:
  coverCategory : Category.{u} (OrbicurveFiniteEtaleCover X)
with F : Type u. Both vendored promachina snapshots have the identical
declaration.  Hence the local structure is not a port-universe error.

For F = S1348K l (Type 0), u = 0, so Category.{0,1} (objects Type 1,
homs Type 0) is forced by the original interface.  S1522/S1529's
Category.{0,1} is therefore faithful, not a typo.

## Actual mismatch

OrbicurveFiniteEtaleCoverMap : Type 1, so it cannot be the Hom family of
Category.{0,1}.  The original field needs a small (Type 0) Hom carrier
with an equivalence to the actual over-maps, or the structure must be
corrected to Category.{u+1} (here Category.{1,1}).

## Exact first missing

S1562OriginalCoverCategory l := Category.{0,1} Cover;
S1562OriginalSmallHomFirstMissing l with Hom : Cover -> Cover -> Type and
homEquiv : Hom A B ≃ CoverMap A B.
S1562CorrectedCoverCategory l := Category.{1,1} Cover;
S1562CorrectedCategoryRequired l := Category.{1,1} Cover.

No inhabitant is asserted for either interface.  No Shrink/ULift carrier
and no fake Category.

## Conclusion

Not a port error.  The original structure itself chooses the small-hom
universe; a corrected interface with Category.{u+1} is the proposed fix,
but it would require changing Iut.OrbicurveEtaleFundamentalGroup and its
consumers.  S1549 is therefore a genuine missing/interfaces item.