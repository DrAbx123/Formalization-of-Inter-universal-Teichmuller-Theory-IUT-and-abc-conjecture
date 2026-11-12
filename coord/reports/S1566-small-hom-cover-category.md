# S1566: small Hom carrier and faithful universe correction

Date: 2026-10-31
Lean: tmp/sheaf/xif/paper/S1566SmallHomCoverCategoryActual.lean
EXIT=0 (missing/exact; no Category inhabitant).
SHA256 A259F091F41B060BB6912E31721CC53E863D31E06EF6152CDC4D4712C63022F2
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S1566SmallHomCoverCategoryActual.olean

## No small carrier constructed

Actual cover maps: S1566CoverMap A B : Type 1.
No Type 0 Hom carrier with an equivalence to the actual maps is
constructed.  Shrink/ULift are not used; Shrink is not accepted as a
construction.

S1566SmallHomData l:
  Hom : Cover -> Cover -> Type
  homEquiv : forall A B, Hom A B ≃ CoverMap A B.
No inhabitant.

## Faithful correction

The universe-matched interface is
S1566CorrectedFirstFields l:
  coverCategory : Category.{1,1} Cover;
  galoisCategory : letI := coverCategory;
    @GaloisCategory.{1,1} Cover coverCategory.
No inhabitant; Category.{1,1} has object universe 1 and hom universe 1,
matching CoverMap Type 1.

## Exact types

S1566OriginalCategoryRequired l := Category.{0,1} Cover (Type 1);
S1566CorrectedCategoryRequired l := Category.{1,1} Cover (Type 2);
S1566SmallHomRequired l := S1566SmallHomData l;
S1566CorrectedFirstFieldsRequired l := S1566CorrectedFirstFields l.

No Shrink/ULift, no fake Category, no group product/l-torsion/terminal.

## Conclusion

The original interface can only be filled by an additional small Hom
carrier; otherwise the faithful repair is Category.{1,1} (and the
corresponding GaloisCategory).  The correction changes the public universe
of Iut.OrbicurveEtaleFundamentalGroup.coverCategory, so it is an interface
change, not a proof of the original field.