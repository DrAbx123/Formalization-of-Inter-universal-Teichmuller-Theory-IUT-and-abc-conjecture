# S1728: actual small cover category — quotient category constructed; exact first missing

Date: 2026-10-31

Lean: tmp/sheaf/xif/paper/S1728CoverCategoryActual.lean

EXIT=0

SHA256: 255D3A978FBCB7DC818E2E8F6E6D97042A39304973B31CDD0523E5FC0B9198A6

olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S1728CoverCategoryActual.olean (366480 bytes)

## Actual constructions

* S1728CoverCategory11: an actual Category.{u+1,u+1} on
  OrbicurveFiniteEtaleCover X, whose homs are 2-isomorphism classes of the
  underlying strong transformations.  The strict category laws are obtained
  from the bicategory unitors/associator after quotienting; no strict
  unitor/associator equality is assumed.  For the S1726 orbicurve this is a
  genuine Category.{1,1} (S1728ActualCategory11).
* S1728CategoryOfHomEquiv and S1728ActualCategory01: transport a category
  structure along explicit small hom carriers.  Given, for every pair of
  actual covers, a Type 0 carrier equivalent to the actual cover-map type, this
  produces a genuine Category.{0,1} on the actual S1726 cover type.
* S1728ActualCategory01OfSmallGaloisModel: a small Galois model yields a
  genuine Category.{0,1} on the actual S1726 cover type.
* S1728SmallRawCoverDataOfEtaleFundamentalGroup and
  S1728SmallRawCoverDataOfEtalePi: any full
  OrbicurveEtaleFundamentalGroup implies small raw cover data for every pair.
* S1728SmallRawCoverDataOfSmallGaloisModel and
  S1728SmallRawCoverDataRequiredOfSmallGaloisModel: the small Galois model
  implies the same small raw cover data.

## Universe observations

* The actual cover-map type is Type 1 (S1728CoverMap).
* The 2-isomorphism quotient is Type 1 (S1728QuotUniverse).
* Core preserves object and hom universes (S1728CoreObject, S1728CoreHom).
* Pith preserves the object universe; its 1-cells are Core (a -> b), hence
  Type 1 for the etale-stack bicategory (S1728PithObject plus the checked
  example).
* Category.{0,1} has a Type 0 hom family; the literal cover-map type is Type 1.
  Hence a small carrier with an equivalence is required in any solution.

## Exact first missing

* S1728SmallRawCoverDataRequired: for every pair of S1726 covers, a Type 0
  carrier equivalent to the actual cover-map type.  No inhabitant.
* S1728CoverCategoryFirstMissing = Category.{0,1} S1728Cover.  No inhabitant.
* S1728GaloisCategoryFirstMissing = the coverCategory/galoisCategory pair.
  No inhabitant.

No GaloisCategory on the actual orbicurve cover category is constructed.  The
small Galois model carries a GaloisCategory on the small side, but the transfer
to the actual cover category is not formalized here.

## Paper input

S1728SmallGaloisModel records a small object type of covers, a Category.{0,0}
on it, an object equivalence to the actual S1726 cover type, hom equivalences
to the actual cover maps, and a GaloisCategory on the small side.  This is the
connected-cover smallness/classification input: connectedness of the orbicurve
plus the classification of finite etale covers by finite separable extensions
of the function field / finite quotients of the etale fundamental group.  No
inhabitant is constructed.

## Axiom audit

The #print axioms block reports only propext, Classical.choice and Quot.sound
for S1728ActualCategory11, S1728ActualCategory01,
S1728SmallRawCoverDataOfEtaleFundamentalGroup,
S1728CoverCategoryAndGaloisOfEtalePi,
S1728ActualCategory01OfSmallGaloisModel and
S1728SmallRawCoverDataRequiredOfSmallGaloisModel.  There is no sorry, no axiom,
no Shrink, no ULift, no PLift and no PUnit in the code.
