# S1568: small cover skeleton — missing/exact

Date: 2026-10-31
Lean: tmp/sheaf/xif/paper/S1568CoverSkeletonActual.lean
EXIT=0 (missing/exact; no small skeleton inhabitant).
SHA256 A6596C8518EB64F879F652B18CD7DCD990C9AA8F68446D72CDF00D5221EBB6DC
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S1568CoverSkeletonActual.olean

## Actual

S1568Cover := OrbicurveFiniteEtaleCover (S1419Orbicurve), Type 1.
S1568CoverMap A B : Type 1.
S1568Id A : S1568CoverMap A A is actual, reused from S405
(leftUnitor on StrongTrans).

## Exact small-skeleton first missing

S1568SmallSkeleton l:
  Skeleton : Type
  objEquiv : Skeleton ≃ S1568Cover
  coverCategory : Category.{0,0} Skeleton
  homEquiv : forall a b, (a ⟶ b) ≃ CoverMap (objEquiv a) (objEquiv b).
No inhabitant.

S1568CompositionRequired l : Type 1 :=
  forall A B C, CoverMap A B -> CoverMap B C -> CoverMap A C.
No inhabitant; S405 records the same missing strict composition/coherence.

S1568OriginalCategoryRequired l := Category.{0,1} Cover.
No inhabitant.

## No workaround

No Shrink/ULift/arbitrary small carrier, no group product, no l-torsion,
no terminal/point fiber.  The actual Type 1 cover-maps do not produce a
Type 0 skeleton by any available scheme/stack API.

## Conclusion

Small skeleton is a genuine missing construction.  The faithful alternative
remains the Category.{1,1} interface of S1566.