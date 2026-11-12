# S1631: small cover category — missing/exact

Date: 2026-10-31
Lean: tmp/sheaf/xif/paper/S1631SmallCoverCategoryActual.lean
EXIT=0 (missing/exact; no Category/skeleton inhabitant).
SHA256 F6048AC8D49617E062B6D7BDEE7D857CA2495C767E5F39833EAEAE2129964618
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S1631SmallCoverCategoryActual.olean

## Exact first missing

S1631SmallCoverCategory l:
  Skeleton : Type
  objEquiv : Skeleton ≃ OrbicurveFiniteEtaleCover (S1419Orbicurve)
  category : Category.{0,0} Skeleton
  homEquiv : forall a b, (a ⟶ b) ≃ CoverMap (objEquiv a) (objEquiv b).
No inhabitant.

S1631CompositionRequired l : Type 1 :=
  forall A B C, CoverMap A B -> CoverMap B C -> CoverMap A C.
No inhabitant.

S1631OriginalCategoryRequired l := Category.{0,1} Cover.
No inhabitant.

## Actual

S1631Id A : CoverMap A A is actual (reused from S405/S1568).
S1419 orbicurve nonterminal and once-punctured signature actual.

## Not used

No Shrink/ULift/arbitrary small carrier, no group product, no l-torsion,
no terminal/point fiber.

## Conclusion

No available scheme/stack API produces a Type 0 skeleton or composition
on the actual Type 1 cover maps.  The faithful alternative remains the
Category.{1,1} interface (S1566).