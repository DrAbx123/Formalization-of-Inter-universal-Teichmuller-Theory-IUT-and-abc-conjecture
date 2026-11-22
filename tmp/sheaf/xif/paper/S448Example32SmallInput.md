# S448: independent Example32SmallInput attempt

Date: 2026-10-29. No fake Input; exact missing recorded.

## Actual part

Example32SmallRationalObject X := Additive (X.unop.obj.obj)^x
on the S432 size-aligned base Example32SmallBase K.

## Exact missing fields

Example32SmallNormBridge:
* toAlgHom : (X ⟶ Y) -> X.unop.obj.obj ->+[K] Y.unop.obj.obj;
* direction_ok : Prop;
* norm_pullback_law : Prop;
* norm_id_law : Prop;
* norm_comp_law : Prop.

Example32SmallInputGap:
* bridge : Example32SmallNormBridge;
* valuationFamily : Prop;
* normCompatibility : Prop;
* divisorNaturality : Prop;
* rationalFunctions_obj_eq : Prop;
* pullback_norm_eq : Prop;
* divisor_eq_coefficient : Prop.

Example32SmallInputRequired := Nonempty gap; no inhabitant.

## Why Input is not filled

S442 supplies normPullback for K-algebra maps on the covariant
DvTriangleFieldCover category; S446 supplies a category-morphism-to-AlgHom
bridge for that covariant category.  S432's base is
ULiftHom ((DvTriangleFieldCover K)^op).  A morphism X -> Y in the size-aligned
opposite base corresponds to an algebra map Y.unop -> X.unop, so the norm
pullback has the wrong direction for GroupLikeAddMonoidOn (which needs
obj Y -> obj X).  No reverse-direction bridge or norm id/comp laws are present
in the repo.

Also the explicit DvCoverNormalizedValuationData family and its norm
compatibility are parameters, not constructed.

Thus no actual Input/example32SmallFrobenioidPresentation is constructed here.
No fake object, no completion/L.
