# S477: rational pullback id/comp laws

Date: 2026-10-29. On S462's example32RationalPullback.

## Proved

example32RationalPullback_eq_arrow:
  example32RationalPullback f
  = (Units.map (arrowAlgebraMap K f).toMonoidHom).toAdditive.

example32RationalPullback_id:
  example32RationalPullback (id X) = AddMonoidHom.id _.

example32RationalPullback_comp:
  example32RationalPullback (f ≫ g)
  = (example32RationalPullback f).comp (example32RationalPullback g).

Proofs use:
* S453 arrowAlgebraMap_id / arrowAlgebraMap_comp;
* Units.map_id / Units.map_comp;
* ext for Additive and MonoidHom.toAdditive.

No GroupLikeAddMonoidOn instance is asserted here (the S462 field type is
Type u while the size-aligned base is Type u+1); only the requested id/comp
laws are proved.  No fake data, no completion/L.
