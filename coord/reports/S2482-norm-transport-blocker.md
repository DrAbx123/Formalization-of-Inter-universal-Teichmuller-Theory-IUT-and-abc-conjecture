# Norm transport: exact blocker after coordinate-ring equivalence

## Actual
S2482CoordRingEquivActual.lean (EXIT=0) gives
  S2482CoordRingEquiv : S2482W.CoordinateRing ≃ₐ[F] S2482CoordinateRing.
SHA 28170772..., olean DF38701B....

## Attempted basis transport
Defined S2482BaseMap : F[X] →+* R by composing S2482CoordRingEquiv with the
Weierstrass algebraMap F[X] -> W.CoordinateRing, and tried to use it to make R an
F[X]-module, then Basis.map. The attempt did not compile:
- the elaborated scalar action on R was (RingHom.id F[X]) c •, not S2482BaseMap c •;
  the local Module.compHom instance was not the one used in the LinearMap target;
- consequently map_smul' cannot be closed by change/rfl.
The invalid file S2482NormTransportActual.lean was removed (not consumed).

## Exact next formal object needed
Build an actual Algebra (Polynomial F) S2482CoordinateRing instance whose algebraMap is
  S2482BaseMap = S2482CoordRingEquiv ∘ algebraMap F[X] W.CoordinateRing,
prove S2482CoordRingEquiv is F[X]-linear for that instance, then define
  S2482Basis := (CoordinateRing.basis S2482W).map S2482LinearEquiv.
After that transport norm_smul_basis/degree_norm_smul_basis, prove phi(x)=x, then phi(y)=±y.

## Status
No fake norm/basis was added. Classification and sign action remain unproved.
The coordinate-ring equivalence itself remains actual and reusable.