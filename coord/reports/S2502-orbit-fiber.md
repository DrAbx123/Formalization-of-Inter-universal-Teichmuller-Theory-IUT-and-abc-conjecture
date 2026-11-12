# S2502: object-level orbit quotient actual; category/stack missing

Date: 2026-11-02. Serialized lake env lean -j1.

ACTUAL:
- S2502Rel sigma x y := y = x or y = sigma.obj x;
- S2502Orbit sigma := Quot (S2502Rel sigma);
- S2502OrbitMk sigma x := Quot.mk _ x;
- S2502OrbitMk_sigma : mk x = mk (sigma.obj x).
EXIT=0, olean 19448, SHA256 00eaccc48b5ac2c83e7754aa1f6db8ff997e4bbf7228eaecc6e936d8299fe879, axioms trio.

NOT a category: object quotient only. Mathlib CategoryTheory.Quotient quotients morphisms between the same objects, not objects; there is no orbit-category/Grothendieck construction API. Need hom quotient well-definedness, congruence, pseudofunctor/IsStack, descend/factor. No fake.