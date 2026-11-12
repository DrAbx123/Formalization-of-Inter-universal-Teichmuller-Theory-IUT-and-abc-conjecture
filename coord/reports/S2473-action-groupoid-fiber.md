# S2473: action groupoid fiber — minimal hom/id/comp actual

Date: 2026-11-02. Serialized lake env lean -j1.

ACTUAL definitions (generic C, sigma : C -> C, sq : sigma ;; sigma ~ 1):
- S2473Hom x y := (x -> y) + (x -> sigma.obj y)  (two branches);
- S2473Id x := inl (id x);
- S2473Comp: inl/inl, inl/inr, inr/inl (uses sigma.map), inr/inr (uses sigma.map and sq.hom.app).
EXIT=0, olean 71168, SHA256 eadbdedef97f81b875e240599bda7c3004ae879048493430fc093c647bc3647d, axioms propext/Classical.choice/Quot.sound.

NOT yet a category: Category instance/laws, functoriality over (SchemeOverField F)^op, IsStack, quotient map, quotientWitness, cF/cK are still missing.

No fake, no IsStack claim.