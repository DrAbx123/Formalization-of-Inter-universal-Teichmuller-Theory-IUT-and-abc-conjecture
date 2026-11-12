# S2461: objectwise NatIso attempt — naturality residual

Date: 2026-11-02. Serialized lake env lean -j1.

Attempt: NatIso.ofComponents with components S2312QHomEqualizerObjIso and naturality by ext x; rfl.
Result: rfl fails. After ext x (x : WalkingParallelPair) the goal is:
  ((presheafHom.map p ≫ component T2.hom) ≫ limit.pi x app T2) x0
  = ((component T1.hom ≫ equalizer.map p) ≫ limit.pi x app T2) x0

This is the same naturality/sign-projection obstruction, now in the limit/equalizer presentation. No NatIso inhabitant.

ACTUAL retained: S2459 app HEq identity (olean 33960, SHA 75e2bd4f...), S2456 bridge (olean 47712), S2453 base identity (olean 54080), S2445 identity case (olean 55640).

S2461 source SHA256 c50459eb82e4b9717803d01f05a1add997ed5666a48c77cce108925ec597e521; no olean. No IsStack claim, no fake.