# S2499: actual OrbicurveSignInvariantMorphism for cF

Date: 2026-11-02. Serialized lake env lean -j1.

ACTUAL:
- S2499CatHom₂Subsingleton: 2-cells between functors from Xf.obj U to cF.obj U are subsingleton (S1932NatTransSubsingleton, target representable/discrete).
- S2499StrongTransSubsingleton: 2-cells between S2482Orbicurve.Hom S2495cF are subsingleton.
- S2499InvariantMorphism : OrbicurveSignInvariantMorphism S2470SignAction S2495cF with map=S2496Map, invariant=S2498Invariant, cocycle closed by explicit S2499StrongTransSubsingleton.elim.

EXIT=0, olean 39568, SHA256 6b7c6c8285330f207709a2f3423d28fdf9e8241620e9a9f4b5b89c1ccc6a942a, axioms propext/Classical.choice/Quot.sound.

Now cF, signal action, quotient map and invariant morphism are actual. Remaining: quotientWitness (descend/factor/descendTwoCell/twoCellExt) and epsilon. No fake.