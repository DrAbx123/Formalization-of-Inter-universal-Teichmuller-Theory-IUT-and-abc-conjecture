# S2470: actual OrbicurveSignAction on S2482Orbicurve

Date: 2026-11-02. Serialized lake env lean -j1.

ACTUAL: S2470SignAction : Iut.OrbicurveSignAction S2482Orbicurve.
Fields:
- diagram := S2468Diagram (via mkPseudofunctor, map = S2465Map on SignGroup, mapComp = S2466MapComp, coherences closed by S2468StrongTransSubsingleton and Subsingleton.elim);
- atBase := S2469AtBase := Bicategory.Equivalence.id Xfiber;
- inversion := S2482EllipticInvolution;
- generator_identification := explicit left/right unitor composition;
- inversionSquared := S2459InvolutionSquared.

EXIT=0, olean 98528, SHA256 d08b8ccfe1ede854c84ca5c6f941d65809ed986ea67402229f1401c5ee5c0c83, axioms propext/Classical.choice/Quot.sound.

This closes the sign-action packaging only. cF/quotient/quotientWitness, cK/scalar extension, groups and epsilon remain missing. No fake, no IsStack.