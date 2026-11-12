# S2471: sign action integrated into S2492 bundle; cF/cK exact missing

Date: 2026-11-02. Serialized lake env lean -j1.

ACTUAL:
- S2470SignAction : OrbicurveSignAction S2482Orbicurve (EXIT=0, olean 98528, SHA d08b8ccf...).
- S2471BundleSignAction : OrbicurveSignAction S2492Bundle.xF := S2470SignAction; S2471BundleSignAction_inversion rfl. EXIT=0, olean 9312, SHA d15dd74037e7255372f09f54d4954a78bbb590f28302885d456f95b5573924fd, axioms trio.

cF NOT constructed. Exact missing: the quotient stack [X/{+-1}] as pointwise lax colimit/Grothendieck construction of the sign action, its pseudofunctor functoriality, its IsStack/stackification, and its OrbicurveSignQuotientWitness universal property. S1932CFQuotient/S1964QuotientStructure isolate exactly this; no inhabitant. The S2492 corrected bundle structure does not contain cF/cK fields, so it cannot supply them.

cK NOT constructed: needs an actual cF first, then SourceOrbicurveScalarExtension F K cF and signature/group data. S2463 only has the affine model Spec F[x], not a proven quotient and not a HyperbolicOrbicurve.

No fake, no IsStack.