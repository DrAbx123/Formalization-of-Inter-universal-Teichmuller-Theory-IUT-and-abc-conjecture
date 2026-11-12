# S2498: actual invariant StrongTrans for S2496Map; cF/cK actual from S2495

Date: 2026-11-02. Serialized lake env lean -j1.

ACTUAL:
- S2495cF : HyperbolicOrbicurve S2490A.F (cF), S2495cF_signature sourceTypeOneLTorsionPlusMinus;
- S2495cK : HyperbolicOrbicurve S2490A.K (cK), S2495cK_signature;
- S2496Map : S2482Orbicurve.Hom S2495cF;
- S2497InvScheme : S2482AffineInvolution >> S2496f = S2496f;
- S2498Invariant : Iso (vcomp S2470SignAction.inversion S2496Map) S2496Map.
Proof: S2398HomOfStrongTrans_vcomp + S2497InvScheme + S1742StrongTransIsoOfHom.

EXIT=0, olean 22840, SHA256 f1110c4bcdcaa5df5d78945a4a0f6b6b47ffb53baecd441908efbec966cce3e6, axioms propext/Classical.choice/Quot.sound.

Still missing: OrbicurveSignInvariantMorphism S2470SignAction S2495cF cocycle field, and OrbicurveSignQuotientWitness. cF/cK themselves are actual S2495. No fake.