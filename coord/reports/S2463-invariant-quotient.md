# S2463: invariant quotient affine model actual; no HyperbolicOrbicurve cF/cK yet

Date: 2026-11-02. Serialized lake env lean -j1.

ACTUAL definitions:
- S2463InvariantCoordinateRing : Type := MvPolynomial (Fin 1) F, the model F[x] of the invariant subring.
- S2463InvariantCoordinate : S2463InvariantCoordinateRing := X 0.
- S2463cFScheme := Spec (CommRingCat.of S2463InvariantCoordinateRing).
- S2463cFOver : SchemeOverField F := Over.mk (Spec.map (algebraMap F ...)), i.e. Spec F[x] over Spec F.
- S2463cKCoordinateRing K := MvPolynomial (Fin 1) K; S2463cKScheme := Spec K[x].
- S2463cFHyperbolicMissing l := exists cF : HyperbolicOrbicurve F, cF.signature = sourceTypeOneLTorsionPlusMinus l (missing statement only).

EXIT=0, olean 26208, SHA256 2fe0f618a726a59b3bb0b0ab8ba24b47504287bd803589abe43ea659d9b0847e, axioms propext/Classical.choice/Quot.sound.

NOT claimed: this is only the affine ring/scheme model F[x] and base change K[x]. It is NOT yet a HyperbolicOrbicurve cF, has no OrbicurveGeometry sign-quotient certificate, no quotient : OrbicurveSignInvariantMorphism signAction cF, no OrbicurveSignQuotientWitness, and no proof that F[x] is the actual invariant subring of R under y -> -y. cK as HyperbolicOrbicurve is likewise missing.

No fake, no IsStack.