# S2482 order-two classification: formal non-constructibility points

## Goal
S2482OrderTwoAlgAutClassification:
  forall phi : R ~= F-algebra R, phi^2=id -> phi=id or phi=S2482CoordinateRingInvolution.

## Norm-degree route and its exact gaps
Mathlib provides, for W: y^2=x^3-x over F:
- CoordinateRing.basis : Basis (Fin 2) F[X] W.CoordinateRing;
- CoordinateRing.norm_smul_basis;
- CoordinateRing.degree_norm_smul_basis [IsDomain F]:
    degree (norm (p • 1 + q • Y)) = max (2*degree p) (2*degree q + 3);
- CoordinateRing.natDegree_norm_ne_one.

The following formal steps are missing:
1. An actual F-algebra equivalence between our R = F[x,y]/(y^2-x^3+x)
   (MvPolynomial quotient) and W.CoordinateRing (AdjoinRoot over F[X]).
   Mathlib has AdjoinRoot quotient machinery and Polynomial.Bivariate.equivMvPolynomial,
   but no assembled equivalence for this R.
2. A theorem that an F-algebra automorphism phi of W.CoordinateRing preserves the pole/norm
   filtration or sends the unique point at infinity to itself. This is not in Mathlib/tree.
3. A theorem that phi(x) lies in F[x] (or has a well-defined polynomial x-degree). Without this,
   the comparison of the rank of W.CoordinateRing over F[phi(x)] cannot be reduced to
   degree(phi(x))*2.
4. A rank/degree argument: if phi(x) in F[x] has degree d, then rank over F[phi(x)] is 2d;
   since phi is an automorphism, rank is also 2, hence d=1 and phi(x)=a x + b.
5. phi^2=id then forces a^2=1; the b=0 branch follows from y^2=x^3-x and the affine
   automorphism of order two fixing the origin. This integer/affine classification is not formalized.
6. Finally Spec/2-Yoneda converts the algebra equality to Nonempty (TwoIso inv S2482EllipticInvolution).
   Only this 2-iso form is needed; equality of strong transformations is not required.

## Branch-point caution
Mobius maps preserving {0,1,-1,infinity} include 1/x and -1/x, so the branch-point permutation
argument alone is insufficient. The norm-degree route also needs gap 2 (filtration preservation).

## Actual baseline (unchanged)
- S2482QiNontrivialActual.lean: nontriviality + original uniqueness refutation actual;
  SHA 380587FF..., olean 645F6D3A....
- S2482CorrectedSourceSignQuotientActual.lean: corrected TwoIso interface;
  SHA 53E074A7..., olean 828901E3....
- S2482InvolutionUniquenessAuditActual.lean: corrected TwoIso Prop;
  SHA D339C8C2..., olean FB83D0AF....
All EXIT=0, axioms propext/Classical.choice/Quot.sound.

## Conclusion
The classification is not constructible from current APIs without adding gaps 1-5. No fake
inhabitant was introduced; sign action/cF/cK remain blocked on this classification and on the
pseudofunctor diagram/atBase data.