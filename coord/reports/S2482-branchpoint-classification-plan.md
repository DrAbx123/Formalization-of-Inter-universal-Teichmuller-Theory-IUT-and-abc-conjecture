# S2482 order-two classification: branch-point route and exact missing

## Goal
S2482OrderTwoAlgAutClassification:
  forall phi : R ~= F-algebra R, phi^2=id -> phi=id or phi=S2482CoordinateRingInvolution.

## Branch-point proof route (not formalized)
1. phi induces an F-automorphism of the function field K=F(x,y), y^2=x^3-x.
2. On F(x) it is a fractional linear transformation of degree <=2 because phi^2=id on K.
3. It must permute the branch points {0,1,-1,infinity}. Enumeration of degree<=2 Mobius maps
   preserving this set gives phi(x)=x or phi(x)=-x.
4. If phi(x)=-x, then phi(y)^2=-(x^3-x), so phi(y)=+/- i y (i^2=-1 in F=Q(i)).
   Then phi^2(y) = -y, contradicting phi^2=id (y != 0). Hence phi(x)=x.
5. Then phi(y)^2=x^3-x, so phi(y)=+/- y. Nonidentity excludes +y, giving the sign involution.
6. Lift the algebra equality to Nonempty (TwoIso inv S2482EllipticInvolution) via Spec/2-Yoneda;
   only a 2-isomorphism is needed, not equality.

## Exact missing formal inputs
A. `phi` on the fraction field/function field: Mathlib API for FractionRing R and its action,
   and the identification K=F(x)(sqrt(x^3-x)). Not assembled in the tree.
B. `phi(x)` is a degree<=2 fractional linear transformation: needs an order/degree argument on
   F(x) under the order-two automorphism phi, plus fraction-field degree theory. Missing.
C. Enumeration of Mobius maps preserving {0,1,-1,infinity} and their squares. Missing.
D. Root comparison in R: u^2=-(x^3-x) -> u=+/- i y, and u^2=x^3-x -> u=+/- y.
   This uses R being an integral domain and the quadratic equation; not formalized here.
E. 2-Yoneda comparison from the algebra/scheme equality to a TwoIso of strong transformations.
   S1742 gives representable strong transformations and their iso comparisons, but the concrete
   comparison for the involution is not assembled.

## Actual baseline (unchanged)
- S2482QiNontrivialActual.lean: phi-nontriviality/refutation actual; SHA 380587FF..., olean 645F6D3A....
- S2482CorrectedSourceSignQuotientActual.lean: corrected interface with TwoIso uniqueness;
  SHA 53E074A7..., olean 828901E3....
- S2482InvolutionUniquenessAuditActual.lean: corrected TwoIso Prop; SHA D339C8C2..., olean FB83D0AF....
All EXIT=0, axioms propext/Classical.choice/Quot.sound.

## Conclusion
The classification is not proved. The branch-point route is mathematically clear but the required
function-field/Mobius/root-comparison API is absent. No fake inhabitant or conditional axiom was added.
Sign action/cF/cK remain blocked on this classification and on the separate pseudofunctor diagram data.