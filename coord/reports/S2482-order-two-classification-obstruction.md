# S2482OrderTwoAlgAutClassification: exact missing

## Actual baseline
- S2482QiNontrivialActual.lean: nontriviality and original-uniqueness refutation actual;
  SHA 380587FF..., olean 645F6D3A....
- S2482CorrectedSourceSignQuotientActual.lean: corrected interface with TwoIso uniqueness;
  SHA 53E074A7..., olean 828901E3....
- S2482InvolutionUniquenessAuditActual.lean: corrected uniqueness Prop in TwoIso form;
  SHA D339C8C2..., olean FB83D0AF....
All EXIT=0, axioms propext/Classical.choice/Quot.sound.

## Classification target
S2482OrderTwoAlgAutClassification:
  forall phi : R ~= F-algebra R, phi^2=id -> phi=id or phi=S2482CoordinateRingInvolution.
No inhabitant.

## Exact missing lemmas for a proof
1. Affine equivalence: endomorphisms of S2482Orbicurve correspond to F-algebra endomorphisms
   of R. Mathlib has Spec.map_inj/fully-faithful affine results, but the stack-level translation to an
   algebra automorphism still has to be assembled.
2. Order-two automorphism fixes x:
     phi(x) = x.
   Missing: use the quotient R -> F[x] by the hyperelliptic involution, or the degree-2
   F(x)-module structure; no formalized invariant-subring argument.
3. Then phi(y)^2 = x^3-x, so phi(y)=+y or -y in the domain R.
   Missing: the equation/root comparison; follows once phi(x)=x and phi is an automorphism.
4. Nonidentity excludes +y: if phi(y)=y and phi(x)=x then phi=id; hence phi(y)=-y,
   which is S2482CoordinateRingInvolution.
5. Lift algebra equality to a TwoIso of strong transformations: Spec/2-Yoneda gives a 2-isomorphism;
   the exact comparison map still has to be written.
None of steps 1-5 is formalized. No fake inhabitant was added.

## Consequence
Corrected uniqueness (TwoIso form) remains exact missing; sign action/cF/cK/epsilon also remain
missing. The blocks are genuine classification and 2-Yoneda comparison data, not syntactic wrappers.

## Artifacts
No new file compiled for this attempt. Existing actual corrected interface and nontriviality files remain
as listed above.