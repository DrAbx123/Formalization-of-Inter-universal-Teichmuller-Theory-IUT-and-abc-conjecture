# S2270: image finiteness and F' degree 12

Date: 2026-11-02. Layer O; consumer S2253/S2260/S2216.

## Actual

Lean:

  tmp/sheaf/xif/paper/S2270IntersectionDegreeActual.lean
  SHA256 D5EAB9FA8B535AD9904580882DB1311B4577A01B33FE8850A085A6F784392051
  EXIT=0
  olean SHA256 82E1610BA752045FFCAEC05E5EA72F9655EAD2177A2D31CBFA7554D3002FF797
  size 56152
  axioms propext, Classical.choice, Quot.sound.

Built:

- s2270FImageFinite, s2270LImageFinite: FiniteDimensional Q of the two images,
  transferred via IntermediateField.equivMap from S1720Field and the
  absolute splitting field;
- s2270FImage_finrank_eq: finrank FImage = finrank S1720Field;
- s2270FImage_finrank: finrank FImage = 12, using S2005_finrank;
- s2270LImage_finrank_eq: finrank LImage = finrank of the absolute
  5-division splitting field;
- s2270IntersectionIsBot_of_degreeProduct: degree product implies
  intersection bot.

## Important correction

S1699/S1710's target finrank = 6 is for S1687Field, not for
F' = S1720Field.  S2005_finrank proves

  Module.finrank Q S1720Field = 12.

Thus [F' : Q] = 12, not 6.  The S2260 degree product must use 12.

## Exact first missing

1. Absolute 5-division degree:
     Module.finrank Q (SplittingField S2057Psi5Q).
   The tree has S1723 bounds for a relative L (dividing 96), not the absolute
   degree of SplittingField S2057Psi5Q.
2. Compositum degree / degree product:
     s2270DegreeProduct;
3. or s2270IntersectionIsBot.

No inhabitant is asserted.

## Conclusion

- BUILT: image finiteness, F' degree 12, degree-product reduction.
- CORRECTED: [F':Q]=12 (S2005), not S1699/S1710's 6 (which is S1687Field).
- MISSING: absolute Q(E[5]) degree, compositum degree/product, intersection.
- no fake.
