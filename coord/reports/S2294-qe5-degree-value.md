# S2294: Q(E[5]) degree value status

Date: 2026-11-02. Layer O; consumer S2289/S2270/S2253.

## Actual

Lean:

  tmp/sheaf/xif/paper/S2294QE5DegreeValueActual.lean
  SHA256 630CC2C065CE664E43F0D77BB08CEBD4A4D09D32EF06C4DD72060C78A9570F58
  EXIT=0
  olean SHA256 C988C80CF8F868DB4FF2A2D2ACF322812117BB94CA0FE7D534D1314E35A2C8E1
  size 29784
  axioms propext, Classical.choice, Quot.sound.

Definitions/theorems:

- s2294QE5DegreeIs n : finrank Q Q(E5) = n;
- s2294QE5_finrank_pos;
- s2294QE5_finrank_eq_card_aut;
- s2294QE5_finrank_dvd_factorial;
- s2294IntersectionIsBot_of_degreeProduct.

## Exact first missing

The actual numeral n with s2294QE5DegreeIs n.  Equivalently the order of the
absolute Galois group/image of the 5-adic representation of S1667Curve.

The tree does not determine it.  Available conditional data:

- S2057RangeHypothesesData b consists of det_surjective, pair_transitive,
  cycle_type_102 for the image of
  S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b;
- it requires b : S1725TorsionBasis S1987Five (rank-two torsion basis, itself
  missing);
- S2132/S2057 prove D5 large-image statements from that data, but a large-
  image inclusion does not pin the exact Galois group order.

So the exact first missing is a group-order computation: determine

  Nat.card (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range

or equivalently finrank Q Q(E[5]), from the Dickson classification plus
trace/determinant data.  No such theorem exists in the tree.

## Consequences

- s2270DegreeProduct (compositum degree = product) remains missing;
- s2253IntersectionIsBot remains missing;
- F' degree 12 is actual (S2005), not 6.

## Conclusion

- BUILT: parameterized degree target, positivity, group-order identity, 12!
  bound, degree-product reduction.
- MISSING: actual group order / [Q(E5):Q], compositum degree, intersection.
- no fake; no assumed large-image theorem.
