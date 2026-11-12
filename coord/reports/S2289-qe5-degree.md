# S2289: absolute Q(E[5]) degree interface

Date: 2026-11-02. Layer O; consumer S2270/S2253/S2216.

## Actual

Lean:

  tmp/sheaf/xif/paper/S2289QE5DegreeActual.lean
  SHA256 82A27E08DA9CFF979FA5BC1D953631EA9E3D500F6AD799815F4B7837B973FF05
  EXIT=0
  olean SHA256 0739BAED9267B7C0EAB1661995175B4967E9A928FDBDB8E0933A50EFB6521536
  size 47368
  axioms propext, Classical.choice, Quot.sound.

Definitions/theorems:

- s2289QE5 := Polynomial.SplittingField S2057Psi5Q;
- NumberField/IsGalois instances;
- s2289Psi5_natDegree : S2057Psi5Q.natDegree = 12;
- s2289QE5_finrank_eq_card_aut:
    finrank Q Q(E5) = Nat.card (Q(E5) ~= Q(E5));
- s2289QE5_finrank_dvd_factorial:
    finrank Q Q(E5) divides 12!;
- s2289IntersectionIsBot_of_degreeProduct:
    degree product -> s2253IntersectionIsBot.

## Exact first missing

The actual value

  Module.finrank Q (SplittingField S2057Psi5Q)

is not computed.  It equals the order of the absolute Galois group of
Q(E[5]), which is the image of the 5-adic Galois representation.  Computing it
requires the large-image/the Galois-group order theorem.  The tree has only:

- psi5 degree 12 and separability;
- S1723/S1720 degree divisibility results;
- S2132 D5 large-image statements conditional on range hypotheses and
  S2132FrobInducesPairCycleType, not actual group order.

Consequently the following are still missing:

- exact [Q(E[5]):Q];
- s2270DegreeProduct (compositum degree = product);
- s2253IntersectionIsBot.

## Conclusion

- BUILT: absolute Q(E[5]) field, degree = Galois group order, 12! divisibility.
- MISSING: actual group order/degree, compositum degree, intersection.
- no fake; no assumed large-image theorem.
