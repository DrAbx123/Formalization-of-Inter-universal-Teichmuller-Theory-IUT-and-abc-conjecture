# S2309: finite-field subfield uniqueness

Date: 2026-11-02. Layer O; consumer S2307/S2217.

## Actual

Lean:

  tmp/sheaf/xif/paper/S2309SubfieldUniqueActual.lean
  SHA256 CA603689A469C5013A7F600CCFE965CB35F3711A71A28C50CF4A1A6DE92D6CCD
  EXIT=0
  olean SHA256 69D7D1297F493829222BA98A51A2390F30477FCEF12B5F74BB9DAF3CB5B53C13
  size 201736
  axioms propext, Classical.choice, Quot.sound.

Theorem:

  finiteField_subfield_eq_of_card_eq
    {F E} [Field F] [Fintype F] [Field E] [Algebra F E]
    (A B : IntermediateField F E) [Fintype A] [Fintype B]
    (hdApos : 0 < Module.finrank F A)
    (hcard : Nat.card A = Nat.card B) : A = B.

Proof:

1. q = Nat.card F, q >= 2;
2. Module.natCard_eq_pow_finrank gives card A = q^dA, card B = q^dB;
3. hcard and Nat.pow_right_injective give dA = dB = d;
4. every a in A satisfies a^(q^d) = a via FiniteField.pow_card;
5. A is contained in the root set of X^(q^d)-X; the root set has at most
   q^d elements by ncard_rootSet_le and natDegree of the difference;
6. A has q^d elements, hence A = root set; similarly B = root set, so A = B.

The positive-degree hypothesis is exactly what transitivity needs
(g irreducible nonconstant); the zero-degree case is separate.

## Exact next missing (transitivity)

1. Construct the embedding phi : adjoin F {x} -> E with phi x = y
   (exists_algHom_adjoin_of_splits_of_aeval, g splits in residue field);
2. prove phi.fieldRange = adjoin F {x} using
   finiteField_subfield_eq_of_card_eq;
3. get phi as AlgEquiv of Kx, use
   FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow to express it as
   a Frobenius power;
4. align Kx-Frobenius with frobBar on E and conclude y = frobBar^n x.

The high-level subfield uniqueness input is now actual; the remaining steps
are not yet formalized.

## Conclusion

- BUILT: finite-field subfield uniqueness lemma (positive degree).
- MISSING: its application to construct/identify phi and derive Frobenius
  transitivity.
- no fake; no false S2057 data.
