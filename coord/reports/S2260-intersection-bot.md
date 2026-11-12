# S2260: degree-product route to F' cap Q(E[5]) = Q

Date: 2026-11-02. Layer O; consumer S2253/S2216/S2167.

## Actual

Lean:

  tmp/sheaf/xif/paper/S2260IntersectionBotActual.lean
  SHA256 6D3371EB251723A20AA91C161709A9145B04FF8B6FA2802D3439048DEB50285B
  EXIT=0
  olean SHA256 D481104276D551228CAA186F3F687D5A6B343F35191314CCFE0E608A7EA59918
  size 29736
  axioms propext, Classical.choice, Quot.sound.

Theorem s2260IntersectionIsBot_of_finrank_sup:

  finite-dimensional images and
  finrank Q (FImage sup LImage) = finrank Q FImage * finrank Q LImage
  imply s2253IntersectionIsBot.

Proof: IntermediateField.LinearDisjoint.of_finrank_sup gives linear
disjointness, then LinearDisjoint.inf_eq_bot gives intersection bot.

## Exact first missing

1. s2260FImageFinite / s2260LImageFinite:
     FiniteDimensional Q of the two images in AlgebraicClosure Q.
   Not synthesized from S1720Field finite or SplittingField API in this file.
2. s2260DegreeProduct:
     finrank Q (FImage sup LImage)
       = finrank Q FImage * finrank Q LImage.
   This needs
   - [F' : Q] = 6 (S1699/S1710 finrank=6 still missing),
   - [Q(E[5]) : Q] (absolute 5-division splitting-field degree),
   - the compositum degree.
3. Equivalently s2253IntersectionIsBot itself.

## Route

The executable route is: prove the two finite-dimensional instances, then
compute the three degrees and prove their product relation.  No coprime-
discriminant/ramification computation has been formalized; that is an
alternative route, not an existing theorem.

## Conclusion

- BUILT: degree-product -> intersection-bot implication.
- MISSING: image finiteness, degree product (F' degree, Q(E5) degree,
  compositum degree), or the intersection equality.
- no fake; no S2040 assumption.
