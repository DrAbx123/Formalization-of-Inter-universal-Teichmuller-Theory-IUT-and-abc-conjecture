# S2443: actual H^2 comparison surjectivity and compatible representative lift

Date: 2026-11-03. Layer O. Consumer: S2114/S2112/S2426/S2440.

## Files

S2442H2ComparisonActual2.lean
  source SHA256 ab2747337d8cc2f845a1fa6b9b1cac5c70d08bfb3873b29de6e95fd9fa63afad
  olean SHA256 5f310dfa42012f4bc25aef50d3f4ab09b41302596341bb951e88c64fb2e3be7f
  EXIT=0, axioms [propext, Classical.choice, Quot.sound].

S2443H1H2ClosedActual.lean
  source SHA256 3d6becfb77c4ee5beda893c3a1478f6ede70dc8eeae7624ca9125073a325c428
  olean SHA256 8a0d22c7e080dedd7f7ad8ad7ac5f97fc42ad333dead7e7162345aecc0f85716
  EXIT=0, axioms [propext, Classical.choice, Quot.sound].

## Construction

1. oneCochainProj_surjective: if coefficient transitions proj n are surjective,
   every continuous 1-cochain at level n lifts to level n+1 (choose preimages and
   use local constancy).
2. exists_defect: the ratio of the projection of a level n+1 representative and
   a level n representative of the same H^2 class is delta of a continuous
   1-cochain.
3. correctNext: multiply the next representative by the coboundary of a lift of
   the inverse correction cochain, keeping the H^2 class and making the
   projection exact.
4. repState recursion along n gives a compatible family repCocycle with
   repCocycle_class and repCocycle_compat.
5. Assembling the compatible family into a limit 2-cocycle gives
   h2Comparison_surjective_of_coeff_surjective.
6. Actual mu_{n!} tower: S2145PowMap is surjective (roots of unity are divisible),
   so the actual H^2 comparison is surjective and the actual S2114 compatible
   representative lift exists.

## Actual results

S2443ActualCompatibleRepresentativeLift :
  S2114CompatibleRepresentativeLift (S2145Coeff p) (S2145PowMap p)
    (S2196MuActionTower p).actn (S2196MuActionTower p).compat.
S2443ActualH2Comparison_surjective : Surjective actual h2Comparison.
S2443S2441Lift : inhabits S2441ActualRepresentativeLiftRequired.
S2443ActualH1Lim1_subsingleton : lim^1 H^1 = 0.

No sorry, no fake axioms, no conditional-as-actual claim.
