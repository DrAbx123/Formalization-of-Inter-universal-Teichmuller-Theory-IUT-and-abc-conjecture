# S2114: H² comparison surjectivity reduced to the representative lift

Date: 2026-11-02. Layer O. Consumer: S2046M3M4 / S2091 PsiCnsH2LimitComparison.

## File

tmp/sheaf/xif/paper/S2114H2SurjectivityGapActual.lean
Source SHA256 9103b78c7f4c8e60fcf4b22481843593806ea1d841381496d6489df9ffee7859
olean SHA256 678d48de2c2a98fc30fee6b0e4eac6e0924f6bd5a5e834f05d45d605e1399654
EXIT=0. Axioms [propext, Classical.choice, Quot.sound].

## Equivalence proved

S2114H2ComparisonSurjective is Function.Surjective (h2Comparison ...).
S2114CompatibleRepresentativeLift is: for every compatible family y of level
H2 classes there is one continuous 2-cocycle c of the limit whose level classes
are exactly y.  The file proves both directions:

S2114_surjective_of_representativeLift :
  lift -> Surjective h2Comparison.

S2114_representativeLift_of_surjective :
  Surjective h2Comparison -> Nonempty lift.

The second uses QuotientGroup.mk'_surjective and Classical.choice only.

## Exact first missing

An inhabitant of S2114CompatibleRepresentativeLift, i.e. the representative
lifting of a compatible family of level H2 classes.  This is the lim^1 H^1 = 0
input: S2112 has the Z^2 exchange and h2Comparison, but no H^1 tower, no lim^1
and no finite/Mittag-Leffler vanishing theorem.  The arithmetic input is
H^1(G_v, mu_n) finite + Mittag-Leffler.

No unconditional Surjective h2Comparison and no CoboundaryLift are asserted.
No fake, sorry, axiom, or reduced surrogate.

## Next

Formalize H^1(G, A_n) as Iut.ContinuousH1 (actn n), its transition maps, the
lim^1 connecting map, and finite + ML => lim^1 = 0.  Then the representative
lift (and CoboundaryLift) follow.
