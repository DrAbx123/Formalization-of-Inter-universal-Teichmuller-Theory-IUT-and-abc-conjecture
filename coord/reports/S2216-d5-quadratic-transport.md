# S2216: mod-29 quadratic and cyclotomic irreducibility; transport gaps

Date: 2026-11-02. Layer O; consumer S2167/S2132 D5 large image.

## Actual

Lean:

  tmp/sheaf/xif/paper/S2216D5QuadraticTransportActual.lean
  SHA256 2FDF39F15E563BA37D5AA0674F0DEC37C4650EA294E0F5354288F11078F17A59
  EXIT=0
  olean SHA256 02951CB5729CFE89CD104CBB447AFD37E2635187D953ADD66B1FC621CB8D22F5
  size 139392
  axioms propext, Classical.choice, Quot.sound.

Theorems:

- s2216_quadratic_irreducible_explicit:
    Irreducible (19 + 24*X + 4*X^2) over ZMod 29;
- s2216_S2132F2Z_reduction:
    S2132F2Z.map (Int.castRingHom (ZMod 29))
      = 19 + 24*X + 4*X^2;
- s2216_quadratic_irreducible:
    Irreducible (S2132F2Z.map (Int.castRingHom (ZMod 29)));
- s2216_cyclotomic_three_mod29_irreducible:
    Irreducible (X^2 + X + 1) over ZMod 29;
- s2216_29_mod_three : (29 : ZMod 3) = 2.

No-root proofs use finite checks over ZMod 29 (decide +revert); no decide on
the full polynomial ring and no native_decide.

## Exact first missing

1. s2216TwentyNineInert:
     (Ideal.span {(29 : RingOfIntegers (CyclotomicField 3 Q))}).IsPrime.
   The residue polynomial is proved irreducible, but the actual ring-of-
   integers inertness statement is not derived.  This is the missing
   Dedekind factorization step.
2. s2216LinearDisjointnessRequired:
     there exists a common algebraically closed field Omega and embeddings
     of F' = S1720Field and the absolute 5-division field
     SplittingField S2057Psi5Q whose images intersect in Q.
   The file defines s2216LinearDisjointness precisely for a chosen pair of
   embeddings, and s2216AbsoluteFiveDivisionField = SplittingField S2057Psi5Q.
   No inhabitant of the required proposition is asserted.

S2167's DedekindFrobeniusCycleTypeStatement remains the general missing
cycle-type theorem; S2216 only supplies the concrete quadratic/cyclotomic
irreducibility inputs.

## Conclusion

- BUILT: both residue irreducibility facts, including the corrected S2132
  quadratic factor.
- MISSING: ring-of-integers inertness of 29 and the F'/Q(E[5]) linear-
  disjointness transport.
- no false S2057 data used; no fake; no target change.
