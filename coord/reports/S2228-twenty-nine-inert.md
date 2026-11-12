# S2228: 29 is inert in Q(sqrt(-3))

Date: 2026-11-02. Layer O; consumer S2216/S2167 D5 transport.

## Actual

Lean:

  tmp/sheaf/xif/paper/S2228TwentyNineInertActual.lean
  SHA256 8F206103EC12629F51F73DA74DBEC78BFC1B93F4F120EE950B37F089664B63DB
  EXIT=0
  olean SHA256 741AC8B9464421CE1C9720EC26D57CE8F58A66EBAAF7712F6AA34707E0063685
  size 76992
  axioms propext, Classical.choice, Quot.sound.

Theorem s2228_twentyNineInert:

  (Ideal.span {(29 : RingOfIntegers (CyclotomicField 3 ℚ))}).IsPrime.

Proof chain:

1. K = CyclotomicField 3 ℚ, θ = (zeta_spec 3 ℚ K).toInteger;
2. exponent θ = 1 via RingOfIntegers.exponent_eq_one_iff and
   hζ.integralPowerBasis.adjoin_gen_eq_top; hence 29 does not divide exponent θ;
3. minpoly ℤ θ = X^2 + X + 1: RingOfIntegers.minpoly_coe +
   hζ.coe_toInteger + cyclotomic_eq_minpoly + cyclotomic_three;
4. Kummer-Dedekind quotient equivalence
   RingOfIntegers.ZModXQuotSpanEquivQuotSpan at p=29;
5. reduction of the minpoly is X^2+X+1 over ZMod 29, irreducible by S2216;
6. quotient is a field, hence (29) is maximal/prime.

The target s2216TwentyNineInert is proved
(s2228_TwentyNineInert_holds).

## Exact first missing

Only the linear-disjointness transport remains:

  s2216LinearDisjointnessRequired.

The absolute 5-division field is SplittingField S2057Psi5Q.  One needs a
common algebraic closure Ω and embeddings of S1720Field and that splitting
field whose images intersect in Q.  No inhabitant is asserted.

The general DedekindFrobeniusCycleTypeStatement of S2167 also remains
unproved; S2228 supplies the inertness half of the transport, not the
cycle-type theorem.

## Conclusion

- BUILT: actual inertness of 29 in O_{Q(sqrt(-3))}.
- MISSING: linear disjointness F' cap Q(E[5]) = Q / transport to
  F'-automorphism.
- no fake; no false S2057 data.
