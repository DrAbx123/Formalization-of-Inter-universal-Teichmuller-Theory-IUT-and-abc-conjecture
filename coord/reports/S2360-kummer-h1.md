# S2360: Kummer theory at Q_p and the H^1 comparison gap

Date: 2026-11-02. Layer O. Consumer: S2204 / S2214 / S2114.

## File

tmp/sheaf/xif/paper/S2360KummerH1Actual.lean
Source SHA256 72ea439ad769a95cea669dfa6b00bf6dc6ff8d33cc85a804d6d8c5f2f2688cf2
olean SHA256 296a77ed90c2a2c0b4810f41ecb5086392d148358dfdf786a3c39fdbc7c48b0f
EXIT=0. Axioms [propext, Classical.choice, Quot.sound].

## Built

S2360KummerEquiv (p) (n) is the actual Kummer isomorphism at K = Q_p,
m = n!:

  Q_p^x/(Q_p^x)^{n!} ~ ContH1 Gal(Q_p^alg/Q_p) (mu_{n!}),

transported from KummerTheory.kummerEquivAlgClosure.

## Exact first missing

1. S2360H1Comparison: an equivalence between the actual Iut.ContinuousH1
   carrier S2204H1 p n and the external ContH1 Gal(...) (mu_{n!}).
   The two H^1 definitions are different formalizations (continuous crossed
   homomorphisms modulo coboundary conventions), so this comparison is not
   available yet.
2. The padic index formula index_range_pow (LocalClassFieldTheory.PadicField.
   PowIndexPadic) is not imported because its olean is absent; it gives finite
   index of (Q_p^x)^{n!} and hence finiteness of the Kummer quotient.
3. Surjectivity of the level transition via kummerEquiv_quotTransition
   (Kummer/Limit.lean) after the H^1 comparison.

No Finite H1 or surjectivity is claimed.
