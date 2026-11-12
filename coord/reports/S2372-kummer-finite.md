# S2372: finite Kummer quotient and the H^1 comparison gap

Date: 2026-11-02. Layer O. Consumer: S2360 / S2204 / S2214.

## Rebuilt external dependency

LocalClassFieldTheory.PadicField.PowIndexPadic was missing its olean; compiled
from tmp/local-cft-port/PadicField/PowIndexPadic.lean into
.lake/build/lib/lean/LocalClassFieldTheory/PadicField/PowIndexPadic.olean
(361664 bytes, SHA256 93d824183ce62e3a714adfc3a8fe8d389b1d6dc860c36bd8773c25bcb66e25dc).
EXIT=0.  Its PadicField.PowIndex/Ramification/Complete dependencies had oleans.

## File

tmp/sheaf/xif/paper/S2372KummerFiniteActual.lean
Source SHA256 bb8ada844011d4f36a5c173eab4f8a521095976717d504deda56d0f8f7436d89
olean SHA256 aac4fe2012d2d99ca5b5c009baf4aa1266b6a68184030229b796e79c7e69a961
EXIT=0. Axioms [propext, Classical.choice, Quot.sound].

## Built

S2372KummerQuotient p n = Q_p^x/(Q_p^x)^{n!}.
S2372KummerQuotient_finite: Finite (S2372KummerQuotient p n), using
PadicField.index_range_pow and finite-index quotient.

## Exact first missing

1. S2360H1Comparison: an equivalence between the actual Iut.ContinuousH1
   carrier S2204H1 p n and the external ContH1 Gal(Q_p^alg/Q_p)(mu_{n!}).
   The Kummer isomorphism S2360KummerEquiv and the finite quotient above are
   actual; the comparison of the two H^1 formalizations is not.
2. After the comparison, finite H1(G_v,mu_{n!}) and the level transition
   surjectivity follow from the Kummer quotient and kummerEquiv_quotTransition.
3. lim1 / S2114CompatibleRepresentativeLift.

No finite H1 or surjectivity is claimed.
