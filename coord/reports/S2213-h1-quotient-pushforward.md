# S2213: coboundary compatibility and the H^1 quotient pushforward

Date: 2026-11-02. Layer O. Consumer: S2210 / S2204 / S2196 / S2145 / S2114.

## File

tmp/sheaf/xif/paper/S2213H1QuotientActual.lean
Source SHA256 a876665f9ca6bbba9e94ad972538fbc775f0771681e167c782c32ff4a2e1194c
olean SHA256 79485c57a1087503d3ba43645f38ba04695ae8998b1b356b4638b85317e7e18f
EXIT=0. Axioms [propext, Classical.choice, Quot.sound].

## Built

S2213Pushforward_cohomologous proves that the continuous 1-cocycle
pushforward of S2210 sends Cohomologous cocycles to Cohomologous cocycles:
for w = z.twist a, the image is pushforward z twisted by S2145PowMap a,
using S2164PowMap_equivariant.
S2213H1Pushforward (n) is the induced map
  ContinuousH1(act_{n+1}) -> ContinuousH1(act_n)
of quotient types.

## Exact first missing

1. S2213H1PushforwardMonoidRequired n: the quotient map as a monoid
   homomorphism H1(n+1) ->* H1(n).  The underlying function is constructed;
   the monoid-hom compatibility with the ContinuousH1 quotient One/Mul
   instances remains to be proved (Quotient induction).
2. Finite H1(G_v,mu_{n!}).
3. Surjectivity of the quotient transition.
4. lim1 H1 = 0 / S2114CompatibleRepresentativeLift.

No H1 instance/finiteness/surjectivity/lim1 is claimed.
