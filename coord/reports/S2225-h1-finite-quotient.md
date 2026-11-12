# S2225: finite-quotient H^1 finiteness

Date: 2026-11-02. Layer O. Consumer: S2214 / S2204 / S2145 / S2114.

## File

tmp/sheaf/xif/paper/S2225H1FiniteQuotientActual.lean
Source SHA256 7f58ba0a83c5976f4d41b7f7a78796f0d76ea7b31fd91cd1004aeda7fec7a816
olean SHA256 53e6b3966043587d5b693d898f0061cfe0a09042356c0778decd0fa1a11066b3
EXIT=0. Axioms [propext, Classical.choice, Quot.sound].

## Built

S2225FiniteQuotientAction n Q takes Q as an explicit parameter with Group and
Finite instances, avoiding the S2220 instance-projection block.
S2225QuotientAction constructs the continuous action of the finite quotient
(for discrete topology).
S2225QuotientH1_finite proves Finite (H1(Q,mu_{n!})): continuous cochains
inject into all functions Q -> mu_{n!}, and both Q and mu_{n!} are finite.
S2225FiniteQuotientH1Data adds the comparison
H1(G_v,mu_{n!}) ~ H1(Q,mu_{n!}).
S2225FiniteH1OfQuotient transports finiteness to H1(G_v,mu_{n!}).

## Exact first missing

1. An actual finite quotient Q of G_v through which the action on mu_{n!}
   factors, with the comparison H1(G_v,mu_{n!}) ~ H1(Q,mu_{n!}).
   This is S2225FiniteQuotientH1Data.
2. Surjectivity of the H1 transition H1(n+1)->*H1(n) (separate chain-level
   lifting).
3. lim1 / S2114CompatibleRepresentativeLift.

No unconditional finiteness or surjectivity is claimed.
