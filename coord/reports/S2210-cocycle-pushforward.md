# S2210: actual cocycle pushforward and the H^1 quotient/finiteness gap

Date: 2026-11-02. Layer O. Consumer: S2204 / S2196 / S2145 / S2138 / S2114.

## File

tmp/sheaf/xif/paper/S2210H1FiniteActual.lean
Source SHA256 2bbe1462393952414bc44f575dd03f8e656a7891d9fa022a78b1ea49d462ce7e
olean SHA256 f93c38f3466b52c073166d5b693d46ee687492dc50fa05cb8ab65280be233e63
EXIT=0. Axioms [propext, Classical.choice, Quot.sound].

## Built

S2210CochainPushforward (n) sends a continuous 1-cocycle at level n+1 to a
continuous 1-cocycle at level n by postcomposition with the actual power map
S2145PowMap p n, using S2164PowMap_equivariant for the cocycle law.
S2210CocyclePushforwardHom (n) is this map as a monoid homomorphism of the
continuous 1-cocycle groups.

## Exact first missing

1. Coboundary compatibility of the cocycle pushforward, yielding the quotient
   map S2204H1 p (n+1) ->* S2204H1 p n.  This needs the twist/coboundary
   formula under a coefficient monoid hom (currently no API in ContinuousH1).
2. S2210H1FiniteRequired: forall n, Finite (H1(G_v,mu_{n!})).
3. Surjectivity of the quotient transition.
4. lim1 H1 = 0 / S2114CompatibleRepresentativeLift.

No H1 instance, finiteness, or surjectivity is claimed.
