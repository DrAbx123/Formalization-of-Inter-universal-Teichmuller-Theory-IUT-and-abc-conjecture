# S2214: H^1 quotient pushforward as a monoid homomorphism

Date: 2026-11-02. Layer O. Consumer: S2213 / S2204 / S2196 / S2145 / S2114.

## File

tmp/sheaf/xif/paper/S2214H1MonoidActual.lean
Source SHA256 76eadd934eb85fc820adc65615fefd6333590a9ae042f4d9a970a485f746ebb6
olean SHA256 e3c8f59355aa87b68a8c8bad63c7f5adbcc5c405aeb615d46fd6d133c206b8fe
EXIT=0. Axioms [propext, Classical.choice, Quot.sound].

## Built

S2214H1PushforwardHom (n) :
  S2204H1 p (n+1) ->* S2204H1 p n
is the H^1 quotient pushforward of S2213 as a monoid homomorphism.  The proof
uses Quotient.map computation and the cocycle-level map_one/map_mul of
S2210CocyclePushforwardHom.

## Remaining exact missing

1. S2214H1RemainingData.finiteH1: forall n, Finite (H1(G_v,mu_{n!})).
2. S2214H1RemainingData.proj_surjective: surjectivity of S2214H1PushforwardHom.
3. lim1 H1 = 0 / S2114CompatibleRepresentativeLift.

Given S2214H1RemainingData, S2214ToS2145Instance constructs
S2145ActualMuH1Instance from the actual action tower S2196.

No finiteness/surjectivity/lim1 is claimed.
