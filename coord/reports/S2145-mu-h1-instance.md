# S2145: actual mu_{n!} coefficient tower and the H^1 instantiation gap

Date: 2026-11-02. Layer O. Consumer: S2142 / S2138 / S2114.

## File

tmp/sheaf/xif/paper/S2145MuH1InstanceActual.lean
Source SHA256 ef516e93d369dfd8c1b2c7a4c31fde7bc18cd4fda54cd73518f297335575198e
olean SHA256 4064523e412d7502097593993ed8dfd5e71c6ffd3e371c2e87db025eef9ac88b
EXIT=0. Axioms [propext, Classical.choice, Quot.sound].

## Actual construction

S2145Coeff p n := rootsOfUnity (n!) (AlgebraicClosure Q_p).
S2145PowMap p n : S2145Coeff p (n+1) ->* S2145Coeff p n is the actual power
map zeta |-> zeta^(n+1).
S2145Coeff_finite n : Finite (S2145Coeff p n).
S2145ToS2142 sends an actual instance (with action/H1 data) to
S2142ActualMuH1Tower.

## Correction: consecutive mu_n is not a tower

The requested coeff n = mu_n with transition mu_{n+1} -> mu_n has no natural
nontrivial map for consecutive n (the divisibility chain is needed; the power
map zeta |-> zeta^k only maps mu_m to mu_{m/k} when k | m).  The file therefore
uses the actual divisibility-chain tower mu_{n!}, with the power map
zeta |-> zeta^(n+1).  This is the same compatible-system convention as the
H2ZHat port (power maps on a divisibility chain), not a fake surrogate.

## Exact first missing

1. S2145TransitionSurjective p n: surjectivity of S2145PowMap p n.
2. S2145MuActionTower p: continuous G_v-action on the mu_{n!} tower,
   compatible with the power transitions.
3. S2145ActualMuH1Instance: finite level H^1 and h1Proj induced by the power
   maps, with h1Proj surjective.
4. lim^1 connecting map and lim^1 H^1 = 0, or directly the S2114
   compatible representative lift.

No unconditional surjectivity of h2Comparison and no CoboundaryLift is
claimed.
