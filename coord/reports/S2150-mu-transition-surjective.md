# S2150: surjectivity of the mu_{(n+1)!} -> mu_{n!} power transition

Date: 2026-11-02. Layer O. Consumer: S2145 / S2142 / S2138 / S2114.

## File

tmp/sheaf/xif/paper/S2150MuTransitionActual.lean
Source SHA256 dbce13d999a223e0cd773784cd618af3aa56dfc18fefa38af5b935c08fc9137e
olean SHA256 75802ad7da92b3cfaf4a1bcc6c040f687c2371246d114f851c6fb467aaa84de2
EXIT=0. Axioms [propext, Classical.choice, Quot.sound].

## Proved

S2150Transition_surjective (p) (n):
  Function.Surjective (S2145PowMap p n),
where S2145PowMap p n : mu_{(n+1)!} ->* mu_{n!}, zeta |-> zeta^(n+1).

Proof: the source mu_{(n+1)!} is cyclic; take a generator zeta. Its order is
(n+1)!. The order of eta = zeta^(n+1) is
  (n+1)! / gcd((n+1)!, n+1) = (n+1)!/(n+1) = n!,
which equals the cardinality of the target mu_{n!}; hence
Subgroup.zpowers eta = top and every target element is eta^k = (zeta^k)^(n+1).
The source cardinalities use HasEnoughRootsOfUnity for AlgebraicClosure Q_p and
natCard_rootsOfUnity; the power order uses orderOf_pow'.

## Exact remaining first missing

1. S2145MuActionTower: continuous G_v-action on mu_{n!} compatible with the
   power maps zeta |-> zeta^(n+1).
2. S2145ActualMuH1Instance: Finite (H1(G_v, mu_{n!})) and h1Proj surjective.
3. lim^1 connecting map and lim^1 H1 = 0, or directly the S2114 compatible
   representative lift.

No unconditional surjectivity of h2Comparison or CoboundaryLift is claimed.
