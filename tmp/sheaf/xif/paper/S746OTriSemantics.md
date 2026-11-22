# S746: O^tri semantics and the q[2u] root

## Source evidence (tmp/source-extract/iut1.txt)

IUT I Example 3.5, lines 3774-3789:
  q[1u]_v[1u] is an element of O-triangle(TX_v[1u]) (≅ O-triangle_{Kv[1u]}).
  By the 2-torsion assumption and the definition of K [Def 3.1(c)],
  q[1u]_v[1u] admits a 2l-th root in O-triangle(TX_v[1u]).
  q[2u]_v[1u] := q[1u]_v[1u]^(1/2l) in O-triangle(TX_v[1u]).

IUT I Def 3.1(c), lines 3240-3248:
  K is the finite Galois extension of F determined by l-torsion;
  l is prime to the residue characteristics of Vbad and to the orders of the
  q-parameters of E_F at Vbad.

IUT I Example 3.5, lines 4216-4221 / 4264-4272:
  ord(O⊿_L) := O⊿_L / O_L^×;
  O⊿_{C⊣v}(-) = O^×_{C⊣v}(-) × (N·log(p_v)).

## Semantics

Ordinary integral O^tri_{K_v} is the monoid
  O^tri = O^× × N·log(p_v),
equivalently a unit part times a nonnegative p-adic exponent.  It is NOT
closed under 2l-th roots.

O-triangle(TX_v[1u]) in the q[2u] passage is the log/root-stack monoid
associated to the root stack TX_v, not the ordinary integral monoid
O-triangle_{K_v}.  The extra root operation is precisely the root-stack datum.

## Exact no-root statement

Let q[1u] = unit * p_v^{n}.  If n is not divisible by 2l, then q[1u] has no
2l-th root in the ordinary integral monoid: a root r=unit'*p_v^{m} would give
  2l * m = n,
contradicting 2l ∤ n.

Def 3.1(c) gives l ∤ n, hence 2l ∤ n.  Therefore q[2u] cannot exist in
ordinary O^tri_{K_v}; its source-defined existence is only in the log/root-stack
O^tri(TX_v).

## Lean

tmp/sheaf/xif/paper/S746OrdinaryOTriActual.lean defines
  OrdinaryOTri K = Kˣ × Nat  (unit part, exponent),
  pow r n = (r.unit^n, n * r.exponent),
  no_twoL_root_of_not_dvd : 2l ∤ n -> no r, r^(2l) = ofExponent u n,
  not_twoL_dvd_of_not_l_dvd : l ∤ n -> 2l ∤ n.

All actual, no AC/L root masquerade.
