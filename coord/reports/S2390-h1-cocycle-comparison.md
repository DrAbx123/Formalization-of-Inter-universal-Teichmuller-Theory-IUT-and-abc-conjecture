# S2390: continuous 1-cocycle comparison and the quotient gap

Date: 2026-11-02. Layer O. Consumer: S2384 / S2372 / S2204.

## File

tmp/sheaf/xif/paper/S2390H1ComparisonDoneActual.lean
Source SHA256 97a6a6d0b807f6c763589e1ab78d9ae0cc8b81e7adb8cd1185076b768006ce1b
olean SHA256 c356bf7e0d574f4e1f34a20f38e75b3f283004a411a549b4f84105db9d61b0a8
EXIT=0. Axioms [propext, Classical.choice, Quot.sound].

## Built

A local MulDistribMulAction of G_v on mu_{n!} is induced from the actual
ContinuousGroupAction automorphism.
S2390ToExternalCocycle maps an internal Iut.ContinuousOneCocycle to an external
ContH1.cocycles by the identity on the underlying function; the external
cocycle law g • f h * f g is obtained from the internal law
f g * act_g f h by commutativity.
S2390OfExternalCocycle is the inverse map; S2390OfTo and S2390ToOf prove the
round trips, so the continuous 1-cocycle carriers are equivalent.

## Exact first missing

The quotient-level equivalence
S2390H1ComparisonRequired:
  S2204H1 p n ≃ ContH1 (LocalAbsoluteGalois p) (S2145Coeff p n).
It remains to prove the coboundary correspondence:
internal Cohomologous (twist a) corresponds to external
IsMulCoboundary₁ (g • x / x) with x = a, then pass to the quotients.
The cocycle-level bijection is actual; only this relation/quotient step and the
Quotient.map construction remain.

Once S2390H1ComparisonRequired is inhabited, S2384FiniteH1OfComparison gives
Finite (S2204H1 p n).  No unconditional Finite or surjectivity is claimed.
