# S2256: Type 1 equalizer identification attempt — still missing

Date: 2026-11-02. Status: Type 1 P and Type 0 R remain actual sheaves, but the
ULift Q hom presheaf, f,g and equalizer iso are not constructed. The suggested
S1971PointwiseQuotient_hom formula is recorded as the bridge, not proved here.
No fake, no IsStack claim.

## 1. Actual halves

S2256P = S2251P: Type 1 constant sign group sheaf, proved sheaf.

S2256R = S2251R: Type 0 representable morphism sheaf, proved sheaf.

## 2. Suggested pointwise formula

S1971PointwiseQuotient_hom gives, for action-category objects P Q,

  (P ⟶ Q) = { g : SignGroup // g • P.back = Q.back }.

The intended plan is:
- define the Type 1 ULift of S2152Q.presheafHom M N;
- define f_T(g) = (g, g • P_T) and g_T(g) = (g, Q_T) in the lifted product
  representable sheaf;
- use the subtype formula to prove
  ULift(Q.presheafHom M N) ≅ Limits.equalizer f g.

## 3. Why not completed

The term S2152Q.map (.toLoc T.unop.hom.op) is opaque from the pointwise
quotient perspective; extracting the two affine morphisms P_T and Q_T and
proving naturality of f,g through the ULift bridge requires additional lemmas
identifying Q.map with S1971PrecompFunctor and its object .back with the
precomposition formula. That identification was not completed.

Therefore S2256QHomSubtypeBridge is an abstract placeholder (alias of the Type 0
bridge), not actual data.

## 4. Status

| Item | Status |
|---|---|
| Type 1 P sheaf | PROVED |
| Type 0 R sheaf | PROVED |
| Q.map = S1971PrecompFunctor | MISSING |
| P_T/Q_T extraction | MISSING |
| f,g naturality | MISSING |
| ULift equalizer iso | MISSING |
| IsStack | not claimed |
| axioms | propext, Classical.choice, Quot.sound |

## Verification

- EXIT=0
- SHA256: 7e73bdb1842303a3644b1b85f5ebed9b723dbccc2142e88d76ec92c9194def59
- olean: D:\lean\.lake\build\lib\lean\tmp\sheaf\xif\paper\S2256QHomEqualizerType1IdActual.olean, size 12672
- axioms: propext, Classical.choice, Quot.sound.
