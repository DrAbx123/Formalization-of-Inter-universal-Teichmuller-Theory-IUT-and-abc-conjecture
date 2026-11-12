# S2263: Type 1 equalizer final step — not completed; exact blockers

Date: 2026-11-02. Status: Q.map = S1971PrecompFunctor re-exported actual. The f,g
maps and ULift equalizer iso are not constructed. The concrete Lean blocker is
recorded. No fake, no IsStack claim.

## 1. Actual re-export

S2263QMapPrecomp:
  for U V : LocallyDiscrete (SchemeOverField S1726K)^op and f : U ⟶ V,
  (S2152Q.map f).toFunctor = S1971PrecompFunctor f.

This is the actual S2259 result, re-exported.

## 2. Concrete blocker

To define P_T and Q_T via S2259QMap_obj_back, one must form

  ((S2152Q.map (T.unop.hom.op).toLoc).toFunctor.obj M).back

whose type is

  unop { as := op (unop T).left }.as ⟶ S1726AffineOver.

Lean cannot synthesize MulAction SignGroup on this point type from the
action-category instances available in scope.  Explicit letI attempts with
S1971PointMulAction on the corresponding LocallyDiscrete object did not unify
with the elaborated point type.

Without this instance, P_T/Q_T extraction, f_T(g) = g • P_T, and the naturality
of f,g cannot be written.  The ULift equalizer iso is then also blocked.

## 3. Exact first missing

The exact first missing is the point-type MulAction instance for

  T.unop.left ⟶ S1726AffineOver

at every T : (Over S)^op, compatible with the action-category instance used in
S1971PointwiseQuotient.

After that: define f,g, prove naturality, and construct
ULift(Q.presheafHom M N) ≅ Limits.equalizer f g.

## 4. Status

| Item | Status |
|---|---|
| Q.map = PrecompFunctor | PROVED (re-export) |
| P_T/Q_T extraction | BLOCKED on MulAction instance |
| f,g | MISSING |
| naturality | MISSING |
| ULift equalizer iso | MISSING |
| IsStack | not claimed |
| axioms | propext, Classical.choice, Quot.sound |

## Verification

- EXIT=0
- SHA256: d98516a19e25785d8e8244d992777a8f449f06bdd7c7b6a14ec4cfa86c9b7a75
- olean: D:\lean\.lake\build\lib\lean\tmp\sheaf\xif\paper\S2263QHomEqualizerFinalActual.olean, size 18904
- axioms: propext, Classical.choice, Quot.sound.
