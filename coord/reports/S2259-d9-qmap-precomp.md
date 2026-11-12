# S2259: Q.map = S1971PrecompFunctor actual; back formula actual

Date: 2026-11-02. Status: the first small step is complete. The map of the actual
pointwise colimit Q is definitionally the precomposition functor, and its object
.back formula is proved. No IsStack claim.

## 1. Actual theorem

File: tmp/sheaf/xif/paper/S2259QMapPrecompActual.lean

For U V : LocallyDiscrete (SchemeOverField S1726K)^op and f : U ⟶ V:

  S2259QMapPrecomp :
    (S2152Q.map f).toFunctor = S1971PrecompFunctor f

Proof: rfl, from S2152Q := S2152PFunctor.toPseudofunctor' and the definition of
S2152PFunctor.map.

Object-level back formula:

  S2259QMap_obj_back (P : S1971PointwiseQuotient U) :
    ((S2152Q.map f).toFunctor.obj P).back = f.as.unop ≫ P.back

Proof: rw [S2259QMapPrecomp]; exact S1971PrecompFunctor_obj_back f P.

Axioms: propext, Classical.choice, Quot.sound.

## 2. Consequence

P_T extraction from the action-category value is now reduced to the back formula.
For T : Over S, the Q hom value is the action-category Hom type, and the
underlying affine morphism at T is obtained by applying the above formula to the
appropriate precomposition arrow.

## 3. Remaining first missing

- define f,g : P ⟶ R for Type 1 lifted P and R, with f_T(g) = (g, g • P_T),
  g_T(g) = (g, Q_T);
- prove naturality of f,g through the ULift bridge;
- construct ULift(Q.presheafHom M N) ≅ Limits.equalizer f g.

## 4. Status

| Item | Status |
|---|---|
| Q.map = S1971PrecompFunctor | PROVED |
| back formula | PROVED |
| P_T/Q_T extraction | next |
| f,g naturality | MISSING |
| ULift equalizer iso | MISSING |
| IsStack | not claimed |
| axioms | propext, Classical.choice, Quot.sound |

## Verification

- EXIT=0
- SHA256: 8e800dbeb76d41b5b61e2e60b97eb52e045f95cd1c21178e87d93b09c5e28f99
- olean: D:\lean\.lake\build\lib\lean\tmp\sheaf\xif\paper\S2259QMapPrecompActual.olean, size 29448
- axioms: propext, Classical.choice, Quot.sound.
