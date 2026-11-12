# S2271: pointwise Q hom subtype actual; naturality/equalizer iso missing

Date: 2026-11-02. Status: the pointwise subtype formula for the Q hom-presheaf
is proved using S1971PointwiseQuotient_hom and the explicit S2267 action. The
natural transformations f,g and the ULift equalizer iso are still missing. No
fake, no IsStack claim.

## 1. Actual theorem

File: tmp/sheaf/xif/paper/S2271QHomEqualizerNatActual.lean

S2271QHomObj_eq_subtype:

  forall (M N : S2152Q.obj (op S)) (T : (Over S)^op),
    (S2152Q.presheafHom M N).obj T =
      { g : SignGroup // g • S2267PT S M T = S2267QT S N T }.

Proof:
- unfold the presheafHom value to the action-category Hom type
  (P ⟶ Qv), with P and Qv the precomposition images of M and N;
- apply S1971PointwiseQuotient_hom with U = LocallyDiscrete.mk (op T.left);
- S2267PT/S2267QT are exactly P.back/Qv.back.

Axioms: propext, Classical.choice, Quot.sound.

## 2. Consequences

The Q hom type is now explicitly the subtype cut out by the affine equality
g • P_T = Q_T.  This is the pointwise equalizer condition.

## 3. Remaining first missing

- Prove naturality of f_T(g) = g • P_T and g_T(g) = Q_T in T.
- Construct the natural isomorphism
  ULift(Q.presheafHom M N) ≅ Limits.equalizer f g.

The pointwise subtype is available; naturality through the presheaf restriction
maps is the next step.

## 4. Status

| Item | Status |
|---|---|
| pointwise subtype formula | PROVED |
| P_T/Q_T | BUILT |
| pointwise f,g | BUILT |
| naturality | MISSING |
| ULift equalizer iso | MISSING |
| IsStack | not claimed |
| axioms | propext, Classical.choice, Quot.sound |

## Verification

- EXIT=0
- SHA256: b06b3976edd8c6f0fc50e81490f1c5dad13da8821c6a102716e5a15373125d45
- olean: D:\lean\.lake\build\lib\lean\tmp\sheaf\xif\paper\S2271QHomEqualizerNatActual.olean, size 29032
- axioms: propext, Classical.choice, Quot.sound.
