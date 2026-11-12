# S2326: naive pointwise subtype presheaf is not functorial

Date: 2026-11-02. Status: the naive Psub with restriction g |-> g is not a
presheaf; the needed cancellation is unavailable. No fake, no IsStack claim.

## 1. Proposed Psub

Psub T := {g : SignGroup // g • P_T = Q_T}, with restriction g |-> g.

## 2. Obstruction

For p : T1 ⟶ T2 in (Over S)^op, S2278 gives

  p.unop.left ≫ P_T1 = P_T2,
  p.unop.left ≫ Q_T1 = Q_T2.

From the condition at T2,

  g • P_T2 = Q_T2

precomposing with p.unop.left is not possible in the direction needed; from the
condition at T1 one obtains

  p.unop.left ≫ (g • P_T1) = p.unop.left ≫ Q_T1,

which is the condition at T2, not at T1.  Cancelling p.unop.left is not
available (slice projections are not mono).  Hence g |-> g is covariant, not a
presheaf restriction; alternatively Psub needs a different restriction map or an
extra mono/epsi hypothesis.

## 3. Status

| Item | Status |
|---|---|
| naive Psub functor | NOT WELL-DEFINED |
| cancellation lemma | MISSING |
| final NatIso | MISSING |
| IsStack | not claimed |
| axioms | propext, Classical.choice, Quot.sound |

## Verification

- EXIT=0
- SHA256: 9823a65fddee551f1258fd591072eb5ff25fe26227c569d6441ff9db3604cd21
- olean: D:\lean\.lake\build\lib\lean\tmp\sheaf\xif\paper\S2326SubtypePresheafActual.olean, size 2960
- axioms: propext, Classical.choice, Quot.sound.
