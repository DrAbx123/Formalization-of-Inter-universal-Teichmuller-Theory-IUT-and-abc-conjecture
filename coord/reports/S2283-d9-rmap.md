# S2283: R.map naturality / equalizer iso — not completed

Date: 2026-11-02. Status: S2278 P_T/Q_T slice naturality is re-exported actual.
The R.map formula, f,g naturality and the ULift equalizer iso are not
constructed. No fake, no IsStack claim.

## 1. Actual re-export

S2283PT_natural: re-export of S2278PT_natural,
  p.unop.left ≫ S2267PT S M T1 = S2267PT S M T2.

## 2. Remaining exact first missing

The next step is to unfold S2192R := (Over.forget S).op ⋙ yoneda.obj S1726AffineOver
and obtain the explicit R.map formula, then prove

  R.map p (g • P_T2) = g • P_T1,
  R.map p (Q_T2) = Q_T1.

This is not done.  The orientation of R.map through Over.forget/yoneda and the
interaction with the explicit right action g |-> P ≫ S1971SchemeAut g was not
completed.

Without the R.map formula, the ULift equalizer iso
ULift(Q.presheafHom M N) ≅ Limits.equalizer f g
is also not constructed.

## 3. Status

| Item | Status |
|---|---|
| P_T/Q_T slice naturality | PROVED (re-export) |
| R.map formula | MISSING |
| f,g naturality | MISSING |
| ULift equalizer iso | MISSING |
| IsStack | not claimed |
| axioms | propext, Classical.choice, Quot.sound |

## Verification

- EXIT=0
- SHA256: 2209d9b7c88266446b8b1a3f9d3d9d2f76158c1a1086ba4ed3dd683d897f2883
- olean: D:\lean\.lake\build\lib\lean\tmp\sheaf\xif\paper\S2283QHomEqualizerFinal3Actual.olean, size 20872
- axioms: propext, Classical.choice, Quot.sound.
