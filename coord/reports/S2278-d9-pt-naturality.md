# S2278: P_T/Q_T naturality actual; R.map f,g and equalizer iso remain

Date: 2026-11-02. Status: the explicit P_T/Q_T formulas and their naturality in the
slice arrow are proved. The naturality of f,g as maps to R and the ULift
equalizer iso are still missing. No fake, no IsStack claim.

## 1. Actual results

File: tmp/sheaf/xif/paper/S2278QHomNaturalityActual.lean

- Global action instance S2278MulAtS:
    MulAction SignGroup
      (Opposite.unop (LocallyDiscrete.mk (op S)).as ⟶ S1726AffineOver).
- S2278PT_eq_comp:
    S2267PT S M T = T.unop.hom ≫ M.back.
- S2278QT_eq_comp:
    S2267QT S N T = T.unop.hom ≫ N.back.
- S2278PT_natural:
    for p : T1 ⟶ T2 in (Over S)^op,
      p.unop.left ≫ S2267PT S M T1 = S2267PT S M T2.
- S2278QT_natural: the analogous formula for Q_T.

Proofs: unfold PT/QT; use S2259QMap_obj_back; then the slice projection equation
Over.w p.unop and associativity.

Axioms: propext, Classical.choice, Quot.sound.

## 2. Remaining

1. Naturality of f_T(g) = g • P_T and g_T(g) = Q_T with respect to R.map p.
   This needs the explicit R.map formula from S2192R (orientation through
   Over.forget/yoneda).
2. Construct ULift(Q.presheafHom M N) ≅ Limits.equalizer f g using
   S2271QHomObj_eq_subtype pointwise and the above naturality.

## 3. Status

| Item | Status |
|---|---|
| explicit action instance | PROVED |
| P_T/Q_T formulas | PROVED |
| P_T/Q_T naturality | PROVED |
| R.map f,g naturality | MISSING |
| ULift equalizer iso | MISSING |
| IsStack | not claimed |
| axioms | propext, Classical.choice, Quot.sound |

## Verification

- EXIT=0
- SHA256: f5c899559eb7a4140d3ef7790e19cc15f67addcd19a442dbc2b4d32510d4d6e3
- olean: D:\lean\.lake\build\lib\lean\tmp\sheaf\xif\paper\S2278QHomNaturalityActual.olean, size 61384
- axioms: propext, Classical.choice, Quot.sound.
