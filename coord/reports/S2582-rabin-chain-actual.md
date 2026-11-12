# S2582 Rabin power-two chain ACTUAL

Date: 2026-11-03. Serial -j1.

## ACTUAL

tmp/sheaf/xif/paper/S2582PowerTwoChainAltActual.lean
  SHA256 A23AADDABA328C29EC4552D703A7F83A129CDEC1A3B1548B9EB9043982DC7BF0
  olean SHA256 519353AFB1E6131748D112BC468C079995D33DEF5ED1DDED2EFE78D04F3DFF04
  size 490440

Theorems (all axioms propext, Classical.choice, Quot.sound):
- chain (k <= 10): F | X^(2^k) - R k
- chain0 .. chain10

`chain10 : F ∣ X^(2^10) - R 10` is actual and kernel-clean.

## S2581 status

S2581PowerTwoChainCorrectActual was not compiled to an olean:
after fully qualifying the correct-batch names, serial compile exceeded the
600 s tool budget (no olean produced).  Likely bottleneck: `simpa [pow_two, pow_mul]`
+ maxRecDepth on the huge R polynomials.  Not used; S2582 replaces it.

## Correction to earlier counterexample

The earlier 'stepEq4 constant 1091 vs 573' check used the wrong R4 constant.
R4 constant is 1027 (R4^2 constant = 573), not 573.  The correct-batch
relation R4^2 = F10*Q4 + R5 is TRUE; the Python recomputation of all Rk/Qk
confirms the data.  The S2560 hollow-L/M batch is what was inconsistent.

## Status

- Rabin semantic chain first segment: ACTUAL via S2582.
- No fake; no sorryAx.
