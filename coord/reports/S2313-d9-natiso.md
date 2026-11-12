# S2313: final NatIso naturality — not closed; minimal goals

Date: 2026-11-02. Status: S2312 objectwise iso remains actual. The final
NatIso naturality is not closed; the two minimal remaining goals are recorded.
No fake, no IsStack claim.

## 1. Actual input

S2312QHomEqualizerObjIso:
  (S2152Q.presheafHom M N).obj T
    ≅ (Limits.equalizer (S2285f S M) (S2285g S N)).obj T.

## 2. Minimal remaining naturality goals

After NatIso.ofComponents and ext x, cases x reduces to:

zero:
  (Fork.ι Types.equalizerLimit.cone)
    (pullHom x (p.unop.left) ...) =
  (S2206P0 S).map p ((Fork.ι ...) x)

one:
  (S2285f S M).app T2 ((Fork.ι ...) (pullHom x ...)) =
  (S2192R S).map p ((S2285f S M).app T1 ((Fork.ι ...) x))

The two issues are:
- identifying pullHom x (Over.Hom.left p.unop) with the Q hom restriction used
  by presheafHom.map p;
- rewriting the first component via S2285f_natural after that identification.

No naturality theorem is asserted.

## 3. Status

| Item | Status |
|---|---|
| objectwise iso | PROVED (S2312) |
| final NatIso | MISSING naturality |
| IsStack | not claimed |
| axioms | propext, Classical.choice, Quot.sound |

## Verification

- EXIT=0
- SHA256: 6342a1fa8ca47ad703d20658a5f72113b78cdf01340d2d6267a66a1e245e210e
- olean: D:\lean\.lake\build\lib\lean\tmp\sheaf\xif\paper\S2313NatIsoFinalActual.olean, size 2960
- axioms: propext, Classical.choice, Quot.sound.
