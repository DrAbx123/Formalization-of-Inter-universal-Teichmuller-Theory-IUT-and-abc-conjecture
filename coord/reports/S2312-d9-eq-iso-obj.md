# S2312: Q hom = equalizer objectwise actual; final NatIso naturality missing

Date: 2026-11-02. Status: using Mathlib Limits.Types.equalizerIso, the objectwise
iso

  (S2152Q.presheafHom M N).obj T ≅
    (Limits.equalizer (S2285f S M) (S2285g S N)).obj T

is actual. The final natural isomorphism (naturality of these components) is not
completed. No fake, no IsStack claim.

## 1. Actual

S2312EqualizerSubtypeIso:
  (Limits.equalizer (S2285f S M) (S2285g S N)).obj T
    ≅ {h : SignGroup // S2267fPoint S M T h = S2267gPoint S N T h}
by S2308EqualizerObjIso ≪≫ Limits.Types.equalizerIso.

S2312QHomEqualizerObjIso:
  (S2152Q.presheafHom M N).obj T
    ≅ (Limits.equalizer (S2285f S M) (S2285g S N)).obj T
by eqToIso (S2271QHomObj_eq_subtype) ≪≫ (S2312EqualizerSubtypeIso).symm.

Axioms: propext, Classical.choice, Quot.sound.

## 2. Missing final NatIso

NatIso.ofComponents with S2312QHomEqualizerObjIso leaves a naturality square
that is not rfl; the goal after ext x is an equality of composite functions
through (presheafHom).map and (equalizer).map, involving the eqToIso/equalizerIso
components. It was not closed.

## 3. Status

| Item | Status |
|---|---|
| pointwise equalizer object iso | PROVED (S2308) |
| equalizer → subtype iso | PROVED |
| Q hom → equalizer objectwise iso | PROVED |
| final NatIso | MISSING naturality |
| IsStack | not claimed |
| axioms | propext, Classical.choice, Quot.sound |

## Verification

- EXIT=0
- SHA256: 100beecce8c230621ab398bdd31cd24867109862c39711a510031d27ee8532a3
- olean: D:\lean\.lake\build\lib\lean\tmp\sheaf\xif\paper\S2312EqualizerIsoFinal2Actual.olean, size 43112
- axioms: propext, Classical.choice, Quot.sound.
