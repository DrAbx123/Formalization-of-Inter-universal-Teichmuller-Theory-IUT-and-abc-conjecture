# S2323: presheaf-level equality route blocked by absence of univalence

Date: 2026-11-02. Status: the proposed equality
(Limits.equalizer (S2285f S M) (S2285g S N)).obj T = subtype
is not derivable from the available Iso data in Lean without univalence.
No fake, no IsStack claim.

## 1. Available

- S2312EqualizerSubtypeIso: equalizer.obj T ≅ {h // f_T h = g_T h}
- S2312QHomEqualizerObjIso: Q.obj T ≅ equalizer.obj T
- S2271QHomObj_eq_subtype: Q.obj T = {g // g•P_T=Q_T}
- S2322Comp: Q.obj T ≅ pointwise equalizer

## 2. Obstruction

An Iso (or Equiv) between types does not yield a type equality. eqToIso requires
an equality, not an isomorphism. The only available type equality is for
Q.obj T; there is no equality for the functor-category equalizer object. The
Types.equalizerIso hom/inv inverse laws give an Iso, not an equality, so the
proposed Presheaf.ext/funext route is blocked.

## 3. Status

| Item | Status |
|---|---|
| objectwise Iso data | AVAILABLE |
| pointwise type equality | NOT DERIVABLE (no univalence) |
| presheaf equality route | BLOCKED |
| final NatIso | MISSING |
| IsStack | not claimed |
| axioms | propext, Classical.choice, Quot.sound |

## Verification

- EXIT=0
- SHA256: 62608973ca340b9e9ac7954c7cf9ce661da5daa2a55176a89e342c319f31f4f5
- olean: D:\lean\.lake\build\lib\lean\tmp\sheaf\xif\paper\S2323PresheafEqActual.olean, size 3136
- axioms: propext, Classical.choice, Quot.sound.
