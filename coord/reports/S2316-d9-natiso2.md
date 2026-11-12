# S2316: final NatIso naturality — still missing

Date: 2026-11-02. Status: naturality is not closed. Zero/one goals after
ext x; cases x still contain the composite components
(eqToIso ≪≫ limitObjIsoLimitCompEvaluation ≪≫ isoOfNatIso ≪≫ equalizerIso).symm
and pullHom; rfl and rw [S2285f_natural] do not apply. No fake, no IsStack claim.

## 1. Actual base

S2312QHomEqualizerObjIso: objectwise Q hom ≅ equalizer.
S2285f_natural / S2285g_natural: f/g naturality.
S2285R_map_apply: R.map formula.

## 2. Failed naturality shape

After NatIso.ofComponents, ext x, cases x:

zero/one goals still have the form

  ((presheafHom).map p ≫ component T2.hom ≫ limit.π ...).toFun x
    = (component T1.hom ≫ (equalizer).map p ≫ limit.π ...).toFun x

with component = eqToIso ≪≫ (limitObjIso ≪≫ isoOfNatIso ≪≫ equalizerIso).symm.
The pullHom restriction and the eqToIso casts prevent rfl/rw [S2285f_natural].

## 3. Status

| Item | Status |
|---|---|
| objectwise iso | PROVED (S2312) |
| final NatIso naturality | MISSING |
| IsStack | not claimed |
| axioms | propext, Classical.choice, Quot.sound |

## Verification

- EXIT=0
- SHA256: 4832cf671bfc2a6c9c34a4a0d06590fd3cb098a0b2f0c9de0e60516f4812b14a
- olean: D:\lean\.lake\build\lib\lean\tmp\sheaf\xif\paper\S2316NatIsoProofActual.olean, size 2960
- axioms: propext, Classical.choice, Quot.sound.
