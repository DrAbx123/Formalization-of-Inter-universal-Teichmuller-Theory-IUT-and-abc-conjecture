# S2320: component cast reduction — not completed

Date: 2026-11-02. Status: cast API is available, but the component hom reduction
to subtype.val is not proved. Naturality remains open. No fake, no IsStack claim.

## 1. Available cast API

- Types.equalizerIso_hom_comp_subtype:
    (equalizerIso g h).hom ≫ subtype.val = equalizer.ι g h
- Types.equalizerIso_inv_comp_ι:
    (equalizerIso g h).inv ≫ equalizer.ι g h = subtype.val
- limit.isoLimitCone_inv_π:
    (limit.isoLimitCone t).inv ≫ limit.π F j = t.cone.π.app j

## 2. Remaining

After composing the naturality square with Types.equalizerIso.hom at T2 and
applying Subtype.ext, the component hom still contains the composite

  eqToIso ≪≫ limitObjIsoLimitCompEvaluation ≪≫ isoOfNatIso ≪≫ equalizerIso.symm

and rfl/simp do not eliminate the eqToIso casts. The pullHom subtype.val
identity is also not proved.

## 3. Status

| Item | Status |
|---|---|
| cast API checked | YES |
| component hom cast reduction | MISSING |
| pullHom subtype.val identity | MISSING |
| final NatIso | MISSING |
| IsStack | not claimed |
| axioms | propext, Classical.choice, Quot.sound |

## Verification

- EXIT=0
- SHA256: d1ec3f5de641c03928ea23a484f40900808a2ba9f0f6815c1274b0db9eee2ecc
- olean: D:\lean\.lake\build\lib\lean\tmp\sheaf\xif\paper\S2320NatIsoCastActual.olean, size 3400
- axioms: propext, Classical.choice, Quot.sound.
