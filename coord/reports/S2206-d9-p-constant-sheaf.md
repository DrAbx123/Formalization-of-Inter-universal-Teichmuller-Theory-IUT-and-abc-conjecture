# S2206: literal constant sign group presheaf P0 and representable sheaf R

Date: 2026-11-02. Status: P0 is constructed as an actual constant presheaf; R is the actual representable morphism sheaf. The P0 sheaf property is the exact remaining first missing. No IsStack claim, no fake.

## 1. P0 actual

File: tmp/sheaf/xif/paper/S2206PConstantSheafActual.lean

S2206P0 S : (Over S)^op ⥤ Type:
  obj _ := Iut.SignGroup
  map _ := identity function
  map_id, map_comp := rfl.

This is the literal constant sign group presheaf on the slice site.

## 2. R actual

S2206R S := S2192R S = (Over.forget S).op ⋙ yoneda.obj S1726AffineOver.

S2206R_isSheaf S:
  Presheaf.IsSheaf (etaleTopology.over S) (S2206R S).

This is actual, from S2192.

## 3. Exact first missing

S2206P0Sheaf S : Prop :=
  Presheaf.IsSheaf (etaleTopology.over S) (S2206P0 S).

S2206FirstMissing S := S2206P0Sheaf S.

Equivalently, the alternative constant-sheaf API is

S2192HasWeakSheafify S :=
  Nonempty (HasWeakSheafify (etaleTopology.over S) Type),

and S2206PFirstMissing S := S2206P0Sheaf S \/ S2192HasWeakSheafify S.

The literal constant presheaf is not yet proved to be a sheaf.  The constant
sheaf construction via HasWeakSheafify is also not available as a global
instance.

## 4. Conditional P/R package

S2206HomSheaves S (hP : S2206P0Sheaf S):
  P := S2206P0 S, R := S2206R S, hP' := hP, hR := S2206R_isSheaf S.

S2206HomSheaves_actual S hP : S2206HomSheaves S hP.

So the P/R package is actual as soon as the literal constant presheaf is proved
to be a sheaf.

## 5. Status

| Item | Status |
|---|---|
| literal P0 presheaf | BUILT |
| P0 sheaf property | MISSING exact |
| R representable sheaf | BUILT + PROVED |
| P/R package | conditional on P0 sheaf |
| HasWeakSheafify alternative | MISSING |
| f,g and equalizer iso | still missing |
| IsStack | not claimed |
| pointwise/label-only substitution | not used |
| axioms | propext, Classical.choice, Quot.sound |

## Verification

- EXIT=0
- SHA256: 6294ddaade67059f7887c7f0059419bfd31e4eeb07b5d70cf3591489c11fdc83
- olean: D:\lean\.lake\build\lib\lean\tmp\sheaf\xif\paper\S2206PConstantSheafActual.olean, size 78480
- axioms: propext, Classical.choice, Quot.sound.
