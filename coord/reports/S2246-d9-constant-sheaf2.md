# S2246: universe-lifted correct P is actual; Type 0 bridge remains missing

Date: 2026-11-02. Status: Mathlib's plus construction gives HasWeakSheafify for Type 1 on the slice site. The universe-lifted constant sign group sheaf P is constructed and proved to be a sheaf. The Type 0 bridge remains the exact first missing. No fake, no IsStack claim.

## 1. Universe lift works

Mathlib (CategoryTheory/Sites/LeftExact.lean) provides an instance of
HasSheafify J (Type (max u v)).  For the slice site, the synthesis of

  HasWeakSheafify ((etaleTopology S1726K).over S) (Type 1)

succeeds (S2246HasWeakSheafifyUp_actual).

## 2. Actual lifted P

File: tmp/sheaf/xif/paper/S2246PConstantSheaf2Actual.lean

S2246P S :
  Sheaf ((etaleTopology S1726K).over S) (Type 1) :=
  (constantSheaf (etaleTopology.over S) (Type 1)).obj
    (ULift.{1,0} Iut.SignGroup).

S2246P_isSheaf S:
  Presheaf.IsSheaf (etaleTopology.over S) (S2246P S).1.

This is an actual constant sign group sheaf at universe Type 1.
Axioms: propext, Classical.choice, Quot.sound.

## 3. Exact first missing

S2246Type0Bridge S :=
  Nonempty (HasWeakSheafify (etaleTopology.over S) Type).

S2246FirstMissing S := S2246Type0Bridge S.

The original Type 0 constant sheaf is not constructed.  The lifted Type 1 P is
not automatically a Type 0 sheaf; a universe-lowering/transport bridge is
missing.  No Shrink or fake transport is used.

## 4. What this closes

- The universe-lifted constant sign group sheaf P exists and is a sheaf.
- The remaining gap for the original Q hom equalizer is a Type 0 bridge
  (or a parallel identification at Type 1 with ULift of the Q hom presheaf).

## 5. Status

| Item | Status |
|---|---|
| HasWeakSheafify at Type 1 | ACTUAL |
| lifted constant sign group sheaf P | BUILT + SHEAF PROVED |
| HasWeakSheafify at Type 0 | MISSING exact |
| Type 0 P | not constructed |
| R representable sheaf | PROVED |
| P0 literal constant presheaf | likely false, not used |
| f,g and equalizer iso | still missing |
| IsStack | not claimed |
| axioms | propext, Classical.choice, Quot.sound |

## Verification

- EXIT=0
- SHA256: 769e48a38958d77c8749750a4d11be5cbdc8fe591688bbc34e3d93eee737fe57
- olean: D:\lean\.lake\build\lib\lean\tmp\sheaf\xif\paper\S2246PConstantSheaf2Actual.olean, size 27040
- axioms: propext, Classical.choice, Quot.sound.
