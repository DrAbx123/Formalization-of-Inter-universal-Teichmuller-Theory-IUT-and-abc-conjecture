# S2183: Q hom equalizer identification — exact first missing

Date: 2026-11-02. Status: the equalizer data for S2152Q.presheafHom is not constructed. S2181 already proves the equalizer sheaf lemma; the remaining exact first missing is only S2168QHomEqualizerIdentification. No IsStack claim, no fake.

## 1. Input

S2181EqualizerSheafLemma is proved: the pointwise equalizer of two sheaves of
types is a sheaf.

Hence S2160QHomSheafFor follows from the equalizer identification alone:

  S2181QHomSheafFor_of_identification :
    S2168QHomEqualizerIdentification -> S2160QHomSheafFor.

## 2. Current package

File: tmp/sheaf/xif/paper/S2183QHomEqualizerIdActual.lean

- S2183QHomEqualizerIdentification := S2168QHomEqualizerIdentification.
- S2183QHomEqualizerIdentification_iff : Iff.rfl.
- S2183QHomSheafFor_of_identification:
    S2183QHomEqualizerIdentification -> S2160QHomSheafFor.
- S2183FirstMissing := S2183QHomEqualizerIdentification.

No data or isomorphism is constructed.

## 3. Required identification

For every S : SchemeOverField S1726K and M N in S2152Q.obj (op S), construct:

- P : (Over S)^op ⥤ Type, the constant sign group sheaf;
- R : (Over S)^op ⥤ Type, the representable morphism sheaf into
  S1726AffineOver;
- hP : Presheaf.IsSheaf (etaleTopology.over S) P;
- hR : Presheaf.IsSheaf (etaleTopology.over S) R;
- f g : P ⟶ R, encoding g |-> g . P_T and g |-> Q_T;
- iso : S2152Q.presheafHom M N ≅ Limits.equalizer f g.

The equalizer value is the subtype

  {g : SignGroup // g . P_T = Q_T}

which is exactly the action-category hom formula.

This identification is missing.

## 4. Status

| Item | Status |
|---|---|
| equalizer sheaf lemma | PROVED (S2181) |
| Q hom equalizer identification | MISSING exact |
| S2160QHomSheafFor | conditional on identification |
| IsStack | not claimed |
| pointwise/label-only substitution | not used |
| S2103 SlicePushNaturality | independent, still missing |
| axioms | propext, Classical.choice, Quot.sound |

## Verification

- EXIT=0
- SHA256: 2dc4a4f31555e1b693396f014adc0ec81d14113a1562b036f7807905496baca5
- olean: D:\lean\.lake\build\lib\lean\tmp\sheaf\xif\paper\S2183QHomEqualizerIdActual.olean, size 9240
- axioms: propext, Classical.choice, Quot.sound.
