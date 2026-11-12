# S2191: Q hom equalizer identification — still missing; exact data fixed

Date: 2026-11-02. Status: the equalizer sheaf lemma is closed (S2181). The equalizer identification for S2152Q.presheafHom is not constructed. No IsStack claim, no fake.

## 1. Closed input

S2181EqualizerSheafLemma is proved: the pointwise equalizer of two sheaves of
types is a sheaf.

Therefore the Q hom-presheaf sheaf condition follows from the equalizer
identification alone:

  S2183QHomSheafFor_of_identification :
    S2168QHomEqualizerIdentification -> S2160QHomSheafFor.

## 2. S2191 package

File: tmp/sheaf/xif/paper/S2191QHomEqualizerIdActual.lean

- S2191QHomEqualizerIdentification := S2168QHomEqualizerIdentification.
- S2191QHomEqualizerIdentification_iff : Iff.rfl.
- S2191QHomSheafFor_of_identification:
    S2191QHomEqualizerIdentification -> S2160QHomSheafFor.
- S2191FirstMissing := S2191QHomEqualizerIdentification.

No equalizer data is constructed.

## 3. Exact data needed

For every S and M N in S2152Q.obj (op S), construct:

- P : (Over S)^op ⥤ Type, the constant sign group sheaf;
- R : (Over S)^op ⥤ Type, T |-> Hom(T.left, S1726AffineOver);
- hP : P is a sheaf for etaleTopology.over S;
- hR : R is a sheaf for etaleTopology.over S;
- f g : P ⟶ R, encoding
    f_T(x) = (x, x . P_T),
    g_T(x) = (x, Q_T),
  where P_T and Q_T are the underlying affine morphisms of the two
  action-category objects at T;
- iso : S2152Q.presheafHom M N ≅ Limits.equalizer f g.

The equalizer condition at x is x . P_T = Q_T, exactly the action-category hom
subtype.

## 4. Status

| Item | Status |
|---|---|
| equalizer sheaf lemma | PROVED (S2181) |
| constant sign group sheaf P | MISSING |
| representable morphism sheaf R | MISSING |
| f,g | MISSING |
| iso to equalizer | MISSING |
| S2160QHomSheafFor | conditional on identification |
| IsStack | not claimed |
| pointwise/label-only substitution | not used |
| S2103 SlicePushNaturality | independent, still missing |
| axioms | propext, Classical.choice, Quot.sound |

## Verification

- EXIT=0
- SHA256: 8bbc7e32f421aa1a3c0e1eed1a49499826e79122793d450b334cc598ae64343a
- olean: D:\lean\.lake\build\lib\lean\tmp\sheaf\xif\paper\S2191QHomEqualizerIdActual.olean, size 8384
- axioms: propext, Classical.choice, Quot.sound.
