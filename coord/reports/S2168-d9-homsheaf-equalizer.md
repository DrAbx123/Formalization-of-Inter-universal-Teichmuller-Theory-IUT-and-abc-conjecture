# S2168: Q hom-presheaf equalizer form — exact Mathlib sheaf lemma and first missing

Date: 2026-11-02. Status: no proof of S2160QHomSheafFor. The equalizer form and the exact Mathlib equalizer sheaf lemma are fixed; the conditional implication to Q hom-presheaf sheaf is proved.

## 1. Required Mathlib equalizer sheaf lemma

File: tmp/sheaf/xif/paper/S2168QHomSheafEqualizerActual.lean

S2168EqualizerSheafLemma (C) (J) : Prop :=

  forall (P R : Cᵒᵖ ⥤ Type)
    (hP : Presheaf.IsSheaf J P) (hR : Presheaf.IsSheaf J R)
    (f g : P ⟶ R),
    Presheaf.IsSheaf J (Limits.equalizer f g).

This is the exact equalizer/subtype sheaf lemma needed: the pointwise equalizer
of two morphisms of sheaves of types is a sheaf.

Mathlib v4.32.2 does not provide this lemma in this form.  No instance or
inhabitant is asserted.

## 2. Equalizer data for Q

S2168QHomEqualizerData S M N:

- P R : ((Over S)ᵒᵖ ⥤ Type);
- hP hR : Presheaf.IsSheaf (etaleTopology.over S) P/R;
- f g : P ⟶ R;
- iso : S2152Q.presheafHom M N ≅ Limits.equalizer f g.

S2168QHomEqualizerIdentification : Prop :=
  forall S M N, Nonempty (S2168QHomEqualizerData S M N).

S2168QHomEqualizerFirstMissing := S2168QHomEqualizerIdentification.

## 3. Conditional actual theorem

S2160QHomSheafFor_of_equalizer:
  (forall S, S2168EqualizerSheafLemma (Over S) (etaleTopology.over S)) ->
  S2168QHomEqualizerIdentification ->
  S2160QHomSheafFor.

Proof: for each S,M,N, the data gives an isomorphism from the Q hom-presheaf to
the equalizer of two sheaf morphisms; the lemma makes that equalizer a sheaf;
Presheaf.isSheaf_of_iso_iff transfers the sheaf property back to the Q
hom-presheaf.

Axioms: propext, Classical.choice, Quot.sound.

## 4. What is missing

1. S2168EqualizerSheafLemma: the equalizer of two sheaf morphisms of types is a
   sheaf.  A direct proof would use closure of Presheaf.IsSheaf under limits,
   or the fact that the forgetful functor Sheaf J (Type) -> presheaf creates
   limits.
2. S2168QHomEqualizerIdentification: for each S,M,N, exhibit the actual
   sheaves P,R and maps f,g whose equalizer is S2152Q.presheafHom M N.
   The intended shape: P is the constant sign group, R is the representable
   sheaf of morphisms into S1726AffineOver, and the two maps encode
   g |-> g . P_T and g |-> Q_T.

Neither is constructed.

## 5. Status

| Item | Status |
|---|---|
| equalizer sheaf lemma | MISSING exact |
| Q hom-presheaf equalizer identification | MISSING exact |
| conditional implication to S2160QHomSheafFor | PROVED |
| IsStack | not claimed |
| pointwise/label-only substitution | not used |
| axioms | propext, Classical.choice, Quot.sound |

## Verification

- EXIT=0
- SHA256: db4c9e73c86bbfeca4cbeb5890cd731d4733c70663b1521ae26e9192a5c6ed8f
- olean: D:\lean\.lake\build\lib\lean\tmp\sheaf\xif\paper\S2168QHomSheafEqualizerActual.olean, size 185240
- axioms: propext, Classical.choice, Quot.sound.
