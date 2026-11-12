# S2181: equalizer sheaf lemma proved; Q hom-presheaf reduces to equalizer identification

Date: 2026-11-02. Status: the Mathlib equalizer sheaf lemma required by S2168 is now proved. The remaining input for S2160QHomSheafFor is only S2168QHomEqualizerIdentification. No IsStack claim.

## 1. Equalizer sheaf lemma

File: tmp/sheaf/xif/paper/S2181EqualizerSheafActual.lean

S2181EqualizerSheafLemma (C : Type 1) [Category.{v} C] (J) :
  S2168EqualizerSheafLemma C J.

Proof:
- Let F : WalkingParallelPair ⥤ (Cᵒᵖ ⥤ Type) be Limits.parallelPair f g.
- Its objects are P and R, both sheaves by hypothesis.
- The object property Presheaf.IsSheaf J is closed under limits of shape
  WalkingParallelPair (Sites.Limits, ObjectProperty.IsClosedUnderLimitsOfShape).
- ObjectProperty.prop_limit gives that limit F is a sheaf.
- Limits.equalizer f g is definitionally limit (parallelPair f g), so
  Presheaf.IsSheaf J (Limits.equalizer f g).

This closes the equalizer/sheaf API gap. Axioms: propext, Classical.choice,
Quot.sound.

## 2. Consequence for Q hom-presheaf

S2181QHomSheafFor_of_identification:
  S2168QHomEqualizerIdentification -> S2160QHomSheafFor.

This uses S2160QHomSheafFor_of_equalizer with the proved lemma at every slice
site.

## 3. Remaining exact first missing

S2181QHomEqualizerIdentificationFirstMissing :=
  S2168QHomEqualizerIdentification.

Need: for every S and M N in Q.obj (op S), exhibit sheaves P R on the slice site,
morphisms f g : P ⟶ R, and an isomorphism
  S2152Q.presheafHom M N ≅ Limits.equalizer f g.

Intended shape:
- P: constant sign group sheaf on the slice site;
- R: representable sheaf of morphisms into S1726AffineOver;
- f, g encode g |-> g . P_T and g |-> Q_T;
- the equalizer is the subtype {g : SignGroup // g . P_T = Q_T}.

This identification is not constructed. No pointwise-only or label-only
substitution is used.

## 4. Status

| Item | Status |
|---|---|
| equalizer sheaf lemma | PROVED |
| Q hom equalizer identification | MISSING exact |
| S2160QHomSheafFor | conditional on identification |
| IsStack | not claimed |
| S2103 SlicePushNaturality | independent, still missing |
| axioms | propext, Classical.choice, Quot.sound |

## Verification

- EXIT=0
- SHA256: 60fbaedefd8803622c8945cbaeca3a13062e5d183cec315c7ea4becf139150f6
- olean: D:\lean\.lake\build\lib\lean\tmp\sheaf\xif\paper\S2181EqualizerSheafActual.olean, size 38096
- axioms: propext, Classical.choice, Quot.sound.
