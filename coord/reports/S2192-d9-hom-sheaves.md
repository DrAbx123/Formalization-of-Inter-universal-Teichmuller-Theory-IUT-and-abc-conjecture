# S2192: Q hom equalizer P/R halves — R actual, P conditional on constant-sheaf API

Date: 2026-11-02. Status: the representable morphism sheaf R is constructed and proved to be a sheaf. The constant sign group sheaf P is constructed only conditionally on HasWeakSheafify for Type on the slice site. No IsStack claim, no fake.

## 1. R: representable morphism sheaf

File: tmp/sheaf/xif/paper/S2192QHomSheavesActual.lean

R S : (Over S)^op ⥤ Type :=
  (Over.forget S).op ⋙ yoneda.obj S1726AffineOver.

At T it is Hom(T.left, S1726AffineOver).

S2192R_isSheaf:
  Presheaf.IsSheaf (etaleTopology S1726K).over S (S2192R S).

Proof:
- representableEtalePresheaf_isSheaf (F := S1726K) S1726AffineOver:
    Presheaf.IsSheaf (etaleTopology S1726K) (yoneda.obj S1726AffineOver);
- Over.forget S is continuous from (etaleTopology.over S) to etaleTopology;
- op_comp_isSheaf_of_isSheaf_type transfers the sheaf property.

This is an actual construction and actual sheaf proof. Axioms: propext,
Classical.choice, Quot.sound.

## 2. P: constant sign group sheaf

S2192HasWeakSheafify S : Prop :=
  Nonempty (HasWeakSheafify (etaleTopology.over S) Type).

S2192P S (h : S2192HasWeakSheafify S) :
  Sheaf (etaleTopology.over S) (Type) :=
  (constantSheaf (etaleTopology.over S) (Type)).obj SignGroup,
using h.some as the instance.

S2192P_isSheaf h : Presheaf.IsSheaf (etaleTopology.over S) (S2192P S h).1.

P is therefore conditional on the exact missing API
HasWeakSheafify (etaleTopology.over S) Type.  Mathlib has no global instance
for Type-valued sheafification on an arbitrary slice site.

## 3. P/R package

structure S2192HomSheaves (h : S2192HasWeakSheafify S):
  P, R : (Over S)^op ⥤ Type;
  hP, hR : Presheaf.IsSheaf (etaleTopology.over S) P/R.

S2192HomSheaves_actual h : S2192HomSheaves S h,
with P := S2192P.1, R := S2192R, hP := S2192P_isSheaf h, hR := S2192R_isSheaf.

## 4. Exact first missing

S2192FirstMissing S := S2192HasWeakSheafify S.

This is the only missing API for the P half.  R is closed.

Note: an alternative P as a literal constant presheaf would require a direct
proof that the constant presheaf of SignGroup is a sheaf for the slice etale
topology; that proof is not in the tree, so the constant-sheaf API is recorded
instead.

## 5. Status

| Item | Status |
|---|---|
| R representable sheaf | BUILT + SHEAF PROVED |
| P constant sign group sheaf | conditional on S2192HasWeakSheafify |
| P/R package | conditional |
| f,g and iso to equalizer | still missing |
| IsStack | not claimed |
| pointwise/label-only substitution | not used |
| axioms | propext, Classical.choice, Quot.sound |

## Verification

- EXIT=0
- SHA256: 4c29e3a51b98ec7dab87186e9c2771631c8de1d5efce7bd081c89a9a33ed3e54
- olean: D:\lean\.lake\build\lib\lean\tmp\sheaf\xif\paper\S2192QHomSheavesActual.olean, size 82920
- axioms: propext, Classical.choice, Quot.sound.
