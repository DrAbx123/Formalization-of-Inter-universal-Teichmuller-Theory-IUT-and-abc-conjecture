# S2160: Q hom-presheaf sheaf condition — exact first missing

Date: 2026-11-02. Status: S2158QHomSheaf is not proved. The exact first missing is recorded as S2160QHomSheafFor = S2158QHomSheaf; no IsStack claim and no fake sheaf instance.

## Target

S2160QHomSheafFor := S2158QHomSheaf:

  forall (S : SchemeOverField S1726K)
    (M N : S2152Q.obj (LocallyDiscrete.mk (op S))),
    Presheaf.IsSheaf (etaleTopology S1726K).over S
      (S2152Q.presheafHom M N).

This is the prestack half of S2158/S2152Q.

## Actual reductions

- S2160QHomSheafFirstMissing := S2160QHomSheafFor.
- S2160QHomSheafFirstMissing_iff_S2158:
    S2160QHomSheafFirstMissing <-> S2158QHomSheaf.
- S2158QPrestack_of_homSheafFirstMissing:
    S2160QHomSheafFirstMissing -> S2158QPrestack.
- S2160QEffectiveDescent l := S2158QEffectiveDescent l.
- S2160QRequiredAPI_iff:
    S2160QHomSheafFirstMissing / S2160QEffectiveDescent l <->
      Nonempty (S2158QRequiredAPI l).

No inhabitant of S2160QHomSheafFor is constructed.

## Why not proved

For fixed S,M,N, the value of S2152Q.presheafHom M N at a test object T is the
hom-type of the action category, i.e. a subtype of the finite sign group
{g : SignGroup // g . P_T = Q_T}.  A direct proof would need:

1. the restriction maps on this subtype are the identity on g;
2. the condition g . P_T = Q_T is local in T, i.e. the subpresheaf of the
   constant sign group is cut out by an equalizer of two maps into the
   representable sheaf T |-> Hom(T.left, S1726AffineOver);
3. closure of Presheaf.IsSheaf under that equalizer/subtype.

Mathlib v4.32.2 does not provide the required equalizer/subtype closure lemma in
the form needed, and the action-category hom formula has not been converted to
this equalizer shape in the tree yet.  No pointwise-only or label-only
substitution is used.

## S2103 independence

S2103 SlicePushNaturality / S2103FirstMissing remains independent; it concerns the
S2029 slice-sheaf prestack, not the S2152 pointwise colimit Q.

## Status

| Item | Status |
|---|---|
| Q hom-presheaf sheaf | MISSING |
| exact first missing | S2160QHomSheafFor |
| effective descent | MISSING |
| IsStack | not claimed |
| axioms | propext, Classical.choice, Quot.sound |

## Verification

- EXIT=0
- SHA256: a9b668f6bca9ef558eca4218d5d70db6010e374b98926893e4b2882910754fac
- olean: D:\lean\.lake\build\lib\lean\tmp\sheaf\xif\paper\S2160QHomSheafActual.olean, size 15072
- axioms: propext, Classical.choice, Quot.sound.
