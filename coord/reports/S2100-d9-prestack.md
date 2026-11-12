# S2100: D9 prestack half — slice pullback comparison, naturality exact missing

Date: 2026-11-02. Status: component functor comparison actual; naturality in the test object remains missing. No IsStack instance is produced.

## Layer

D9 prestack half (Route B, large Cat.{u+1,u+1} target). Not a pointwise/label-only construction, not S841/S853.

## Source objects

- F = S2029SheafPrestack K = (etaleTopology K).pseudofunctorOver (Type u).
- For S : SchemeOverField K and T : Over S:
  - F.presheafHom at T uses overMapPullback T.hom.
  - SheafHom at T uses the slice-site overPullback T.
- The iterated-slice equivalence T.iteratedSliceEquiv : Over T ~= Over T.left and
  Over.iteratedSliceBackward_forget T : T.iteratedSliceBackward >> Over.forget T = Over.map T.hom.

## Domain

S : SchemeOverField K, T : Over S, M N : sheaves on (etaleTopology K).over S with values in Type u.

## Direction

Actual natural isomorphism desired between the two hom presheaves; currently:
- actual functor iso at each T;
- naturality in T is the exact missing input.

## BUILT

File: tmp/sheaf/xif/paper/S2100D9PrestackNaturalityActual.lean

- S2100SlicePullbackIso S T:
    (J.overMapPullback (Type u) T.hom)
      ≅ ((J.over S).overPullback (Type u) T) ⋙
          T.iteratedSliceBackward.sheafPushforwardContinuous (Type u)
            (J.over T.left) ((J.over S).over T)
  Actual proof: Functor.sheafPushforwardContinuousComp plus
  Over.iteratedSliceBackward_forget T, using the continuity instances for
  Over.forget T, Over.map T.hom and iteratedSliceBackward.

- S2100SlicePullbackIso_actual: Nonempty form of the component iso.
- S2100PrestackNaturalityIso: exact naturality input,
    forall S M N, Nonempty (F.presheafHom M N ≅ (sheafHom M N).1).
- S2100SheafPrestack_of_naturality:
    S2100PrestackNaturalityIso -> S2093SheafPrestack K.

## PROVED

- The component comparison is actual and uses the Mathlib slice lemmas.
- If the naturality iso exists, the prestack half S2093SheafPrestack follows by
  Presheaf.isSheaf_of_iso_iff and the sheaf property of sheafHom.
- Axioms: propext, Classical.choice, Quot.sound for the component ISO and the
  conditional prestack theorem; no sorryAx, no new axiom.

## MISSING

S2100PrestackNaturalityIso: the naturality in T of the component identification.
Concretely, for p : T1 -> T2 one must compare:
- the pullHom action on F.presheafHom;
- the sheafHom map action;
using the compatibility of iteratedSliceEquiv with Over.map p (iteratedSliceForwardNaturalityIso /
iteratedSliceEquivOverMapIso) and the coherence of the pushforward composition.
This is the precise prestack-half first missing; it is not an IsStack/effective-descent claim.

Effective descent (S2093SheafEffectiveDescent) remains untouched.

## Consumer

S2100PrestackNaturalityIso -> S2093SheafPrestack -> S2050LargeSheafStackMissing (prestack half)
-> S2093LargeCFDataExact.

## No fake

No pointwise groupoid, label-only representable orbicurve, Shrink/ULift, or fabricated IsStack.
The conditional theorem does not assert its hypothesis.

## Verification

- EXIT=0
- SHA256: 4fbfcfd40a0923a14323b91a5ce2b46cca74f2393d1359217afd477b1d1c726b
- olean: D:\lean\.lake\build\lib\lean\tmp\sheaf\xif\paper\S2100D9PrestackNaturalityActual.olean, size 63640
- axioms: propext, Classical.choice, Quot.sound.
