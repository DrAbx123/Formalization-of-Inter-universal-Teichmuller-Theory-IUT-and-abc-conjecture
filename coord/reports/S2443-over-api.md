# S2443: Over API compatibility — exact missing functor iso

Date: 2026-11-02.

Mathlib APIs available (checked):
- Over.iteratedSliceEquivOverMapIso (p : f ⟶ g) : f.iteratedSliceForward ⋙ Over.map p.left ⋙ g.iteratedSliceBackward ≅ Over.map p
- GrothendieckTopology.overMapPullback
- GrothendieckTopology.overMapPullbackComp
- Functor.sheafPushforwardContinuousComp
- Functor.sheafPushforwardContinuousIso

Exact missing construction: an actual functor isomorphism
  (slicePush g) ⋙ (J.overMapPullback A p.left)
    ≅ (J.overMapPullback A p) ⋙ (slicePush f)
or its object-level component equality (S2436 goal).  It is obtained by applying
sheafPushforwardContinuousIso to iteratedSliceEquivOverMapIso, then cancelling the
iteratedSliceEquiv unit/counit for f and g.  This cancellation was not constructed:
pushforward(forward f) is only inverse to slicePush f = pushforward(backward f) up to
the iteratedSliceEquiv unit/counit iso, and arranging the resulting composites to match
the S2436 RHS requires additional associativity/unit coherence not present as a named
Mathlib lemma.

No inhabitant of S2439PullHomCoherence or SlicePushNaturality is asserted. No fake.

Verification:
- EXIT=0
- SHA256: 53677dc8f441f4da0b470d7dcd6f29c7e0bfcf5219d5c3945f1f12d0368e28a9
- olean: D:\lean\.lake\build\lib\lean\tmp\sheaf\xif\paper\S2443OverMapCompatActual.olean, size 2888
- axioms: propext, Classical.choice, Quot.sound