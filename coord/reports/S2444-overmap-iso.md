# S2444: exact missing Over compatibility functor iso; no inhabitant

Date: 2026-11-02.

Actual type definition:
  S2444OverMapCompatIsoType p :=
    (slicePush g) ⋙ (J.overMapPullback A (Over.Hom.left p))
      ≅ ((J.over X).overMapPullback A p) ⋙ (slicePush f)

No inhabitant is asserted. The direct candidate Iso.refl fails (composites are not definitionally equal). Construction needs:
1. sheafPushforwardContinuousIso applied to Over.iteratedSliceEquivOverMapIso p;
2. unit/counit cancellation between pushforward(forward f) and slicePush f = pushforward(backward f);
3. associativity/unit coherence to match the two composites.

Subagents for unit/counit and associativity produced no requested files; no integration.

No S2439PullHomCoherence, no SlicePushNaturality, no S2152QIsStack. No fake.

Verification:
- EXIT=0
- SHA256: ad36f71e040d37c114d560ce4f323d65d9a3af13ec08fb83ef1c4dcda90ce5a6
- olean: D:\lean\.lake\build\lib\lean\tmp\sheaf\xif\paper\S2444OverMapCompatIsoActual.olean, size 18840
- axioms: propext, Classical.choice, Quot.sound