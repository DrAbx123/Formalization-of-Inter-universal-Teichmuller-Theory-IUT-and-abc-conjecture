# S2436: SlicePushNaturality reduced to exact pullHom coherence

Date: 2026-11-02.

S2436SlicePushProofActual.lean compiles EXIT=0 and isolates the exact goal.

After ext phi, change and unfolding slicePush/pullHom, the goal is:

  ((unop X2).iteratedSliceEquiv.inverse.sheafPushforwardContinuous ...).map
    (((J.over S).overMapPullback A f.unop).map phi)
  =
  ((J.pseudofunctorOver A).mapComp' ...).hom.toNatTrans.app M
    ≫ ((J.pseudofunctorOver A).map (Over.Hom.left f.unop).op.toLoc).toFunctor.map
        ((slicePush X1).map phi)
    ≫ ((J.pseudofunctorOver A).mapComp' ...).inv.toNatTrans.app N

This is the comparison between Over.overMapPullback and mapComp'/pullHom, mediated by
Over.iteratedSliceEquivOverMapIso. No proof completed; no SlicePushNaturality inhabitant.

Verification:
- EXIT=0
- SHA256: 2e0af11fc12ea80ec6358a622a16e1e5678b1a39c67e25dd6b02c9b7f24835be
- olean: D:\lean\.lake\build\lib\lean\tmp\sheaf\xif\paper\S2436SlicePushProofActual.olean, size 2672
- axioms: propext, Classical.choice, Quot.sound

Focused subagents dispatched: S2437 pullHom coherence, S2438 sign projection, S2436 Cech descent.