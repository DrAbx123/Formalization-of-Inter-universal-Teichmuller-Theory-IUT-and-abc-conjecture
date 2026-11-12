# S2442: D9 actual-proof status — PullHomCoherence still missing

Date: 2026-11-02.

No new equivalent interface is claimed. The actual proof of S2439PullHomCoherence was attempted by unfolding slicePush (iteratedSliceEquiv.inverse.sheafPushforwardContinuous), Over.overMapPullback (sheafPushforwardContinuous of Over.map), pullHom, and mapComp' (overMapPullbackComp). The reduced goal remains S2436:

  (slicePush X2).map (overMapPullback f phi)
  = mapComp'.hom M ≫ map f.left (slicePush X1 phi) ≫ mapComp'.inv N

The missing compatibility is between Over.overMapPullbackComp and Over.iteratedSliceEquivOverMapIso. No inhabitant constructed.

Focused subagents S2440 (amalgamation) and S2441 (sign projection) produced no requested files; they produced unrelated files, so nothing is integrated.

Actual files:
- S2436SlicePushProofActual.lean EXIT=0 olean 2672 SHA256 2e0af11fc12ea80ec6358a622a16e1e5678b1a39c67e25dd6b02c9b7f24835be
- S2439D9ProofActual.lean EXIT=0 olean 62160 SHA256 31606f3f2e9b7b5b85af60aac201f6c0361db10bd8faf85d133a186907a7faf9
- S2425NatIsoCastHelpersActual.lean EXIT=0 olean 530872 accepted
- S2134D9DescentActual.lean EXIT=0 olean 476224 base cases accepted
- S2432PrestackCloseActual.lean rejected (literal sorry)

No S2152QIsStack claim. No fake.