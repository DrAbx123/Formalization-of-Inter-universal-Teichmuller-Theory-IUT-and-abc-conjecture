# S2451: sign projection — identity case actual; general case blocked

Date: 2026-11-02. Serialized lake env lean -j1 only; no lake build.

ACTUAL:
- S2445_signProjection_id (tmp/sheaf/xif/paper/S2445SignProjectionActual.lean):
  (S2427Comp T).hom (Q.presheafHom.map (1 : T) x) = S2332Psub.map (1 : T) ((S2427Comp T).hom x).
  EXIT=0, olean 55640, SHA256 240d5ca2de3cfe5ca7d6a7f0266411a7c9cf9ca1c88e83d71d2e594319e2be44, axioms propext/Classical.choice/Quot.sound.

GENERAL:
- S2446SignProjectionGeneralActual.lean attempts S2427SignProjection. EXIT!=0; unsolved goal after unfolding and Subtype.ext is the pullHom composite equality containing S2152PFunctor.toPseudofunctor'.mapComp'.
- Critical type diagnosis: S2152PFunctor.toPseudofunctor'.mapComp' app M is a subtype of a base function (a functor between action categories), NOT an action-category hom label. Therefore the earlier plan of proving a label = 1 is ill-typed; the coherent functor-level identity/action-on-x lemma is the actual missing input.
- No general S2427SignProjection inhabitant. No fake.

Subagent/Cech branch: no delivered file in this round.

Files:
- S2445SignProjectionActual.lean: EXIT=0, olean 55640, SHA256 240d5ca2de3cfe5ca7d6a7f0266411a7c9cf9ca1c88e83d71d2e594319e2be44, axioms ok.
- S2446SignProjectionGeneralActual.lean: EXIT!=0, no olean. Source only.
- S2447/S2448 attempts: EXIT!=0 (type diagnosis only), no olean.

No S2152QIsStack claim.