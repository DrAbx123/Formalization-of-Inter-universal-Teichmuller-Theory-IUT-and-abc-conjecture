# S2452: functor-level mapComp identity — exact goal, not proved

Date: 2026-11-02. Serialized lake env lean -j1 only.

Attempt: for the app M of S2152PFunctor.toPseudofunctor'.mapComp', prove the underlying base morphism is identity:
  ((S2152PFunctor.toPseudofunctor'.mapComp' f g h hh).hom.toNatTrans.app M).1 = 1

Lean type: the app is a subtype of a base morphism between ((map h).obj M).fst and ((map f ≫ map g).obj M).fst; .1 is that base morphism. rfl does not prove it equals the identity; exact residual goal is:

  ↑((S2152PFunctor.toPseudofunctor'.mapComp' f g h hh).hom.toNatTrans.app M)
    = 𝟙 ((S2152PFunctor.toPseudofunctor'.map h).toFunctor.obj M).fst

No proof. The missing input is the functor-level identity/action-on-x lemma; label-level .val is ill-typed.

ACTUAL from previous: S2445_signProjection_id identity case EXIT=0 olean 55640 SHA256 240d5ca2de3cfe5ca7d6a7f0266411a7c9cf9ca1c88e83d71d2e594319e2be44 axioms ok.

S2452 source SHA256: 4736fe7065072762a4d83ca5a09b246618af40a887e2eb409a127d0f3f50b3a6; EXIT!=0, no olean.

No S2152QIsStack claim, no fake.