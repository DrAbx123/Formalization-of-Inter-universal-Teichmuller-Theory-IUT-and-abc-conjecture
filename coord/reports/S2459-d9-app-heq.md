# S2459: app M HEq identity functor actual

Date: 2026-11-02. Serialized lake env lean -j1.

ACTUAL:
  S2459_app_heq :
    HEq ((S2152PFunctor.toPseudofunctor'.mapComp' f g h hh).hom.toNatTrans.app M)
        (𝟙 ((S2152PFunctor.toPseudofunctor'.map h).toFunctor.obj M))
Proof: cases hh; rfl. EXIT=0, olean 33960, SHA256 75e2bd4f7e6d1c4f1b99bf86e16d1f29ee4e7616820b33b77d743dda6de26759, axioms propext/Classical.choice/Quot.sound.

Interpretation: the mapComp' coherence app is HEq to the identity functor/morphism at the source object. This avoids the previous endpoint mismatch.

Remaining: use this HEq (eq_of_heq + Functor.congr_obj/congr_map) to prove the action-on-x equality, then S1971PrecompFunctor_map_val and S2427SignProjection.

No general S2427SignProjection, no IsStack claim, no fake.