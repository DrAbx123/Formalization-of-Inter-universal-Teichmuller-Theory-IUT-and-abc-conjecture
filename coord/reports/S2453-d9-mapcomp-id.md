# S2453: mapComp' base identity actual; action-on-x still missing

Date: 2026-11-02. Serialized lake env lean -j1 only.

ACTUAL: S2453_mapComp_fun_id:
  ((S2152PFunctor.toPseudofunctor'.mapComp' f g h hh).hom.toNatTrans.app M).1
    = 𝟙 ((S2152PFunctor.toPseudofunctor'.map h).toFunctor.obj M).fst
Proof: cases hh; rfl. EXIT=0, olean 54080, SHA256 7668353c2a4da87b4216c63335f3aeb3c5f2af778e9729b65b6bf27c7ed87155, axioms propext/Classical.choice/Quot.sound.

REMAINING: the app M is a subtype of a base morphism (or a functor between action categories); base identity is proved, but its action on the action-category hom x is not yet proved. The target general statement is S2427SignProjection.

No S2152QIsStack claim; no fake.

Files:
- S2453MapCompIdProofActual.lean: EXIT=0, olean 54080, SHA256 7668353c2a4da87b4216c63335f3aeb3c5f2af778e9729b65b6bf27c7ed87155, axioms ok.
- S2445SignProjectionActual.lean: identity p=1 case accepted.