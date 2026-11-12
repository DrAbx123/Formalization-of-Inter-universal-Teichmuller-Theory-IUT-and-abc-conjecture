# S2456: mapComp' app equals eqToIso coherence actual; action-on-x residual

Date: 2026-11-02. Serialized lake env lean -j1.

ACTUAL: S2456_app_eq_eqToIso:
  ((S2152PFunctor.toPseudofunctor'.mapComp' f g h hh).hom.toNatTrans.app M)
    = (eqToIso (S2456e f g h hh)).hom.toNatTrans.app M
where S2456e : S2152PFunctor.map h.as = S2152PFunctor.map f.as ≫ S2152PFunctor.map g.as, proved by cases hh; exact S2152PFunctor.map_comp f.as g.as.
Proof: cases hh; rfl. EXIT=0, olean 47712, SHA256 d107daed1fc25ca2ead561adf2ccce74f5af502b4786e62ec299ed0a6372d46a, axioms propext/Classical.choice/Quot.sound.

Residual: derive action-on-x of the eqToIso component (an eqToHom/natural-transformation component between equal functors), then compose with S1971PrecompFunctor_map_val. A direct simp attempt S2457 was too slow and was killed; no conclusion.

No general S2427SignProjection, no IsStack claim, no fake.