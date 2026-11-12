# S2421: mapComp' app check output unchanged; identity coherence not extracted

Date: 2026-11-02.

#check output:

  (S2152Q.mapComp' f g h hh).hom.toNatTrans.app M :
    (S2152Q.map h).toFunctor.obj M ⟶ (S2152Q.map f ≫ S2152Q.map g).toFunctor.obj M

This is an action-category hom, but the .val lemma is still elaborated at a
base-Type function type rather than SignGroup. The Iso.refl identity coherence
was not extracted; sign projection and S2332Psub NatIso remain missing.

Available actual: S1971PrecompFunctor_map_val, S2259QMapPrecomp, S2332Psub.

No IsStack claim, no fake.

Verification:
- EXIT=0
- SHA256: 0895f6f2dee31b2f9d864d0ca580e732c4884fdbbedf3ee35f3c183aa806c800
- olean: D:\lean\.lake\build\lib\lean\tmp\sheaf\xif\paper\S2421StrictSign2Actual.olean, size 3568
- axioms: propext, Classical.choice, Quot.sound.