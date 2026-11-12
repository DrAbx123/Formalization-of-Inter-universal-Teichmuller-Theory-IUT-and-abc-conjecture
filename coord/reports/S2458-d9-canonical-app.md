# S2458: canonical mapComp' app identity attempt — compile too slow, no conclusion

Date: 2026-11-02. Serialized lake env lean -j1.

Attempt: for canonical h = f ≫ g, prove
  ((S2152PFunctor.toPseudofunctor'.mapComp' f g (f ≫ g) rfl).hom.toNatTrans.app M)
    = 𝟙 ((S2152PFunctor.map (f ≫ g)).toFunctor.obj M)
by rw [S2456_app_eq_eqToIso]; rfl.

Compile exceeded 3+ minutes and was killed; no olean. It is not proven.

ACTUAL retained: S2456_app_eq_eqToIso (EXIT=0, olean 47712, SHA256 d107daed1fc25ca2ead561adf2ccce74f5af502b4786e62ec299ed0a6372d46a) and S2453 base identity (olean 54080).

Remaining exact: prove canonical eqToIso coherence app is identity, then action-on-x, then S2427SignProjection; or directly HEq/app-cast formulation. No IsStack claim, no fake.

S2458 source SHA256: cf8f0a32b32d83774b0bfb071a5bdf5c044487810a00fa010559cd4b6db0cc9d; no olean.