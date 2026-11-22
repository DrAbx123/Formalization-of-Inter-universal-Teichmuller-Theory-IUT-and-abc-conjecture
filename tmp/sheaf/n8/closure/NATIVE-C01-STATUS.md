# Native C0/C1 slice + C7 Haar correction status

- NativeInput.lean: new C0 input root `N8NativeInput` = `SourceNativeInitialThetaData` + `NativeLattice` over `NativePlaces`; place bijection from `V_mod_bijection.symm`; compiles exit0.
- NativeC1.lean: place bijection/comap and selected-place membership; compiles exit0.
- SourceHolomorphicHull.lean: removed `logVolume_pos` on ENNReal IQ interface; replaced with Haar mass fields `haar_pos`/`haar_lt_top`; compiles exit0 (one named sorry).
- C7Actual.lean: obligations/equivalence updated to Haar mass; compiles exit0.
- Not done: C1 local completion/valued objects; C3/T11 root system in algebraic closure; C7 actual U/H construction; C9 actual Values/Q/Theta; C10 native assembly. No N8 closure claimed.