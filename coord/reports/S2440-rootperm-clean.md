# S2440: clean rootPerm/permBar cycle-type transport

Date: 2026-11-03.

## Actual

Lean:

  tmp/sheaf/xif/paper/S2440RootPermCycleCleanActual.lean
  SHA256 88E6A0C79E2CD7FFADEAB936C157DC7CC6F887261986A3FABD95EDC2D00F53CC
  EXIT=0
  olean SHA256 34F87BFF37C5586CDA751107C7D6F70B544D6DF312A3AEBF1B074643A2F330B9
  size 269680
  axioms propext, Classical.choice, Quot.sound.

Theorems:

- s2440_cycleType_permCongr (generic cycle-type invariance);
- s2440RootSetEquiv: S2345 equivalence retyped so codomain is
  (f.map (algebraMap O_K K)).rootSet L, eliminating the rootPerm cast;
- s2440RootPermBar: permBar transported along redRootEquiv;
- s2440RootPermBar_cycleType;
- s2440RootPermBar_agrees_rootPerm;
- s2440RootPermBar_eq_permCongr_rootPerm;
- s2440RootPermBar_cycleType_rootCycleType;
- s2440_permBar_cycleType_eq_rootCycleType.

All with axioms trio only, no sorryAx.  S2427 remains broken and unused.

## Next

Final S2217 integration is delegated (S2445D5FinalActual.lean): apply
cycleType_eq_fiber_sizes to permBar and the root-to-factor map, use S2428
filter bridge, then S2440 for rootCycleType.  Exact missing, if any, will be
reported there.

## Conclusion

- BUILT: clean rootPerm/permBar cycle-type alignment.
- S2427 with sorryAx is not used.
- no fake.
