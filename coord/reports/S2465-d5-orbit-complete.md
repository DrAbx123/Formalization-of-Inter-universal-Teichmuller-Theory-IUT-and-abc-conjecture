# S2465: D5 orbitSize and S2217Missing ACTUAL

Date: 2026-11-03. Serial -j1.

## Actual

tmp/sheaf/xif/paper/S2465D5OrbitSizeActual.lean
  SHA256 98A0D00DCA25D90418D9F60D0C8B1AC713D21F495035B5050174DFC492DF3A90
  EXIT=0
  olean SHA256 9C5C3BEE743D064C091F49E69FEBA639E0FE2EFCBB97223AE022D042AC8C5CAF
  size 227928
  axioms propext, Classical.choice, Quot.sound; no sorryAx.

Theorems:
- s2465_filter_ne_one_add_replicate_count_one:
    M.filter (· != 1) + replicate (M.count 1) 1 = M;
- s2465_factorDegrees_sum:
    (factorDegrees (fbar f p)).sum = f.natDegree;
- s2465_orbitSizeMultiset_rootPerm_eq_factorDegrees:
    orbitSizeMultiset (rootPerm K L f hsplit sigma) = factorDegrees (fbar f p);
- s2465OrbitSizeStatement:
    DedekindFrobeniusOrbitSizeStatement f p P hmonic hsep hsplit;
- s2465DedekindFrobeniusOrbitSizeTheorem:
    DedekindFrobeniusOrbitSizeTheorem;
- s2465S2217Missing: S2217Missing.

Proof chain: S2464 corrected theorem (S2460 rootCycleType + S2463 action transport)
+ Equiv.Perm.card_fixedPoints + multiset filter/count arithmetic +
card roots via s2440RootSetEquiv/card_rootSet_eq + factor degree sum via
natDegree_multiset_prod_of_monic/prod_normalizedFactors.

## Status

D5 closed actual: corrected cycle type and orbit-size/S2217Missing.
Allowed axioms only; no fake; S2427 sorryAx unused.
