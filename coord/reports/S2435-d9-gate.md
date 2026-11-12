# S2435: D9 compile gate report

Date: 2026-11-02.

Gate results:

1. S2425NatIsoCastHelpersActual.lean: EXIT=0, olean 530872, axioms propext/Classical.choice/Quot.sound. ACCEPTED. It provides natIsoOfPointwiseEqToIso and eqToIso/subtype cast helpers.
2. S2434D9AttackActual.lean: EXIT=0, olean 2641, axioms propext/Classical.choice/Quot.sound. ACCEPTED. It provides S2434SlicePush_iff_pullHom (actual equivalence of SlicePushNaturality and the explicit pullHom coherence) and the three-input D9 decomposition.
3. S2432PrestackCloseActual.lean: EXIT=0 but contains a literal sorry (declaration uses sorry). REJECTED as a proof; test_slicePushNaturality is not actual.
4. S2134D9DescentActual.lean: EXIT=0, olean 476224, axioms propext/Classical.choice/Quot.sound. ACCEPTED for base cases/equivalence; S2134FirstMissing has no inhabitant.

S2435D9GateActual.lean gate-check file: EXIT=0, SHA256 43be62bb94890e1abb99bc014fc63a58e6f0da1feff1fcebcb2a30a22a44a244, olean 2584.

D9 remains open: S2428D9Missing has no inhabitant. Three missing:
- SlicePushNaturality (S2103FirstMissing), now reduced to explicit pullHom coherence by S2434; proof still missing.
- S2134EffDescentOnEtaleFamilies: general amalgamation missing.
- S2427SignProjection Psub NatIso naturality.

No S2152QIsStack claim. No fake.