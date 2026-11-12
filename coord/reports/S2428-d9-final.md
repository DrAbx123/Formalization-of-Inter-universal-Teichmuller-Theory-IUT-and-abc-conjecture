# S2428: D9 integration — conditional Psub NatIso + S2134 descent halves actual; concrete missing

Date: 2026-11-02.

## Integrated actual

- S2427 conditional Psub NatIso: S2427NatIso_of_signProjection : S2427SignProjection -> (Q.presheafHom M N ≅ S2332Psub S M N).
- S2428PsubNatIsoMissing S := forall M N, S2427SignProjection S M N.
- S2428PsubNatIso_of_missing : S2428PsubNatIsoMissing S -> forall M N, Q.presheafHom M N ≅ S2332Psub S M N.
- A subagent S2134D9DescentActual: effective descent base cases (identity cover, maximal sieve, split epi), amalgamation equivalence, exact S2134FirstMissing, and S2093LargeSheafStackMissing_iff_halves. Axioms propext/Classical.choice/Quot.sound, EXIT=0.
- S2428D9Missing S := S2103FirstMissing K ∧ S2134EffDescentOnEtaleFamilies K ∧ S2428PsubNatIsoMissing S.

## Concrete missing

1. S2427SignProjection S M N: naturality/sign projection of the S2271 cast, for every M N. This is the exact remaining Psub NatIso input.
2. S2103FirstMissing K: prestack naturality half.
3. S2134EffDescentOnEtaleFamilies K: effective descent for arbitrary proper etale covers; only base cases (split/identity/maximal) are proved.

No IsStack instance is claimed. B subagent (cast helpers) produced no report file found in coord/reports or the requested S2425 file; treat as not delivered.

## Verification

- EXIT=0
- SHA256: 7334cef49875fe00e3edb90d22ca4e73c8c38bd9886190058528403a01de221d
- olean: D:\lean\.lake\build\lib\lean\tmp\sheaf\xif\paper\S2428D9FinalActual.olean, size 20024
- axioms: propext, Classical.choice, Quot.sound.