# EXPLORATION-C-C2 — invariant library (Status: NUMERIC)

Status: **NUMERIC**. Not Lean, not a proof, not evidence for ABC. This file records the
Cremona/Sage invariant sample required by EXPLORATION-ROUTES C2 and the C3 preparation.

## 1. Sample and scope

- Canonical data: data/c2_invariants.jsonl (one JSON record per curve).
- Machine-readable summary: coord/c2_invariants_summary.csv.
- Source: Sage 10.9 (WSL Ubuntu-24.04) + Sage CremonaDatabase, which covers conductors
  up to 9999. The run enumerated N = 1..2000.
- N_total (all curves seen, including non-semistable): 11308.
- N_semistable (rows kept): 4154; label range 11a1 .. 1995h6; N in [11,1995].
- Runtime: 100.74 s for the full enumeration + invariants.
- semistable filter: E.is_semistable() over all Cremona curves in the range.
- The 5e5 target is not reachable from this database (cap 9999); no LMFDB access was
  available (LMFDB API returned reCAPTCHA HTML). Recorded, not silently ignored.

## 2. Fields and method

Each record has:
N, label, ainvs, discriminant, semistable, bad_primes, vp_delta, tamagawa,
torsion_order, torsion_invariants, modular_degree, a_p (good p <= 10000), a_p_limit.

Computation:
- discriminant: Sage minimal discriminant of the Cremona model;
- bad_primes / vp_delta: exact factorization of the discriminant;
- Tamagawa: E.tamagawa_number(p) for every bad p;
- torsion: E.torsion_subgroup() order and invariants;
- modular_degree: E.modular_degree() (sympow path resolved in the Sage environment);
- a_p: E.ap(p) for all good primes p <= 10000 (bad-prime p skipped, recorded in the
  bad_primes list);
- semistable: E.is_semistable() (filter).

Unavailable/null fields: none among the requested C2 fields in this run. Fields C2 lists but
which are not in this dataset (analytic Sha order, real period, isogeny class, full torsion
field invariants) were not computed and are not present in the JSONL; they are declared
out of scope for this numeric pass, not silently null.

## 3. Coverage and field completeness

| field | status | count |
|---|---|---|
| rows | complete | 4154 |
| N, label, ainvs, discriminant | 100% | 4154 |
| semistable | 100% | 4154 |
| bad_primes / vp_delta | 100% | 4154 / 12547 bad-prime entries |
| tamagawa | 100% non-null | 4154 |
| torsion_order / torsion_invariants | 100% | 4154 |
| modular_degree (deg phi) | 100% non-null | 4154 |
| a_p for good p <= 10000 | 100% of good primes | 5092719 entries; 1225..1228 per curve |
| a_p bad primes | skipped by definition | listed in bad_primes |

Data size: canonical JSONL 64,336,856 bytes (64.3 MB). Summary CSV is tiny.
No full duplicate CSV is kept in coord/; backups of the previous dumps are in
tmp/c2_backup_20261112-A922* (73.8 MB CSV, 64.3 MB JSONL, old 40-sample files).

## 4. Status, touchstones, external registry

- Status: **NUMERIC** (C2 sample only). This is not a proof of any Szpiro/ABC statement.
- Touchstone declaration: no ABC conclusion is drawn from this dataset; it is an invariant
  library for C3 model fitting. Positive margins on known curves are expected (§C.3 of
  EXPLORATION-ROUTES) and are not evidence.
- External registration:
  - Sage 10.9, WSL Ubuntu-24.04, PATH /opt/miniconda/envs/sage/bin;
  - Sage CremonaDatabase (Cremona elliptic curve database, conductor <= 9999) as the
    source of curves/ainvs; Tamagawa/torsion/modular_degree from Sage methods;
  - no LMFDB/Cremona web API used.
- Reproducer: tools/c2_invariants.sage; output data/c2_invariants.jsonl +
  coord/c2_invariants_summary.csv.
