# EXPLORATION-RESULTS-C — route C summary (Status: MIXED / STOP-NO-SIGNAL)

Status: **MIXED**. C2 is NUMERIC data (complete C2 pass); C0/C1 are PARTIAL; C3 and C3b
reached STOP. This document is a results summary, not a proof and not evidence for ABC.
It is intended to be written back into EXPLORATION-ROUTES.md as the route-C outcome.

## 1. Stage verdicts

| stage | verdict | pointer |
|---|---|---|
| C0 Ind2/archDefect | **PARTIAL** (formulas conditional; exact identification not closed) | coord/EXPLORATION-C-C0.md; Lean: Mzk1C0Ind2ArchActual |
| C1 local calculator | **PARTIAL / MODEL** (paper-MODEL margin; arch/Ind2 MODEL-PAPER) | coord/EXPLORATION-C-C1.md; tools/c1_calculator.py, tools/c1_batch.py; coord/c1_margin_v2.csv |
| C2 invariant library | **NUMERIC COMPLETE** (4154 semistable, N<=2000) | coord/EXPLORATION-C-C2.md; data/c2_invariants.jsonl; tools/c2_invariants.sage |
| C3 proxy search | **STOP** (no qualified candidate) | coord/EXPLORATION-C-C3.md; coord/c3_search_results.json; tools/c3_search.py |
| C3b real-margin strata | **STOP / no signal** (old staircase does not survive) | coord/EXPLORATION-C-C3b.md; tools/c3b_analyze.py; coord/c1_margin_v2.csv |
| A3 support (adjacent numeric) | **NUMERIC** (Belyi/Legendre/triples) | coord/A3-SUPPORT.md; coord/a3_support.csv; tools/a3_support.py |

Overall route-C verdict: **stop / no signal**. No ABC/Szpiro theorem, no new invariant
relation, and no candidate that passes the known-equivalence filter with a provable bound.

## 2. Stage conclusions and file pointers

### C0 — local formulas
- ind2Term is read from Iut/WallEquiv/Gap.lean (:747-754), with ind2Term_nonneg and
  gapHullAt (:895); archDefect is read at :459-463 and the exact value
  log((2^(N-1))!)/2^N is stated at :66 but not formalized.
- T2 (archDefect formula) is conditional on the tensor-metric orthogonality gap; C0 is
  therefore PARTIAL, not a green exact calculator.
- Pointer: coord/EXPLORATION-C-C0.md.

### C1 — local calculator
- Paper-MODEL formula used by hull:
    H = arch_mean + (p=2: 0.5log2) + (p=3: (2/3)log3) + odd bad e=1 term 0;
    arch_mean = (1/nC) sum_i arch_defect(i+2), arch_defect(N)=log((2^(N-1))!)/2^N;
    T = (sF-1) v_p(Delta) log p / (2l), l=5, nC=2, sF=2.5;
    Ind2 = sum_j frac(j^2 v_p(Delta)/(2l)) log p;
    M = H + Ind2 - T.
- Output: coord/c1_margin_v2.csv, 4154 rows; fields N,label,nbad,M,admissible.
- C1 is PARTIAL/MODEL because arch/Ind2 are MODEL-PAPER; it is not the exact C1 object.
- Pointer: coord/EXPLORATION-C-C1.md.

### C2 — invariant library
- 4154 semistable curves enumerated from the Sage Cremona database N<=2000
  (N_total=11308); canonical data data/c2_invariants.jsonl (64.3 MB), summary
  coord/c2_invariants_summary.csv.
- Fields: N, label, ainvs, discriminant, semistable, bad_primes, vp_delta, tamagawa,
  torsion_order, torsion_invariants, modular_degree (deg phi), a_p for good p<=10000.
  Tamagawa/torsion/deg phi are 100% non-null; a_p total 5,092,719 entries.
- Database cap is 9999, so 5e5 is not reachable with this source; LMFDB API was blocked by
  reCAPTCHA and is recorded, not used.
- Pointer: coord/EXPLORATION-C-C2.md.

### C3 — proxy search
- Proxy M0 = log(deg phi) - 0.15 log N on 4154 curves.
- OLS M0 ~ 1+logN+log|Delta|+b+maxvp: R^2=0.8781, holdout 0.8931; the log|Delta|
  coefficient 0.1558 ~ 1/6 is the known-equivalence direction.
- Known equivalence: h ~ 0.5log(deg phi)-0.5logN and 12h ~ log|Delta| imply
  log(deg phi) ~ logN+log|Delta|/6; relations along this line are marked KNOWN-EQUIVALENT.
- After removal, only empirical thresholds survive (M0 >= -0.4567, bad-count staircase);
  none has an independent bound X. Stop.
- Pointer: coord/EXPLORATION-C-C3.md.

### C3b — real paper-MODEL margin
- M range: min -5.570216, max 5.592119, mean 2.767960; admissible 2604/4154;
  M<0: 74 rows, of which only 4 are admissible.
- The old proxy staircase was (b=1 -0.44, b=2 -0.46, b=3 +0.18, b=4 +1.97). It does
  not survive: all-row minima are (-0.3142, -3.6019, -4.6367, -5.5702); admissible minima
  are (+0.4318, +0.5106, -0.5401, -4.5936) for b=1..4.
- Tightest: overall 1870h2 M=-5.570216 (non-admissible); admissible 858k2 M=-4.593599;
  other admissible negatives 714g4 (-0.3684), 777b1 (-0.5401), 1634c1 (-0.1214).
- OLS M ~ features R^2=0.2045, residual [-7.0841,+3.0189]; known-equivalence line residual
  [-21.0539,-1.0134]. No zero-violation relation with known X survives.
- Pointer: coord/EXPLORATION-C-C3b.md.

## 3. Key negative results

1. **Bad-prime staircase does not survive the real margin.** The proxy M0 showed a clean
   increasing lower envelope in b; the paper-MODEL M has a decreasing minimum in b
   (-0.314, -3.602, -4.637, -5.570 for all rows). The admissible subset is even clearer:
   b=3/4 have negative minima (-0.540/-4.594). The staircase was a proxy artifact.
2. **Negative tail is a MODEL/maxvp effect.** 74 negative rows; 70 are non-admissible and
   the tail concentrates at max v_p(Delta)=20 (min -5.5702), 10/15/12/11
   (mins -4.637/-2.952/-1.732/-2.535). maxvp=1..4 strata are nonnegative. This is a
   diagnostic of the MODEL formula (arch_mean/Ind2/T), not an ABC signal.
3. **Admissibility rules conflict with the Frey family.** A3 support: all 80 triples
   (60 family (1,3^k-1,3^k) + 20 high-quality) contain the bad prime 2, so "all bad primes
   odd" gives 0/80 admissible; p-adic admissibility (all |a/c|_p < 1) is also 0/80 because
   denominator primes have |a/c|_p > 1, with max 4.2391e28 at k=60. The naive admissibility
   rules are therefore incompatible with Frey curves; the A3 normalization must be
   supplied before these checks are meaningful.
4. **No qualified C3 candidate.** After known-equivalence removal, the only bounds are
   sample minima (M0 >= -0.4567, M >= -5.5702) with no known upper bound X; these are not
   accepted as conjectures.

## 4. C0 dependency and next steps

Conclusions depending on C0/lana:
- The C1 margin is MODEL-PAPER, not exact: arch_mean uses the conditional archDefect
  formula and Ind2 uses the tentative ind2Term. The negative tail may change when C0 is
  closed. Until then, C3/C3b are STOP for the MODEL, not for the exact paper object.
- Needed C0/lana inputs: ind2Term/gapHullAt/gap_eq from Iut/WallEquiv/Gap.lean; the exact
  archDefect log((2^(N-1))!)/2^N and the tensor-metric orthogonality lemma.
- C2 data does not depend on C0 and is final for the stated coverage (N<=2000; Cremona cap
  9999; no LMFDB).

Next steps (if route C is reopened):
1. Close C0 (exact ind2Term/archDefect) and rebuild C1 with the exact margin.
2. Re-run C3b on the exact M; test whether the negative tail at maxvp=20/10 persists.
3. Extend C2 only with a database that covers N>9999 (LMFDB/other), and record the source.
4. Redefine A3 admissibility (Frey-compatible), then re-run the A3 checks; do not cite the
   current 0/80 odd-admissibility as a theorem.
5. Keep the negative results (staircase failure, maxvp tail) as diagnostics, not as ABC
   evidence; do not tune parameters to remove them.

No Lean theorem, no ABC conclusion, and no new accepted conjecture is claimed.
