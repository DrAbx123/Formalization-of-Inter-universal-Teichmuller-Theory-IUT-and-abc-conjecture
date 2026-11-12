# EXPLORATION-C-C3b — real paper-MODEL C1 margin on 4154 curves (Status: NUMERIC)

Status: **NUMERIC**. This is a data check, not a theorem and not ABC evidence.
Touchstone: deferred (no ABC conclusion). The C1 margin is paper-MODEL (hull's
c1_margin_v2.csv), not a proof; arch/Ind2 are MODEL-PAPER per hull, C0 still partial.

## 1. Data and margin

- Input: coord/c1_margin_v2.csv (4154 rows, one per C2 semistable curve), joined to
  data/c2_invariants.jsonl for bad-prime/max-vp features.
- Columns: N, label, nbad, M, admissible.
- Formula (hull, MODEL-PAPER):
      H = arch_mean + (p=2: 0.5 log2) + (p=3: (2/3)log3) + odd bad e=1 term 0;
      arch_mean = (1/nC) sum_i arch_defect(i+2), arch_defect(N)=log((2^(N-1))!)/2^N;
      T = (sF-1) v_p(Delta) log p / (2l), l=5,nC=2,sF=2.5;
      Ind2 = sum_j frac(j^2 v_p(Delta)/(2l)) log p;
      M = H + Ind2 - T.
- M range: min -5.570216, max 5.592119, mean 2.767960.
- admissible: 2604/4154; M<0: 74 rows (4 of them admissible).

## 2. Strata by bad-prime count b

All 4154 rows:

| b | rows | min M | mean M | max M | M<0 |
|---:|---:|---:|---:|---:|---:|
| 1 | 129 | -0.3142 | 2.5226 | 5.5748 | 1 |
| 2 | 932 | -3.6019 | 2.6361 | 5.5921 | 16 |
| 3 | 1818 | -4.6367 | 2.7978 | 5.5505 | 35 |
| 4 | 1275 | -5.5702 | 2.8466 | 5.4215 | 22 |

Admissible rows only (2604):

| b | rows | min M | mean M | M<0 |
|---:|---:|---:|---:|---:|
| 1 | 128 | +0.4318 | 2.5451 | 0 |
| 2 | 755 | +0.5106 | 2.8430 | 0 |
| 3 | 1212 | -0.5401 | 3.1877 | 2 |
| 4 | 509 | -4.5936 | 3.3563 | 2 |

The old proxy staircase was (b=1 -0.44, b=2 -0.46, b=3 +0.18, b=4 +1.97).
Under the real paper-MODEL margin it does **not** persist: min M decreases with b (all
rows), and even on admissible rows b=3/4 have negative minima (-0.540, -4.594). The
staircase is inverted/absent.

By max v_p(Delta), the negative tail is concentrated at maxvp=20 (min -5.5702),
maxvp=10/15/12/11 (mins -4.637, -2.952, -1.732, -2.535); maxvp=1..4 strata are all
nonnegative (min >= 0.3826). This is an empirical diagnostic, not a theorem.

## 3. Tight samples and zero-violation candidates

Overall min M: 1870h2 (nbad=4, maxvp=20) M=-5.570216, admissible=False.
Min among admissible: 858k2 (nbad=4) M=-4.593599; other admissible negatives:
714g4 (-0.368396), 777b1 (-0.540068), 1634c1 (-0.121419).
All other 70 negative rows are non-admissible.

The only global zero-violation candidate is the empirical bound
    M >= -5.5702,
which is just the sample minimum and has no known upper bound X (and includes a
non-admissible sample). It does not qualify as a C3 candidate.

Known-equivalence check:
- OLS M ~ 1 + logN + log|Delta| + b + maxvp gives R^2=0.2045, residual [-7.0841,+3.0189];
  the fit is weak, so M is not explained by the h/degphi/logDelta direction alone.
- The known-equivalence line M_known=0.85 logN + log|Delta|/6 has residual range
  [-21.0539,-1.0134], mean -5.9223; relations along it are marked KNOWN-EQUIVALENT and
  do not count as discoveries.
- After removing the known-equivalence direction, no zero-violation relation with a
  known X remains: the negative tail is a property of the MODEL formula itself
  (especially maxvp=20/10 rows), not a new invariant relation.

## 4. Verdict

- The old proxy bad-prime staircase does **not** survive the real C1 margin. In the
  admissible subset the minima are (+0.432, +0.511, -0.540, -4.594) for b=1..4; the
  all-row minima are (-0.314, -3.602, -4.637, -5.570).
- 74/4154 MODEL margins are negative; only 4 are admissible; the global minimum
  (-5.5702) is non-admissible, and the admissible minimum is -4.5936 (858k2).
- No qualified zero-violation relation after the known-equivalence filter; the only
  bound is the sample-fitted constant -5.5702 with no known upper bound.
- Verdict: **STOP / no signal** in this C3b pass. The negative strata are a diagnostic
  of the MODEL formula (and of maxvp=10/20 rows), not an ABC theorem. Next only if the
  C0/Ind2 exact (non-MODEL) margin changes the negative tail.

Data: coord/c1_margin_v2.csv; analysis script tools/c3b_analyze.py.
