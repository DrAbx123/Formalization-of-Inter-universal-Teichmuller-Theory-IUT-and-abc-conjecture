# EXPLORATION-C-C3-PREP — first pass on C2 data (Status: NUMERIC / MODEL)

Status: **NUMERIC / MODEL**. Not Lean; not a proof of ABC. The C1 margin formula needs
C0 (archDefect, Ind2 term) and concrete D/Theta-data, which are still pending. This note
therefore computes only a clearly-labelled model proxy and the raw invariant distribution;
it does not claim a zero-violation relation.

## 1. Data and model margin

Input: data/c2_invariants.jsonl (4154 semistable curves N <= 2000, C2).
Proxy used (MODEL, not C1):
    M0(D) = log(deg phi) - (sF-1) * log(N) / (2*l),   l=5, sF-1=1.5,
i.e. M0 = log(deg phi) - 0.15 log N.
This drops V, gap, arch and Ind2; it is only a scale test for C3 feature engineering.
The real C1 margin is M(D)=V+gap-(sF-1)A and remains pending C0.

## 2. Raw first-pass distribution

- rows: 4154; N in [11,1995]; deg phi in [1,1720320].
- Szpiro ratio log|Delta|/log N: min 1.0, max 8.9037, mean 2.7392.
- log(deg phi)/log N: min 0.0, max 1.9381, mean 0.8710.
- bad-prime count per curve: max 4; max v_p(Delta) = 63.
- M0: min -0.4567, max 13.2226, mean 4.8838; M0 >= 0 for 4147/4154 rows.

## 3. First patterns / zero-violation candidates

The only negative M0 rows are 7 curves:
11a1 (-0.3597), 14a1 (-0.3959), 15a1 (-0.4062), 17a1 (-0.4250), 19a1 (-0.4417),
21a1 (-0.4567), 131a1 (-0.0381).
Thus on this proxy sample the zero-violation inequality
    M0(D) >= -0.46
holds for all 4154 rows (sharp at 21a1). Other candidate relations to test in the real C1
margin (not yet computed):
- log(deg phi) <= 1.94 log N + C (observed max ratio 1.9381);
- log|Delta| <= 8.91 log N (observed max Szpiro ratio 8.9037);
- M0 grows roughly linearly with log N on this sample (mean log(deg)/logN=0.871).

These are **candidate patterns**, not discovered theorems: the thresholds are fitted to the
sample and no independent upper bound is known. Per EXPLORATION-ROUTES C.3, positive margins
are expected and "no counterexample" is not evidence.

## 4. Next steps

1. Implement the true C1 V/H_v/Ind2 terms with C0 results; replace M0 by M(D).
2. Restrict to admissible l and V_bad choices, enforce l ∤ ord_v(q), Galois image contains
   SL2(F_l), odd bad places.
3. Fit only linear/log-linear/segmented models; pre-remove relations implied by
   h ~ 0.5 log(deg phi) - 0.5 log N and 12h ~ log|Delta|.
4. Treat any counterexample as a result, not as a parameter to tune away.
