# EXPLORATION-C-C3 — margin search on 4154 semistable curves (Status: NUMERIC)

Status: **NUMERIC**. This is a data-fitting/search pass, not a proof and not evidence for
ABC. The C1 margin still lacks C0 (archDefect, Ind2) and concrete Theta-data; the quantity
searched here is the model proxy M0. Touchstone: no ABC conclusion follows; positive margins
on known curves are expected (EXPLORATION-ROUTES §C.3).

## 1. Data and proxy

- Data: data/c2_invariants.jsonl (4154 semistable curves, N<=2000, C2).
- Proxy:
      M0(D) = log(deg phi) - (sF-1)*log(N)/(2*l),   l=5, sF-1=1.5
            = log(deg phi) - 0.15 log N.
  This is the chain2 model coefficient for the q-side requirement, with logQ replaced by
  logN; it is NOT the exact C1 margin V+gap-(sF-1)A.
- Features: logN, log|Delta|, log(deg phi), number of bad primes b, max v_p(Delta).

## 2. Regressions

Full-sample ordinary least squares
    M0 ~ 1 + logN + log|Delta| + b + maxvp:
  coefficients [-3.7257, 0.78269, 0.15583, 0.18262, 0.00175],
  R^2 = 0.8781, residual range [-1.1656, +6.6264].
Holdout (80/20, seed 20261112):
  test R^2 = 0.8931, test residual range [-1.0807, +4.0761].
The coefficient of log|Delta| is 0.1558 ~ 1/6; this is exactly the known-equivalence
direction (see §3), so the fit itself is not a new relation.

M0 distribution: min -0.45668, max 13.22261, mean 4.88377; quantiles (0,1%,50%,99%,100%)
= (-0.45668, 0.64089, 4.75550, 10.07463, 13.22261).

## 3. Pre-removal of known equivalences

Known inputs:
    h ~ (1/2) log(deg phi) - (1/2) log N,
    12 h ~ log|Delta|.
Eliminating h gives
    log(deg phi) ~ log N + log|Delta|/6,
hence
    M0_known = 0.85 log N + log|Delta|/6.
A relation that follows from M0_known is marked KNOWN-EQUIVALENT and not a discovery.
On the sample, M0 - M0_known has range [-5.0550, +2.8875], mean -3.8065. This mismatch is
expected because the proxy omits V, gap, arch and Ind2; it means the known-equivalence line
is not the exact C1 margin either.

## 4. Segmented lower envelopes and candidates

By number of bad primes b, empirical min M0:
  b=1 (129 rows): -0.4417; b=2 (932): -0.4567; b=3 (1818): +0.1830;
  b=4 (1275): +1.9705.
This is a clean empirical staircase, but its lower envelope is fitted to the sample; no
known upper bound X(b) is available, and it is not implied by the known equivalence above
(the known line's residual min is -5.055, much lower). It therefore does **not** qualify as
a C3 candidate under the rule "X has a known upper bound or can be proved independently".

By max v_p(Delta), the empirical min M0 is also positive for most strata except maxvp=1,3,4
(the minima are -0.0381, -0.4417, -0.4567 respectively); again sample-fitted.

The only global zero-violation candidate is the empirical constant
    M0(D) >= -0.4567,
sharp at 21a1. It has no independently known X (a constant fitted to the sample is not an
upper bound), so it is recorded as NUMERIC observation, not a conjecture with proof route.

## 5. Verdict

- Linear/log-linear fit: R^2 0.878 (test 0.893); no residual zero-violation relation with
  a known bound.
- Known-equivalence direction log|Delta|/6 is recovered by the fit (coefficient 0.1558);
  relations along it are marked KNOWN-EQUIVALENT.
- After removal, the only zero-violation statements are empirical thresholds such as
  M0 >= -0.4567 and the bad-count staircase; none has an independent upper bound X.
- Therefore, under EXPLORATION-ROUTES C3/C4, this first pass **stops**: no new candidate
  relation survives the known-equivalence filter with a provable X. The staircase is the
  only pattern worth re-testing once the true C1 margin (with C0/Ind2 and Theta-data) is
  available.

Data: coord/c3_search_results.json (raw fit/segment output).
