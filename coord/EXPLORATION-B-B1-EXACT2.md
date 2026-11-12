# EXPLORATION-B-B1-EXACT2 — complete constraints (newforms + oldforms) and certificate direction

Status: NUMERIC, 2026-11-12. B line only; no Lean. This supersedes A979's
same-level-only exact SNF run. The constraint set now includes all oldforms, and
the certificate direction r_f^opt | min_abs is validated on every positive row.

## 0. Pre-registration (written before the complete-constraint runs)

For a curve f at level N:

- A rows: every other newform at level N, and every oldform arising from every
  newform h at every proper divisor M | N, M < N. For p not dividing N,
  a_p(oldform h) = a_p(h). This matches the A972 Q_p family's constraint set.
- Columns: constant term plus a_p for primes p <= Pmax, p not dividing N.
  Two versions are run: Pmax = 60 and Pmax = 200.
- Non-rational newforms: sum c_p a_p(g) = 0 is expanded in the coefficient-field
  basis; denominators are cleared, producing several integer rows.
- K = integer kernel matrix A.right_kernel_matrix() over ZZ; b = (1, a_p(f));
  min_abs = gcd { b K_i } = minimal positive value of the linear functional on
  the integer kernel lattice (SNF/maximal-minor invariant). min_abs = 0 means
  no nonzero certificate exists in this window.
- Certificate-direction check: r_f^opt = min over the isogeny class of
  E.modular_degree(); require r_f^opt | min_abs (and hence min_abs >= r_f^opt)
  on every positive row. If this fails, the constraint set is incomplete.
- Pre-registered PASS ("有戏"): C_obs = log(min_abs)/log N has max <= 3 AND
  median/zero rate does not rise with N. Otherwise STOP, recording slopes and
  the failure mode.

## 1. Constraint set and method

Script: tools/b1_exact_snf2.sage. Inputs: N<=500 uses coord/b1_curves_500.json
(941 semistable curves, 198 levels); N<=1000 uses Cremona enumeration (2122
semistable curves). Newforms: CuspForms(Gamma0(N),2).newforms(names='a').
Oldforms: for every proper divisor M of N, every newform at level M is included
with its a_p for p not dividing N. No oldform is duplicated beyond this
one-row-per-(M,newform) convention.

Outputs:
- coord/b1_exact2_500_p60.csv, coord/b1_exact2_500_p200.csv (941 rows each)
- coord/b1_exact2_1000_p60.csv, coord/b1_exact2_1000_p200.csv (2122 rows each)
- coord/b1_exact2_summary.csv, coord/b1_exact2_bins.csv
Fields: N, label, r_f_opt, nforms, n_same_other, n_oldforms, ncols, rank,
min_abs, valid_div, valid_ge, kernel_zero.

Validation (all datasets):
- every positive row has r_f^opt | min_abs: 100% (no violation);
- every positive row has min_abs >= r_f^opt: 100%;
- no missing-form failure was found among positive rows. Zeros are rows where no
  nonzero certificate exists in the chosen Pmax window; they are not direction
  violations.

## 2. NUMERIC, N <= 500 (941 curves)

Pmax = 60:
- positive: 348/941; zero: 593/941 (63.0%);
- valid_div = 348/348 (100%); valid_ge = 348/348;
- C_obs (positive): max 2.309019, median 0.492568, mean 0.581738;
- log(min_abs) vs log N slope (positive): 2.218616;
- bins: 0-100 (146 rows, 0 zero, max 1.0058, med 0.2561),
  100-200 (191, 11 zero, max 1.8193, med 0.6275),
  200-300 (203, 181 zero, 22 positive, max 2.3090, med 1.7722),
  300-400 (198, all zero), 400-500 (203, all zero).

Pmax = 200:
- positive: 941/941; zero: 0;
- valid_div = 941/941 (100%); valid_ge = 941/941;
- C_obs: max 1.520991, median 0.644886, mean 0.631952;
- slope: 1.424032;
- min_abs/r_f^opt: min 1, median 1, max 4; equal to r_f^opt in 761/941;
- bins (rows, zero, positive, max C_obs, median C_obs, mean C_obs):
  0-100: 146,0,146,1.005811,0.256059,0.280819
  100-200: 191,0,191,1.422651,0.580675,0.615152
  200-300: 203,0,203,1.446991,0.682766,0.687054
  300-400: 198,0,198,1.330248,0.705735,0.724876
  400-500: 203,0,203,1.520991,0.705280,0.754561

At N<=500 Pmax=200 the max C_obs is 1.521 <= 3 and there are no zeros, but the
median still rises from 0.256 to 0.706 (then flattens). Strictly, the
pre-registered "median does not rise" clause is not satisfied across all bins;
the high bins 300-500 are flat at about 0.705.

## 3. NUMERIC, N <= 1000 (2122 curves)

Pmax = 60:
- positive: 348/2122; zero: 1774 (83.6%);
- valid_div = 348/348 (100%); valid_ge = 348/348;
- C_obs: max 2.309019, median 0.492568, mean 0.581738;
- slope: 2.218616;
- all positive rows are at N < 300; every bin 300-400 and above is all zero.
- bins: same as N<=500 for 0-500; 500-1000 all zero (213,208,265,235,260 rows).

Pmax = 200:
- positive: 1019/2122; zero: 1103 (52.0%);
- valid_div = 1019/1019 (100%); valid_ge = 1019/1019;
- C_obs: max 7.741035, median 0.659568, mean 0.735677;
- slope: 2.186431;
- min_abs/r_f^opt: median 1, equal 777/1019; max ratio dominated by N=571a1
  (min_abs 2.1838e21, r_f^opt 120), a genuine large-gcd positive row;
- bins (rows, zero, positive, max C_obs, median C_obs, mean C_obs):
  0-100: 146,0,146,1.005811,0.256059,0.280819
  100-200: 191,0,191,1.422651,0.580675,0.615152
  200-300: 203,0,203,1.446991,0.682766,0.687054
  300-400: 198,0,198,1.330248,0.705735,0.724876
  400-500: 203,0,203,1.520991,0.705280,0.754561
  500-600: 213,135,78,7.741035,0.953017,1.987022
  600-700: 208,208,0
  700-800: 265,265,0
  800-900: 235,235,0
  900-1000: 260,260,0

The N<=500 Pmax=200 plateau does not survive the extension: at N>500 the zero
rate jumps to 63.4% in 500-600 and 100% for N>=600, and the positive C_obs max
rises to 7.741 (571a1). Even ignoring the single outlier, the median rises from
0.705 to 0.953 in 500-600.

## 4. Judgment

- Complete constraints fix the certificate direction: for every positive row in
  all four datasets, r_f^opt | min_abs and min_abs >= r_f^opt (100%, no missing
  form found); this validates the A matrix for the found certificates. The
  earlier A979 min_abs < r_f artifacts are gone because oldforms are now included.
- Pre-registered criterion:
  - Pmax=60: C_obs max 2.309 <= 3 (passes the max bound), but zero rate rises to
    63% at N<=500 and 100% by N>=300; median rises -> FAIL on stability.
  - Pmax=200: N<=500 looks bounded (max 1.521, zero 0) but the N<=1000 extension
    has max 7.741, zero rate 52% overall, 63% at 500-600, 100% for N>=600;
    median rises -> FAIL on stability and max.
- Verdict: **STOP / no "有戏" signal** under the pre-registered criterion. The
  correct statement is: with complete newform+oldform constraints, the exact
  minimal |P(f)| is certificate-direction-valid, but it is not a bounded
  C_obs family; in the Pmax=200 window the size grows and nonzero certificates
  disappear above N~500. The zeros are a Pmax/window effect, not a proof of
  nonexistence. No B2 support.

## Files

- coord/b1_exact2_500_p60.csv, coord/b1_exact2_500_p200.csv
- coord/b1_exact2_1000_p60.csv, coord/b1_exact2_1000_p200.csv
- coord/b1_exact2_summary.csv, coord/b1_exact2_bins.csv
- tools/b1_exact_snf2.sage, tools/b1_exact2_analyze.py
- Prior context: coord/EXPLORATION-B-B1-EXACT.md (A979 incomplete constraints)
