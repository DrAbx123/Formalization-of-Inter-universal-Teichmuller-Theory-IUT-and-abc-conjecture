# EXPLORATION-B-B1-EXACT — exact integer-kernel minimisation (SNF/gcd)

Status: NUMERIC, 2026-11-12. B line only; no Lean. This tests the exact
minimum of |P(f)| over integer Hecke combinations annihilating all other
same-level newforms, replacing the restricted Q_p search of B1-FIX.

## 0. Pre-registration (written before the exact run)

Let A be the integer annihilation matrix: rows are other newforms g at the same
level, columns are the constant term and a_p(g) for primes p <= 60, p not
dividing N. Let L = { c in Z^cols : A c = 0 } be the integer kernel, and let
b = (1, a_p(f)) be the target row. The exact minimum positive value is

  min_abs = min { |b c| : c in L, b c != 0 } = gcd { b c : c in L },

i.e. the gcd of the linear functional on the integer kernel lattice (equivalently
the maximal-minor/SNF invariant of the stacked system). If all b c = 0, no
nonzero certificate exists in this window and min_abs = 0.

Pre-registered criterion (same thresholds as B1-FIX2, C0 = 3):
- PASS ("有戏") only if C_obs = log(min_abs)/log N has max <= 3 AND its
  median does not rise with N (bin medians stable), with no systematic
  disappearance of nonzero certificates at high N.
- Otherwise STOP / record the true growth rate, slope, Cmax and Cmedian.

## 1. Method

Script tools/b1_exact_snf.sage for N<=500 (data coord/b1_curves_500.json, 941
curves, 198 levels); tools/b1_exact_snf_1000.sage for N<=1000 (Cremona
enumeration, semistable curves).

- Newforms: CuspForms(Gamma0(N),2).newforms(names='a'); f is matched to the
  rational newform of the curve by a_p for p <= 60, p not | N.
- A rows: all other same-level newforms (oldforms are NOT included here; this is
  a narrower annihilation set than B1's oldform-inclusive Q_p search).
- Non-rational newforms: the equation sum c_p a_p(g) = 0 is expanded in the
  coefficient-field basis, denominators cleared, giving several integer rows.
- K = A.right_kernel_matrix() over ZZ; values b.K.row(i); min_abs = gcd of these
  integers (gcd is independent of the integer kernel basis).
- Outputs: coord/b1_exact_snf_500.csv (941 rows), coord/b1_exact_snf_1000.csv
  (2122 rows), coord/b1_exact_snf_bins.csv (bin summary).
- No target r_f is imposed: this is the true minimum |P(f)|, not a search for a
  certificate hitting r_f. Constant certificate P = 1 is allowed and gives
  min_abs = 1 when there are no other forms.

## 2. NUMERIC, N <= 500 (941 curves)

- min_abs = 0: 153 (16.3%), min_abs = 1: 62 (6.6%), min_abs > 1: 726 (77.2%);
- min_abs range: 0 .. 13,057,880;
- positive C_obs (788 rows): max = 2.888061, median = 0.360104, mean = 0.497250;
- slope of log(min_abs) vs log N (positive rows): 1.724139;
- slope restricted to min_abs > 1: 2.072975;
- comparison with B1 Q_p certificates (108 rows with Q_p found and positive
  exact min): exact < Q_p 84, exact = Q_p 24, exact > Q_p 0. Thus exact SNF
  strictly improves the restricted Q_p family wherever both exist.
- exact min = r_f: 94/941; exact min divides r_f: 674/941; min/r_f median =
  0.211111 (the exact minimum is usually much smaller than r_f).

Bin table (100-wide, C_obs = log(min_abs)/log N; zero = no nonzero certificate):

| N range | rows | zero | positive | max C_obs | median C_obs | mean C_obs | max min_abs |
|---|---|---|---|---|---|---|---|
| 0-100 | 146 | 0 | 146 | 0.689656 | 0.161639 | 0.140133 | 20 |
| 100-200 | 191 | 0 | 191 | 0.797217 | 0.299741 | 0.351211 | 60 |
| 200-300 | 203 | 12 | 191 | 2.888061 | 0.451364 | 0.563813 | 13,057,880 |
| 300-400 | 198 | 50 | 148 | 2.356111 | 0.362489 | 0.632654 | 953,640 |
| 400-500 | 203 | 91 | 112 | 2.571915 | 0.572429 | 0.919385 | 6,072,960 |

Criterion at N<=500: max C_obs = 2.888 <= C0 = 3 (passes the max bound), but the
median rises from 0.162 to 0.572 and the zero count rises from 0 to 91. The
stability clause fails.

## 3. Extension, N <= 1000 (2122 rows)

- zero: 1206 (56.8%); min_abs = 1: 62; min_abs > 1: 854; positive rows: 916;
- min_abs range: 0 .. 13,057,880;
- positive C_obs: max = 2.888061, median = 0.388891, mean = 0.504092;
- slope of log(min_abs) vs log N (positive rows): 1.481400;
- exact min = r_f: 100/2122; exact min divides r_f: 790/2122.

| N range | rows | zero | positive | max C_obs | median C_obs | mean C_obs |
|---|---|---|---|---|---|---|
| 0-100 | 146 | 0 | 146 | 0.689656 | 0.161639 | 0.140133 |
| 100-200 | 191 | 0 | 191 | 0.797217 | 0.299741 | 0.351211 |
| 200-300 | 203 | 12 | 191 | 2.888061 | 0.451364 | 0.563813 |
| 300-400 | 198 | 50 | 148 | 2.356111 | 0.362489 | 0.632654 |
| 400-500 | 203 | 91 | 112 | 2.571915 | 0.572429 | 0.919385 |
| 500-600 | 213 | 117 | 96 | 0.972918 | 0.578974 | 0.563789 |
| 600-700 | 208 | 176 | 32 | 0.592226 | 0.486187 | 0.493277 |
| 700-800 | 265 | 265 | 0 | n/a | n/a | n/a |
| 800-900 | 235 | 235 | 0 | n/a | n/a | n/a |
| 900-1000 | 260 | 260 | 0 | n/a | n/a | n/a |

The zero fraction is 0,0,5.9%,25.3%,44.8%,54.9%,84.6%,100%,100%,100%. For N >= 700
the Pmax=60 / same-level window has no nonzero integer certificate at all; C_obs
is undefined rather than stable.

## 4. Judgment

- Exact SNF confirms the B1-FIX direction: the true algebraic minimum is often
  much smaller than the Q_p certificate (84/108 strict improvements, max C_obs
  2.888 vs the old Q_p max 10.03). The exact max C_obs is below C0=3 on N<=500.
- But the pre-registered stability clause FAILS:
  1. the median C_obs rises from 0.162 to 0.572 over N<=500;
  2. the fraction of rows with no nonzero certificate rises to 56.8% by N<=1000
     and to 100% for N>=700 in this window;
  3. the positive-subset slope is 1.724 (2.073 for min_abs>1), i.e. the exact
     minimum grows like N^1.7-2.1, not a bounded constant.
- Verdict: **STOP / no "有戏" signal under the pre-registered criterion.**
  The relevant true growth is min_abs ~ N^1.5-2.1; the disappearance of nonzero
  certificates at high N is a window/Pmax effect and must not be reported as
  mathematical nonexistence. The correct negative statement is: within
  Pmax=60 and same-level newform constraints, exact minimal |P(f)| is not a
  bounded C_obs family; no B2 support.
- If ever restarted, the necessary change is a larger/adaptive prime window and
  oldform constraints, with a new pre-registration; the current thresholds
  cannot be re-used.

## Files

- coord/b1_exact_snf_500.csv (941 rows, N<=500)
- coord/b1_exact_snf_1000.csv (2122 rows, N<=1000)
- coord/b1_exact_snf_bins.csv (100-wide bins)
- tools/b1_exact_snf.sage, tools/b1_exact_snf_1000.sage
- B1 context: coord/EXPLORATION-B-B1-FIX.md, coord/EXPLORATION-B-B1-FIX2.md
