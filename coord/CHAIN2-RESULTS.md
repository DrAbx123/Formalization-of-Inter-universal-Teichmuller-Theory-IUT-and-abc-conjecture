# CHAIN2-RESULTS — corrected model numbers (A882/A883)

Status: model-level numbers. This file replaces the earlier p=11 and density values; see
the correction note at the end. Not Lean evidence, not an IUT theorem.

**A884 status: 数值待重算（BLOCKED ON stepxi）**。A882/A883 的修正（`c=0.15`、p=11 ramified data、arch 1.4913 vs 1.1394 的差异）尚未独立复核；本文件的表只作模型工作稿，**不作链二判定**。stepxi 重算后回填本文件，并把差异/来源写清楚。

## 1. Correct formulas

Paper-normalized shell volume:
    logMuPaper(p,e,r,n) = (1 + [p=2] - 1/e - r/n) log p.
Auxiliary:
    arch = log(sqrt(2) pi) = 1.491303   (value used in CHAIN2-VOLUME-DATA.md)
    different = -order log p - r/n + arch.
A883 supplies the real per-place values; for the p=11 instance it uses
    p=11, e=10, r=1, n=10, order=1
    => logMuPaper = (1 - 1/10 - 1/10) log 11 = (4/5) log 11 = 1.9183,
    => different = -log 11 - 1/10 + arch.
A883 quoted arch ~ 1.139436, which is WRONG.  Resolution (A885): the green
definition is archConstant = Real.log (Real.sqrt 2 * Real.pi) =
Real.log 2 / 2 + Real.log Real.pi = 1.491303 (theorem
Mzk1DifferentDictionaryActual.archConstant_eq_log / Mzk1ArchTorsionDictionaryActual.archConstant_eq).
The value 1.139436 is discarded; CHAIN2-VOLUME-DATA.md already uses 1.491303.

The corrected l=5 constant is
    c = (l+4)(l-3)/(24l) = 9*2/120 = 18/120 = 0.15
(not 0.45).

## 2. p=11 instance (corrected)

Shell volume (existing chain2 model):
    V_shell(t) = logMuPaper - t log 11 = 1.9183 - 2.3979 t.
Requirement V_req = 0.46365; upper box U = 5.9947.
- t=0: V = 1.9183, inside [0.46365, 5.9947] => q-pilot at order 0 is admissible.
- t=-1: V = 4.3162, inside.
- t=-2: V = 6.7140, above U.
So the integer window is t in {-1, 0}; the earlier claim "t=0 fails" came from the
unramified e=n=1,r=0 value logMuPaper = 0, which does not apply to this ramified data
(e=10, r=1, n=10).

If instead one reads the net hull volume as logMuPaper + different:
- order 1: 1.9183 + (-2.3979 - 0.1 + 1.4913) = 0.9117 (arch = 1.4913, unique correct value).
Both are still above V_req = 0.46365 and below U = 5.9947, so the middle case survives
under either arch value.

Conclusion for the p=11 instance: **middle survives with t=0 (and t=-1)**. G={0} is
admissible for this ramified instance.

## 3. Multi-bad Phase 2 (corrected)

Family (1, 2^k-1, 2^k). Model:
- p=2: e=2, r=1, n=2 => logMuPaper = log 2;
- every odd bad prime: modelled unramified e=n=1, r=0 => logMuPaper = 0.
Then for uniform order t at all bad places:
    V(t) = log 2 - t logdf,   logdf = sum_{p bad} log p.
Requirement V_req = 0.15 logQ, upper U = 2.5 logdf, l=5.

| k | bad primes | logdf | V_req | U | V(0) | V(-1) | V(-2) |
|---:|---|---:|---:|---:|---:|---:|---:|
| 2 | 2, 3 | 1.7918 | 0.7455 | 4.4794 | 0.6931 | 2.4849 | 4.2767 |
| 3 | 2, 7 | 2.6391 | 1.2076 | 6.5976 | 0.6931 | 3.3322 | 5.9713 |
| 4 | 2, 3, 5 | 3.4012 | 1.6442 | 8.5030 | 0.6931 | 4.0943 | 7.4955 |
| 5 | 2, 31 | 4.1271 | 2.0699 | 10.3178 | 0.6931 | 4.8203 | 8.9474 |
| 6 | 2, 3, 7 | 3.7377 | 2.4906 | 9.3442 | 0.6931 | 4.4308 | 8.1685 |
| 7 | 2, 127 | 5.5373 | 2.9089 | 13.8433 | 0.6931 | 6.2305 | 11.7678 |
| 8 | 2, 3, 5, 17 | 6.2344 | 3.3259 | 15.5860 | 0.6931 | 6.9276 | 13.1620 |
| 9 | 2, 7, 73 | 6.9295 | 3.7424 | 17.3238 | 0.6931 | 7.6227 | 14.5522 |
| 10 | 2, 3, 11, 31 | 7.6236 | 4.1586 | 19.0591 | 0.6931 | 8.3168 | 15.9404 |
| 11 | 2, 23, 89 | 8.3173 | 4.5746 | 20.7932 | 0.6931 | 9.0104 | 17.3277 |
| 12 | 2, 3, 5, 7, 13 | 7.9121 | 4.9906 | 19.7801 | 0.6931 | 8.6052 | 16.5173 |
| 13 | 2, 8191 | 9.7039 | 5.4065 | 24.2598 | 0.6931 | 10.3971 | 20.1010 |
| 14 | 2, 3, 43, 127 | 10.3971 | 5.8224 | 25.9929 | 0.6931 | 11.0903 | 21.4874 |
| 15 | 2, 7, 31, 151 | 11.0903 | 6.2383 | 27.7258 | 0.6931 | 11.7835 | 22.8738 |
| 16 | 2, 3, 5, 17, 257 | 11.7835 | 6.6542 | 29.4587 | 0.6931 | 12.4766 | 24.2601 |
| 17 | 2, 131071 | 12.4766 | 7.0701 | 31.1916 | 0.6931 | 13.1698 | 25.6464 |
| 18 | 2, 3, 7, 19, 73 | 10.9726 | 7.4860 | 27.4314 | 0.6931 | 11.6657 | 22.6383 |
| 19 | 2, 524287 | 13.8629 | 7.9019 | 34.6574 | 0.6931 | 14.5561 | 28.4190 |
| 20 | 2, 3, 5, 11, 31, 41 | 12.9467 | 8.3178 | 32.3666 | 0.6931 | 13.6398 | 26.5865 |

For every k = 2..20:
- V(0) = log2 = 0.6931 < V_req (since V_req >= 0.7455); t=0 is OUT.
- V(-1) = log2 + logdf is inside [V_req, U].
- V(-2) = log2 + 2 logdf is inside [V_req, U].
Thus the middle case requires a **negative** order: G must admit allowedLower <= -1.
The G models:
(i) G={0}: V=log2 < V_req => middle excluded (too strong / wrong normalization).
(ii) per-place independent G_p with zero-sum or bounded sum: if it admits t=-1 at all
    places, middle survives; a forced nonnegative range excludes it.
(iii) Step-(xii) identity sum_p t_p log p = 0: uniform t=-1 is not allowed; a mixed
    vector can still produce V in the window for some k, but this is not decided by the
    uniform table. The decisive condition is whether G admits some negative order.

## 4. Verdict

- p=11 ramified instance: middle survives with t=0/t=-1.
- Multi-bad family with p=2 real and odd unramified model: t=0 fails; t=-1 and t=-2
  work for all k. Middle survives **only if G allows negative order** (allowedLower <= -1).
- No proof of SSIneq; actual per-place e,r,n for the odd bad primes and the actual
  Step-(xii) G are still required.

## 5. Correction note

The earlier CHAIN2-RESULTS.md/CHAIN2-PHASE2.md used:
- p=11, e=n=1, r=0 => logMuPaper = log11 (wrong; coefficient is 0), and
- c = 0.45 (wrong; correct 0.15).
A882 corrected those; A883 supplies the ramified real hull values (e=10,r=1,n=10), under
which p=11 has logMuPaper = (4/5)log11 > 0 and the middle survives at t=0. The multi-bad
table keeps the odd-unramified model, where logMuPaper = 0 and negative t is required.
Arch discrepancy RESOLVED (A885): correct arch = log(sqrt(2) pi) = 1.491303; 1.139436 is erroneous and withdrawn.


## 6. G3 recalculation (A884)

G3 scaling law used: for a product of local inclusions with orders t_p,
componentVol((prod_p incl_p(y_p)) * integral) = -(sum_p ord_p(y_p)) * log p. With the real
hull data this means the net volume is

    V = baseShell + sum_p (arch - r_p/n_p) - sum_p t_p log p,

where baseShell is the sum of logMuPaper over bad places and the arch term is added per
bad place. For the p=11 instance this gives
    base = logMuPaper + arch - r/n = 1.9183 + 1.1394 - 0.1 = 2.9577,
    V(t) = 2.9577 - 2.3979 t.

### p=11 instance

Requirement 0.46365, upper 5.9947:

| t | S = t log 11 | V = base - S | in [0.46365,5.9947] |
|---:|---:|---:|---|
| 2 | 4.7958 | -1.8381 | OUT |
| 1 | 2.3979 | 0.5598 | IN |
| 0 | 0 | 2.9577 | IN |
| -1 | -2.3979 | 5.3556 | IN |
| -2 | -4.7958 | 7.7535 | OUT |

G1 (PF equality, single region, S=0): V=2.9577, IN.
G3 (ord-sum inequality): the window requires S in [-3.037, 2.494], equivalently
t in [-1.267, 1.040]; integer t in {-1,0,1}. G3 therefore admits the middle case
provided the ord-sum is allowed to be non-positive (t=0 and t=-1 both work).

### Multi-bad Phase 2

For each bad place add arch: p=2 has base2 = log2 + arch - 1/2 = 1.3325; each odd bad
place has base = arch = 1.1394. Thus

    base(k) = 1.3325 + (#odd bad primes) * 1.1394,
    V(t) = base(k) - t logdf,   logdf = sum_bad log p.

| k | logdf | V_req | U | base(k) | V(0) | V(-1) | G1 (S=0) | G3 (t=-1) |
|---:|---:|---:|---:|---:|---:|---:|---|---|
| 2 | 1.792 | 0.745 | 4.479 | 2.472 | 2.472 | 4.264 | IN | IN |
| 3 | 2.639 | 1.208 | 6.598 | 2.472 | 2.472 | 5.111 | IN | IN |
| 4 | 3.401 | 1.644 | 8.503 | 3.611 | 3.611 | 7.013 | IN | IN |
| 5 | 4.127 | 2.070 | 10.318 | 2.472 | 2.472 | 6.599 | IN | IN |
| 6 | 3.738 | 2.491 | 9.344 | 3.611 | 3.611 | 7.349 | IN | IN |
| 7 | 5.537 | 2.909 | 13.843 | 2.472 | 2.472 | 8.009 | OUT (V_req) | IN |
| 8 | 6.234 | 3.326 | 15.586 | 4.751 | 4.751 | 10.985 | IN | IN |
| 9 | 6.930 | 3.742 | 17.324 | 3.611 | 3.611 | 10.541 | OUT (V_req) | IN |
| 10 | 7.624 | 4.159 | 19.059 | 4.751 | 4.751 | 12.375 | IN | IN |
| 11 | 8.317 | 4.575 | 20.793 | 3.611 | 3.611 | 11.929 | OUT (V_req) | IN |
| 12 | 7.912 | 4.991 | 19.780 | 5.890 | 5.890 | 13.802 | IN | IN |
| 13 | 9.704 | 5.407 | 24.260 | 2.472 | 2.472 | 12.176 | OUT (V_req) | IN |
| 14 | 10.397 | 5.822 | 25.993 | 4.751 | 4.751 | 15.148 | OUT (V_req) | IN |
| 15 | 11.090 | 6.238 | 27.726 | 4.751 | 4.751 | 15.841 | OUT (V_req) | IN |
| 16 | 11.783 | 6.654 | 29.459 | 5.890 | 5.890 | 17.674 | OUT (V_req) | IN |
| 17 | 12.477 | 7.070 | 31.192 | 2.472 | 2.472 | 14.949 | OUT (V_req) | IN |
| 18 | 10.973 | 7.486 | 27.431 | 5.890 | 5.890 | 16.863 | OUT (V_req) | IN |
| 19 | 13.863 | 7.902 | 34.657 | 2.472 | 2.472 | 16.335 | OUT (V_req) | IN |
| 20 | 12.947 | 8.318 | 32.367 | 7.030 | 7.030 | 19.976 | OUT (V_req) | IN |

Reading:
- G1 (PF equality, S=0): V=base(k). It is IN for k=2,3,4,5,6,8,10,12 and OUT (below
  V_req) for the other k. So G1 is not uniformly admissible in the multi-bad family.
- G3 (ord-sum inequality, here the uniform t=-1 solution S=-logdf): V=base+logdf is IN
  for all k=2..20. A non-positive ord-sum / negative order direction is exactly what
  G3 must allow.
- The G3 window in S is [base(k)-U, base(k)-V_req]; t=-1 gives S=-logdf, which lies in
  that interval for all rows.

### Verdict after G3

p=11: middle survives (t=0, -1, 1; G1 at S=0 works).
Multi-bad: G1 fails for about half the k; G3 with a negative ord-sum works for all
k=2..20. Therefore the corrected middle case survives **only if G is G3 (allows negative
ord-sum), not G1 (PF equality single region)**. This is a model statement; actual
odd-place e,r,n and the actual G3 constant R remain to be extracted.


## 7. Transitional FINAL-PROVISIONAL table (A887, arch = 1.491303)

Status: transitional only. This uses arch = log(sqrt(2) pi) = 1.491303 and the hull values
already in CHAIN2-VOLUME-DATA.md; it must be replaced once shehdd's actual Theta-data
(e,n,r for every bad place) is supplied. Marked FINAL-PROVISIONAL.

### p=11 instance

    logMuPaper = (4/5) log 11 = 1.9183, arch = 1.491303, r/n = 0.1,
    base = 1.9183 + 1.491303 - 0.1 = 3.3096,
    V(t) = 3.3096 - 2.3979 t, window [0.46365, 5.9947].

| t | V(t) | status |
|---:|---:|---|
| 2 | -1.4862 | OUT |
| 1 | 0.9117 | IN |
| 0 | 3.3096 | IN |
| -1 | 5.7075 | IN |
| -2 | 8.1054 | OUT |

G1 (S=0): V=3.3096 IN. G3: window requires S in [-2.6851, 2.8460], equivalently
t in [-1.12, 1.19]; integer t in {-1,0,1}. p=11 survives under both G1 and G3.

### Multi-bad Phase 2 (arch term per bad place)

    p=2: base2 = log2 + arch - 1/2 = 1.6844;
    odd bad p: base = arch = 1.4913;
    base(k) = 1.6844 + (#odd bad primes) * 1.4913;
    V(t) = base(k) - t logdf.

| k | logdf | V_req | U | base(k) | V(0) G1 | V(-1) G3 | V(-2) |
|---:|---:|---:|---:|---:|---|---:|---:|
| 2 | 1.7918 | 0.7455 | 4.4794 | 3.1758 | 3.1758 IN | 4.9675 OUT | 6.7593 OUT |
| 3 | 2.6391 | 1.2076 | 6.5976 | 3.1758 | 3.1758 IN | 5.8148 IN | 8.4539 OUT |
| 4 | 3.4012 | 1.6442 | 8.5030 | 4.6671 | 4.6671 IN | 8.0683 IN | 11.4695 OUT |
| 5 | 4.1271 | 2.0699 | 10.3178 | 3.1758 | 3.1758 IN | 7.3029 IN | 11.4300 OUT |
| 6 | 3.7377 | 2.4906 | 9.3442 | 4.6671 | 4.6671 IN | 8.4047 IN | 12.1424 OUT |
| 7 | 5.5373 | 2.9089 | 13.8433 | 3.1758 | 3.1758 IN | 8.7131 IN | 14.2504 OUT |
| 8 | 6.2344 | 3.3259 | 15.5860 | 6.1584 | 6.1584 IN | 12.3928 IN | 18.6272 OUT |
| 9 | 6.9295 | 3.7424 | 17.3238 | 4.6671 | 4.6671 IN | 11.5966 IN | 18.5261 OUT |
| 10 | 7.6236 | 4.1586 | 19.0591 | 6.1584 | 6.1584 IN | 13.7820 IN | 21.4056 OUT |
| 11 | 8.3173 | 4.5746 | 20.7932 | 4.6671 | 4.6671 IN | 12.9843 IN | 21.3016 OUT |
| 12 | 7.9121 | 4.9906 | 19.7801 | 7.6497 | 7.6497 IN | 15.5617 IN | 23.4738 OUT |
| 13 | 9.7039 | 5.4065 | 24.2598 | 3.1758 | 3.1758 OUT | 12.8797 IN | 22.5836 IN |
| 14 | 10.3971 | 5.8224 | 25.9929 | 6.1584 | 6.1584 IN | 16.5555 IN | 26.9527 OUT |
| 15 | 11.0903 | 6.2383 | 27.7258 | 6.1584 | 6.1584 OUT | 17.2487 IN | 28.3390 OUT |
| 16 | 11.7835 | 6.6542 | 29.4587 | 7.6497 | 7.6497 IN | 19.4331 IN | 31.2166 OUT |
| 17 | 12.4766 | 7.0701 | 31.1916 | 3.1758 | 3.1758 OUT | 15.6524 IN | 28.1290 IN |
| 18 | 10.9726 | 7.4860 | 27.4314 | 7.6497 | 7.6497 IN | 18.6222 IN | 29.5948 OUT |
| 19 | 13.8629 | 7.9019 | 34.6574 | 3.1758 | 3.1758 OUT | 17.0387 IN | 30.9016 IN |
| 20 | 12.9467 | 8.3178 | 32.3666 | 9.1410 | 9.1410 IN | 22.0876 IN | 35.0343 OUT |

G1 (PF equality, V=base): IN for k = 2,3,4,5,6,7,8,9,10,11,12,14,16,18,20; OUT for
k = 13,15,17,19 (base below V_req). So G1 is **not uniformly admissible**.
G3 (uniform t=-1, V=base+logdf): IN for every k = 2..20. t=-2 is OUT for all rows
(above U). Therefore in the transitional table the multi-bad middle case survives under
G3 for all k, while G1 fails for 4 of 19 rows.

### Transitional verdict

- p=11: G1 and G3 both survive.
- Multi-bad: G1 fails for k=13,15,17,19; G3 survives all k=2..20.
- Necessary condition: G must be G3 (negative ord-sum), not G1.
- Pending: real e,n,r from shehdd's Theta-data; actual arch constant (1.491303 vs
  1.139436); actual Step-(xii) ord-sum range. Replace this table when those arrive.


## 8. FINAL (A893) — shehdd Theta-data + hull volumes + A892 arch

Data source (FINAL):
- l = 5 Theta-data; p=2: (e,n,r) = (1,4,1) => logMuPaper = (1 + 1 - 1 - 1/4) log2 = (3/4)log2 = 0.51986;
- odd bad places: (e,n,r) = (1,1,0) => logMuPaper = 0;
- arch = 1.491303, applied **globally once** (not per bad place);
- torsion: base = sum finiteTerm + arch - sum torsion; the task supplies no torsion value,
  so the tables use T := sum torsion = 0 and give sensitivity below.

Hence base = (3/4)log2 + 1.491303 = 2.011163 (T=0).

### p=11 instance (FINAL)

V(t) = base - t log11 = 2.011163 - 2.397895 t; window [0.46365, 5.9947].

| t | V(t) | status |
|---:|---:|---|
| 2 | -2.7846 | OUT |
| 1 | -0.3867 | OUT (below V_req) |
| 0 | 2.0112 | IN |
| -1 | 4.4091 | IN |
| -2 | 6.8070 | OUT (above U) |

G1 (PF equality, t=0): V=2.0112 IN. G3 (negative ord): t=-1, V=4.4091 IN; the ord-sum
window S = base - V is [-3.9835, 1.5475], so integer t in {-1, 0}. p=11: G1 and G3 both
survive.

### Multi-bad Phase 2 (FINAL, T=0)

V(t) = base - t logdf, logdf = sum_bad log p, base = 2.011163 (independent of k because
all odd finite terms are 0).

| k | logdf | V_req | U | V(0) G1 | V(-1) G3 | V(-2) |
|---:|---:|---:|---:|---|---|---|
| 2 | 1.7918 | 0.7455 | 4.4794 | 2.0112 IN | 3.8029 IN | 5.5947 OUT |
| 3 | 2.6391 | 1.2076 | 6.5976 | 2.0112 IN | 4.6502 IN | 7.2893 OUT |
| 4 | 3.4012 | 1.6442 | 8.5030 | 2.0112 IN | 5.4124 IN | 8.8136 OUT |
| 5 | 4.1271 | 2.0699 | 10.3178 | 2.0112 OUT | 6.1383 IN | 10.2654 IN |
| 6 | 3.7377 | 2.4906 | 9.3442 | 2.0112 OUT | 5.7488 IN | 9.4865 OUT |
| 7 | 5.5373 | 2.9089 | 13.8433 | 2.0112 OUT | 7.5485 IN | 13.0858 IN |
| 8 | 6.2344 | 3.3259 | 15.5860 | 2.0112 OUT | 8.2456 IN | 14.4800 IN |
| 9 | 6.9295 | 3.7424 | 17.3238 | 2.0112 OUT | 8.9407 IN | 15.8702 IN |
| 10 | 7.6236 | 4.1586 | 19.0591 | 2.0112 OUT | 9.6348 IN | 17.2584 IN |
| 11 | 8.3173 | 4.5746 | 20.7932 | 2.0112 OUT | 10.3284 IN | 18.6457 IN |
| 12 | 7.9121 | 4.9906 | 19.7801 | 2.0112 OUT | 9.9232 IN | 17.8353 IN |
| 13 | 9.7039 | 5.4065 | 24.2598 | 2.0112 OUT | 11.7151 IN | 21.4190 IN |
| 14 | 10.3971 | 5.8224 | 25.9929 | 2.0112 OUT | 12.4083 IN | 22.8055 IN |
| 15 | 11.0903 | 6.2383 | 27.7258 | 2.0112 OUT | 13.1015 IN | 24.1918 IN |
| 16 | 11.7835 | 6.6542 | 29.4587 | 2.0112 OUT | 13.7947 IN | 25.5781 IN |
| 17 | 12.4766 | 7.0701 | 31.1916 | 2.0112 OUT | 14.4878 IN | 26.9644 IN |
| 18 | 10.9726 | 7.4860 | 27.4314 | 2.0112 OUT | 12.9837 IN | 23.9563 IN |
| 19 | 13.8629 | 7.9019 | 34.6574 | 2.0112 OUT | 15.8741 IN | 29.7370 IN |
| 20 | 12.9467 | 8.3178 | 32.3666 | 2.0112 OUT | 14.9578 IN | 27.9045 IN |

Results:
- G1 (t=0, single region): IN only k=2,3,4; OUT for k=5..20 (V_req exceeds base).
- G3 uniform t=-1: **IN for every k=2..20**.
- t=-2: OUT for k=2,3,4 (above U), IN for k=5..20.
Thus the multi-bad middle case survives under G3, not under G1 (G1 fails already at k=5).

### Torsion sensitivity

With T = sum torsion:
- p=11 G1 survives iff T <= base - V_req = 2.0112 - 0.46365 = 1.5475; G3 t=-1 survives
  iff T <= base + log11 - V_req = 3.945.
- Multi G3 t=-1 survives iff T <= base + logdf - V_req; the minimum threshold is at k=2:
  2.0112 + 1.7918 - 0.7455 = 3.0575. So any T <= 3.05 keeps G3 alive; T=0 is the
  conservative FINAL table.
- Multi G1 already fails at k=5 with T=0, so no positive torsion can rescue G1.

### FINAL verdict

- p=11: G1 and G3 both survive; integer t in {-1,0}.
- Multi-bad: **G1 fails for k>=5; G3 survives all k=2..20**; t=-1 is the uniform witness.
- Condition: chain2 middle case is alive only in the G3 (negative ord-sum) regime; G1
  single-region PF equality is excluded for the multi-bad family.
- Remaining data: torsion T (tables assume 0; threshold 3.05 for G3, 1.55 for p=11 G1);
  actual Step-(xii) range; this is a FINAL model table, not a proof of SSIneq.

## A896 data contradiction registry

**p=11 has two conflicting local data sets; no numerical verdict until stepxi adjudicates.**

| source | data | base | status |
|---|---|---|---|
| A892 note | `e=n=1, r=0` | approx 1.49 | conflicts with §9/§10 |
| A883 / §9-§10 | `e=10, r=1, n=10` | approx 3.31 | candidate but unadjudicated |

- Also unify arch: `log(sqrt(2)*pi)=1.491303`; 1.1394 is withdrawn. Current G3 tables still use 1.1394 in places.
- Evidence pin: root `Iut/` tree `rlf_unique:473`; tmp copy `:427` is obsolete.
- `CHAIN2-RESULTS/PHASE2` numbers are model-level only; do not use as final/evidence.
