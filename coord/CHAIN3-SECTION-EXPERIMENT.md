# CHAIN3 — section experiment for (1, 3^n-1, 3^n), l = 7 (A878)

Status: **model calculation**, not an IUT theorem. The actual Theta-data field K, the
archimedean metric, and the hull exponents of the concrete curve are PENDING in the repo
(no compiled lana blocks yet). This note fixes the model explicitly so the sign test is
reproducible; it is not evidence for a green inequality.

## 1. Chain3 object and the candidate section

From ROUTES-FINAL-GAP §14 (chain 3):
- arithmetic line bundle H_j = det(hull_j) tensor L_q^{-(j^2-1)};
- a nonzero global section x_j;
- candidate sections: (a) ratio of theta constants at E; (b) discriminant of the
  l-division polynomial; (c) kappa-coric function;
- expected mechanism: x_j != 0 => deg H_j >= -arch(x_j) => wall of capsule j => average in j.

For the experiment use candidate (a), the theta-constant ratio. In the IUT normalization
its V-place valuation is
    ord_p(theta_j / theta_0) = (j^2 - 0^2) * ord_p(q) / (2 l),        (1)
where q is the q-pilot and l = 7.

## 2. Model choices

Take the model field K = Q (so [K:Q] = 1 and componentVol has no extra degree denominator;
see R1 note). For the triple
    (a,b,c) = (1, 3^n - 1, 3^n),   a+b=c,   gcd(a,b)=1,
set
    q = (abc)^2,      ord_p(q) = 2 v_p(abc).              (2)
Then
    log Q := sum_p ord_p(q) log p = 2 log(abc).             (3)

For l = 7, j in {1,2,3}. The V set is modelled as the finite bad primes (all p | abc);
the archimedean component is treated separately in §4. Hull denominator margin is the
L_q part of H_j: (j^2 - 1) log Q (the det(hull_j) part is read as the hull normalization
and is zero for the tame unramified model, h_p = 1 - 1/e = 0).

## 3. Explicit valuation table (l = 7)

For candidate (a) and j:
    V_pos(j) = (j^2) * log Q / (2 l) = (j^2 / 14) * log Q,
    H_den(j) = (j^2 - 1) * log Q,
    residual R(j) = V_pos(j) - H_den(j).

| n | abc | bad primes p (v_p) | log Q | V_pos(j=1) | H_den(j=1) | R(1) |
|---:|---:|---|---:|---:|---:|---:|
| 1 | 6 = 2*3 | 2(1), 3(1) | 2 log 6 | (1/14) logQ | 0 | + (positive) |
| 2 | 72 = 2^3*3^2 | 2(3), 3(2) | 2 log 72 | (1/14) logQ | 0 | + |
| 3 | 702 = 2*3^3*13 | 2(1), 3(3), 13(1) | 2 log 702 | (1/14) logQ | 0 | + |
| 4 | 6480 = 2^4*3^4*5 | 2(4), 3(4), 5(1) | 2 log 6480 | (1/14) logQ | 0 | + |
| 5 | 58806 = 2*3^5*11^2 | 2(1), 3(5), 11(2) | 2 log 58806 | (1/14) logQ | 0 | + |

(The n=5 factorization is 3^5 = 243, 3^5-1 = 242 = 2*11^2, so
abc = 242*243 = 58806 = 2*3^5*11^2; v_p = (1,5,2).)

For j = 2:

| n | V_pos(2) | H_den(2) | R(2) = V_pos - H_den | sign |
|---:|---:|---:|---:|---|
| 1 | (4/14)logQ = (2/7)logQ | 3 logQ | (2/7 - 3)logQ = -(19/7)logQ | negative |
| 2 | (2/7)logQ | 3 logQ | -(19/7)logQ | negative |
| 3 | (2/7)logQ | 3 logQ | -(19/7)logQ | negative |
| 4 | (2/7)logQ | 3 logQ | -(19/7)logQ | negative |
| 5 | (2/7)logQ | 3 logQ | -(19/7)logQ | negative |

For j = 3:
    V_pos(3) = (9/14)logQ, H_den(3) = 8 logQ,
    R(3) = (9/14 - 8)logQ = -(103/14)logQ < 0.

The q-exponent distribution does not enter R(j) in this model: V_pos scales with
sum ord_p(q) log p = logQ, so R(j) = (j^2/(2l) - (j^2-1)) logQ
= (j^2 - 14(j^2-1))/14 logQ = (-13 j^2 + 14)/14 logQ, which is negative for j >= 2.

## 4. Identity check (the expected veto)

The candidate theta ratio is a ratio of theta constants, hence a modular unit: its
product formula over **all** places is zero. In the model the finite V positive part is
P = (j^2/14) logQ; the archimedean component of the same unit is -P (up to the bounded
archimedean metric/denominator term), so the full sum is an identity, not an inequality.
This is exactly the known obstacle in §14 chain 3: the V-positive contribution is canceled
by the archimedean/product-formula negative term, and the hull denominator margin
(j^2 - 1) logQ makes the finite residual negative for j >= 2.

## 5. Decision

- j = 1: V_pos = logQ/14 > 0 and H_den = 0, so the finite test alone is positive; but this
  is the degenerate case with no L_q factor. It gives no wall inequality and does not
  produce (s-1)A <= V.
- j >= 2: R(j) < 0 (e.g. j=2: -19/7 logQ), so the V positive contribution does **not**
  exceed the hull denominator margin.
- Including the archimedean/product-formula term gives an identity, not a positive
  residual.

**Verdict: chain 3 is vetoed by this experiment** (expected identity; no positive residual
for j >= 2). The test is a model calculation; it does not prove the actual IUT setup and
does not enter the evidence chain. The exact archimedean metric, K, and hull exponents are
PENDING; the conclusion should be re-run once the lana Cor312/hull blocks compile.

## 6. Candidate sections status

| candidate | source | status |
|---|---|---|
| theta constant ratio at E | IUT II/III theta values; valuation formula (1) is the only one used | model input; actual theta constants not compiled in the repo |
| discriminant of l-division polynomial | equals l-power times Delta-power (global identity) | global identity, same product-formula veto |
| kappa-coric function | not constructed; no valuation formula | PENDING |

R1 cross-reference: componentVol normalization matches L3 with no (j/2)d correction; the
margin above uses dot(hull) degree and L_q exponent, not componentVol normalization.
