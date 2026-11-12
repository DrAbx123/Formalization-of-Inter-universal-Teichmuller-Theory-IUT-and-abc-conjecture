# CHAIN3-RESULTS — numerical experiment (1, 3^n-1, 3^n), l = 7

Status: model calculation, source-level. No lana Cor312/hull olean is available, so this
does not prove an IUT inequality and does not enter the evidence chain. It does give a
reproducible sign table for the chain-3 test.

## 1. Setup

Triple: (a,b,c) = (1, 3^n - 1, 3^n), n = 2..20, l = 7.
Let q = (abc)^2 and logQ := 2 log(abc). For the theta-constant ratio
    u = theta_j / theta_0,
the IUT valuation formula at a finite V-place p is
    ord_p(u) = (j^2 - 0^2) * ord_p(q) / (2l)
             = j^2 * v_p(abc) / 7            since l=7, ord_p(q)=2 v_p(abc).
At the archimedean place the same unit has
    ord_inf(u) = - j^2 * logQ / 14
(this is the product-formula partner of the finite V sum; sign fixed so that
sum_finite ord_p(q) log p + arch(q) = 0).

For H_j = det(hull_j) tensor L_q^{-(j^2-1)} the denominator margin is taken as
    H_den(j) = (j^2 - 1) * logQ
(the det(hull_j) part is normalized to zero in the tame/unramified model; this is the
same model caveat as R1). The V positive contribution is
    V_pos(j) = (j^2 / 14) * logQ.
Hence residual
    R(j) = V_pos(j) - H_den(j) = (j^2/14 - (j^2-1)) logQ
         = ((-13 j^2 + 14)/14) * logQ.

## 2. Table (j = 2; n = 2..20)

| n | bad primes of abc (with exponents) | logQ | V_pos(2) | H_den(2) | R(2) | sign |
|---:|---|---:|---:|---:|---:|---|
| 2 | `3^2` ; 2^3 * 3^2 | 8.553332 | 1.221905 | 25.659997 | -24.438092 | negative |
| 3 | `3^3` ; 2^1 * 3^3 * 13^1 | 13.107867 | 1.872552 | 39.323600 | -37.451048 | negative |
| 4 | `3^4` ; 2^4 * 3^4 * 5^1 | 17.552952 | 2.507565 | 52.658855 | -50.151290 | negative |
| 5 | `3^5` ; 2^1 * 3^5 * 11^2 | 21.963998 | 3.137714 | 65.891995 | -62.754281 | negative |
| 6 | `3^6` ; 2^3 * 3^6 * 7^1 * 13^1 | 26.363950 | 3.766279 | 79.091849 | -75.325570 | negative |
| 7 | `3^7` ; 2^1 * 3^7 * 1093^1 | 30.760229 | 4.394318 | 92.280688 | -87.886370 | negative |
| 8 | `3^8` ; 2^5 * 3^8 * 5^1 * 41^1 | 35.155288 | 5.022184 | 105.465865 | -100.443681 | negative |
| 9 | `3^9` ; 2^1 * 3^9 * 13^1 * 757^1 | 39.549941 | 5.649992 | 118.649822 | -112.999831 | negative |
| 10 | `3^10` ; 2^3 * 3^10 * 11^2 * 61^1 | 43.944458 | 6.277780 | 131.833373 | -125.555593 | negative |
| 11 | `3^11` ; 2^1 * 3^11 * 23^1 * 3851^1 | 48.338929 | 6.905561 | 145.016788 | -138.111227 | negative |
| 12 | `3^12` ; 2^4 * 3^12 * 5^1 * 7^1 * 13^1 * 73^1 | 52.733386 | 7.533341 | 158.200158 | -150.666817 | negative |
| 13 | `3^13` ; 2^1 * 3^13 * 797161^1 | 57.127838 | 8.161120 | 171.383513 | -163.222394 | negative |
| 14 | `3^14` ; 2^3 * 3^14 * 547^1 * 1093^1 | 61.522288 | 8.788898 | 184.566863 | -175.777965 | negative |
| 15 | `3^15` ; 2^1 * 3^15 * 11^2 * 13^1 * 4561^1 | 65.916737 | 9.416677 | 197.750212 | -188.333535 | negative |
| 16 | `3^16` ; 2^6 * 3^16 * 5^1 * 17^1 * 41^1 * 193^1 | 70.311186 | 10.044455 | 210.933559 | -200.889104 | negative |
| 17 | `3^17` ; 2^1 * 3^17 * 1871^1 * 34511^1 | 74.705636 | 10.672234 | 224.116907 | -213.444673 | negative |
| 18 | `3^18` ; 2^3 * 3^18 * 7^1 * 13^1 * 19^1 * 37^1 * 757^1 | 79.100085 | 11.300012 | 237.300254 | -226.000242 | negative |
| 19 | `3^19` ; 2^1 * 3^19 * 1597^1 * 363889^1 | 83.494534 | 11.927791 | 250.483602 | -238.555811 | negative |
| 20 | `3^20` ; 2^4 * 3^20 * 5^2 * 11^2 * 61^1 * 1181^1 | 87.888983 | 12.555569 | 263.666949 | -251.111380 | negative |

For every n = 2..20, R(2) is negative (roughly -(19/7) logQ); the variation in the table
comes only from logQ, not from the exponents.

## 3. j values

- j = 1: H_den = 0, V_pos = logQ/14 > 0. This is the degenerate case (no L_q factor);
  it does not produce a wall inequality.
- j = 2: R = -(19/7) logQ < 0 for all n.
- j = 3: V_pos = (9/14) logQ, H_den = 8 logQ, R = -(103/14) logQ < 0 for all n.
- For general j >= 2, R(j) = ((-13 j^2 + 14)/14) logQ < 0.

## 4. Full-place cancellation

Including the archimedean component:
    V_pos(j) + ord_inf(u) = (j^2/14) logQ - (j^2/14) logQ = 0.
So the **all-place** divisor of the theta ratio is principal: the positive V contributions
are exactly canceled by the archimedean negative term. This is the expected identity.
Consequently the chain-3 mechanism cannot extract a positive inequality from this unit:
the finite V test is positive only in the degenerate j=1 case, and for every j >= 2 it is
already dominated by the hull denominator margin.

## 5. Decision

**Chain 3 is vetoed by this experiment.** The candidate theta ratio gives an identity
over all places; the finite V positive contribution minus the hull denominator margin is
negative for all j >= 2 in every n = 2..20. There is no positive residual to continue the
chain.

The l-division-polynomial discriminant is also a global identity (its divisor is a
power of Delta plus an l-supported term), so it gives the same product-formula veto; the
kappa-coric candidate is not constructed and remains PENDING.

Caveats: K=F_mod, the actual archimedean metric, and the hull exponents of the concrete
Theta-data are not compiled; the table is a model calculation, not a theorem. Re-run after
the lana Cor312/hull blocks are green.

R1 cross-reference: componentVol normalization matches L3 with no (j/2)d correction; the
table uses dot(hull) degree and L_q exponent, not a componentVol normalization factor.
