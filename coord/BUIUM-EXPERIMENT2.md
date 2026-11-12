# BUIUM-EXPERIMENT2 — Route γ numerical feasibility report

Date: 2026-11-12. Status: **experiment not executed for the Buium invariant; route γ remains paused.**

## 1. Reproducible Szpiro side

Frey triples `(a,b,c) = (1, 2^k-1, 2^k)`, curve `y^2 = x(x-a)(x+b)`:
`|Δ| = 16(abc)^2`, and (for the odd part) `N = rad_odd(abc) = 2·rad(2^k-1)`.
Using trial-division radical on `2^k-1`:

| k | Δ (approx) | N | σ = log|Δ|/log N |
|---|---|---|---|
| 2 | 2.304000e+3 | 6 | 4.321 |
| 3 | 5.017600e+4 | 14 | 4.101 |
| 4 | 9.216000e+5 | 30 | 4.038 |
| 5 | 1.574502e+7 | 62 | 4.015 |
| 6 | 2.601124e+8 | 42 | 5.184 |
| 7 | 4.228121e+9 | 254 | 4.003 |
| 8 | 6.818365e+10 | 510 | 4.001 |
| 9 | 1.095221e+12 | 1022 | 4.001 |
| 10 | 1.755784e+13 | 2046 | 4.000 |
| 11 | 2.812002e+14 | 4094 | 4.000 |
| 12 | 4.501401e+15 | 2730 | 4.555 |
| 13 | 7.204000e+16 | 16382 | 4.000 |
| 14 | 1.152781e+18 | 32766 | 4.000 |
| 15 | 1.844562e+19 | 65534 | 4.000 |
| 16 | 2.951389e+20 | 131070 | 4.000 |
| 17 | 4.722294e+21 | 262142 | 4.000 |
| 18 | 7.555729e+22 | 58254 | 4.801 |
| 19 | 1.208921e+24 | 1048574 | 4.000 |
| 20 | 1.934278e+25 | 419430 | 4.497 |
| 21 | 3.094847e+26 | 599186 | 4.585 |

Full reproducible data n=100: k=2..101; σ = 2 log(2^k(2^k-1)) / log(2·rad(2^k-1)), computed by the same trial-division script (Python: `rad`, `math.log`).  These curves have σ ≈ 4 in the range; no high-Szpiro spread, so they are a poor dataset for correlation.

## 2. Buium p-curvature side

The invariant `v_p(f^1_p(E))` is not implemented in this repo or vendor trees; no green formula
for `δ_p x = (φ(x)-x^p)/p` on an elliptic curve is available in Lean or Python here.
Therefore the correlation requested in §3 **cannot be computed from current assets**; any number
would be fabricated.  We do not report one.

## 3. Verdict

* Szpiro dataset is reproducible (formula above; n=100 possible).
* Buium invariant: **NO computable implementation / no green formula** ⇒ correlation NOT computed.
* Route γ: **not supported by evidence; remains paused**.  To unblock: provide a concrete
  p-curvature formula (or vendor implementation) and a high-Szpiro dataset (Mestre/Mazur tables)
  with conductor data; then rerun this experiment.

## 4. Lean interface candidate

None asserted.  If a formula arrives, candidate interface:
`buiumInvariant : EllipticCurve → Prime → ℤ` with
`szpiroRatio E = log|Δ|/log N` and a correlation theorem shape `r² ≥ threshold`
as an explicit empirical Prop (never a theorem without data).
