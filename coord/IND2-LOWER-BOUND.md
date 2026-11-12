# IND2-LOWER-BOUND — gapHullAt/ind2Term lower bounds (A1077)

Status: read-only algebra; no compile.  `gapHullAt` is green nonnegative, but
the C0 `frac` formula is conditional on a missing hull equality.

## 1. Definitions and green facts

- `ind2Term` (`Gap.lean:747`):
  `V(leastHull(thetaComponent)) - V(scaleElt • leastHull(shell))`.
- `ind2Term_nonneg` (`Gap.lean:756`): `0 ≤ ind2Term`.
- `gapHullAt` (`Gap.lean:895`):
  finite `p`: `Σ_c tupleWeight p c · ind2Term`;
  `∞`: `0`.
- `gapHullAt_eq` (`Gap.lean:919`): packetVol difference.
- `gapHullAt_nonneg` (`Gap.lean:937`): `0 ≤ gapHullAt`.
- `gapHullAt_eq_zero` (`Gap.lean:945`): `p ∉ badChars ⇒ gapHullAt = 0`.
- `tupleWeight = ∏_j weight` (`Container:338`), each `weight > 0`
  (`Container:147`).

Thus the unconditional lower bound is only
```
0 ≤ gapHullAt D i vQ
```
and at finite `p`:
```
0 ≤ Σ_c w_c·ind2Term.
```

## 2. The C0 `frac` formula

`coord/C0-EXACT-DERIVATION.md` derives, under A1-A4:
```
ind2Term = frac(x)·log p,   x = j²·v_p(q)/(2ℓ),   frac(x)=x-floor x ∈ [0,1).
```
Here `v_p(q) = qOrder/(2ℓ·ramIdx)` in general, or `qOrder/(2ℓ)` at an
unramified section place.

**Status: not a theorem.**  The missing core input is
`leastHull_thetaComponent_eq_pow_floor`:
```
HΘ = p^{-floor(x)} • leastHull(shell)
```
and the consequent `V(HΘ) = V(L) - floor(x)logp`.  Without it, no explicit
lower bound beyond `0` is available.

## 3. Conditional lower bound for `ind2Term` and `gapHullAt`

Assume the explicit hypothesis
```lean
hfrac : ∀ (i) (p : Nat.Primes) (c),
  (p : Nat) ∈ D.badChars →
  frac (j² * qOrder/(2*l) : Real) * Real.log p ≤ ind2Term D i p c
```
where `j = i.1 + 1` and `qOrder`/`v_p(q)` is the local q order.

Then:
```lean
theorem gapHullAt_ge_frac_sum
    (hfrac : ∀ p c, (p : Nat) ∈ D.badChars →
      frac (...) * Real.log p ≤ ind2Term D i p c) :
    (∑ c, tupleWeight p c * frac (...) * Real.log p) ≤ gapHullAt D i (.finite p) := by
  unfold gapHullAt
  refine Finset.sum_le_sum fun c _ => ?_
  exact mul_le_mul_of_nonneg_left (hfrac p c ...)
    (Finset.prod_nonneg fun _ _ => (weight_pos _ _ _).le)
```
At `p ∉ badChars`, both sides are `0` (use `gapHullAt_eq_zero`; `frac` is `0`
because `scaleElt=1`).

Thus conditionally:
```
gapHullAt D i (.finite p) ≥ Σ_c w_{p,c}·frac(j² v_p(q)/(2ℓ))·log p.
```

## 4. Sum over primes

`gapHullAt` is finitely supported (`finite_support_gapHullAt`, Gap:949), and
vanishes outside bad residue characteristics plus `∞`, `2`, ramified places.
Under `hfrac` one gets
```
Σ_p gapHullAt D i (.finite p)
  ≥ Σ_{p ∈ badChars} Σ_c w_{p,c}·frac(j² v_p(q)/(2ℓ))·log p.
```
For `p ∉ badChars` the RHS term is `0`; for `p=2`/ramified the C0 formula may
need a different exponent (`e` and the ramified local order), so it should be
stated separately or excluded.

## 5. Parity grouping

Let `j = i.1 + 1`.  The `frac` argument is `j²·v_p(q)/(2ℓ)`.

- `j = 2r` (even): `j² = 4r²`, so
  `frac(j²v/(2ℓ)) = frac(2r² v/ℓ)`.
- `j = 2r+1` (odd): `j² = 8s+1` (`s=r(r+1)/2`), so
  `frac(j²v/(2ℓ)) = frac((8s+1)v/(2ℓ))`.

Equivalently, only `j² v mod 2ℓ` matters.  A parity split of the capsule sum
gives
```
Σ_{j=1}^{l⋇} frac(j²v/(2ℓ))
  = Σ_{r: 2r≤l⋇} frac(2r²v/ℓ)
    + Σ_{r: 2r+1≤l⋇} frac((8s+1)v/(2ℓ)).
```
No closed form is claimed without `v mod 2ℓ` data.  For a fixed bad prime `p`,`
the weighted sum is
```
Σ_c w_{p,c}·[Σ_{j} frac(j² v_p(q_c)/(2ℓ))]·log p
```
with `q_c` the qOrder at the distinguished label of the tuple `c`.

## 6. Verdict

- Green: `0 ≤ ind2Term` and `0 ≤ gapHullAt`.
- Not green: `ind2Term ≥ frac(...)logp`; it needs
  `leastHull_thetaComponent_eq_pow_floor`, which is the C0 core gap.
- Conditional lower bound: `gapHullAt ≥ Σ_c w_c frac(...) logp` is immediate
  from `hfrac` + weight positivity.
- Sum over primes and parity split are algebraic consequences of the
  conditional bound; no unconditional positive lower bound is proved.
- lana marks the exact `ind2Term` value Open (`Gap.lean` docstring); the
  C0 derivation is source-level conditional, not a Lean theorem.
