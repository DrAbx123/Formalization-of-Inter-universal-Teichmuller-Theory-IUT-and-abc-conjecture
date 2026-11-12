# S2481: coeff-limit forward map + compatibility helpers actual

Date: 2026-11-03. Layer O (M3/M4 coefficient comparison). Serial compile.

## Deliverable

`tmp/sheaf/xif/paper/S2481CoeffLimitActual.lean`

```text
EXIT=0
lines=120
source SHA256=24677F5EE0B58A049A61CC7B93740FDAFF88724AB1A173B110B12DEED2E62A7B
olean SHA256=520CF5F8CBA8CBD5CDFB6B43A926E5A1AC3920B2FFC0590DB88FD1253B018749
olean bytes=300144
axioms:
  S2481Eval_compat, S2481EvalLimit,
  S2481_val_pow, S2481_val_eq_pow -> propext, Classical.choice, Quot.sound
```

## Actual

```text
S2481Roots p n := rootsOfUnity n (Otri p)
S2481Proj p h : S2481Roots p n →* S2481Roots p m  (h : m ∣ n)
S2481CoeffLimit p  (compatible family carrier)
S2481Eval p f n
S2481Eval_compat f h
S2481EvalLimit f : S2481CoeffLimit p
S2481_val_pow L n : (L.val n)^n = 1
S2481_val_eq_pow L h : L.val m = (L.val n)^(n/m)
```

The last two are exactly the compatibility tools needed for the reverse map:
- finite order of every value;
- m-value as power of the n-value under divisibility.

## Exact remaining for S2481Reverse

```text
S2481_coe_independent
  (L : S2481CoeffLimit p) {k k' : ℤ} {m n : ℕ+}
  (h : (k : ℚ)/(n : ℚ) = (k' : ℚ)/(m : ℚ) in ℚ/ℤ) :
  ((L.val m : (Otri p)ˣ) ^ k) = ((L.val n : (Otri p)ˣ) ^ k')
```

Proof plan:

1. set `N = n * m` (need compatible choice of positive product);
2. use `S2481_val_eq_pow` with `m ∣ N` and `n ∣ N` to rewrite both
   sides as powers of `L.val N`;
3. `S2481_val_pow L N` gives `(L.val N)^N = 1`;
4. the rational equality in `ℚ/ℤ` gives
   `k * m - k' * n ∈ N ℤ`; hence the integer exponents agree modulo N;
5. conclude unit powers equal.

Then:

```text
S2481ReverseCandidate (L) : AddCircle 1 → (Otri p)ˣ
  q ↦ (L.val q.den) ^ q.num
```

with `q ↦ q+1` periodicity and quotient well-definedness, then:

```text
S2481Reverse L : PsiCnsCyclotome p
S2481Equiv : PsiCnsCyclotome p ≃* S2481CoeffLimit p
```

## Status

- forward map actual;
- compatibility/power helper lemmas actual;
- reverse map and equivalence exact missing;
- no fake inverse or assumed well-definedness.
