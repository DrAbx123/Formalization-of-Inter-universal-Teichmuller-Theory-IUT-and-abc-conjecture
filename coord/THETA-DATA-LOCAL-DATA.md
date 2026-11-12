# THETA-DATA-LOCAL-DATA — Frey bad-prime `(e,n,r)` adjudication (A887)

Date: 2026-11-12.  Scope: paper Θ-data local data at a **multiplicative bad prime**
`p` with `p ∤ l` (so `p ≠ l`), for a Frey curve over `F = ℚ`; the auxiliary prime is `l`.

## 0. Verdict (first)

* `K = F(E[l])` is the `l`-torsion field of the Θ-data (`Iut/Cor312/ThetaData/Basic.lean:127-132`, `InitialThetaData.K`).
* At a multiplicative prime `p ∤ l`, **`K/ℚ` is unramified at `p`** (inertia acts trivially on `E[l]`);
  hence `e = 1`.
* `n = [K_w : ℚ_p] = f` is the **residue degree** = order of Frobenius on the 1-dimensional
  `E[l]` over `𝔽_p`: `f = ord_l(p)` in the split case, `lcm(2, ord_l(p))` in the nonsplit case.
* `r = log_p #μ_{p^∞}(K_w)`: `r = 0` for odd `p`; `r = 1` for `p = 2`.
* `logMuPaper = (1 + [p=2] − 1/e − r/n)·log p` (`Mzk1PaperNormMuActual.logMuPaper`).

**For the CHAIN2 context (`l = 5`, `c = (l+4)(l−3)/(24l) = 0.15`):**

| bad p (p∤5) | e | n | r | logMuPaper |
|---|---|---|---|---|
| p = 2 | 1 | ord₅(2) = 4 | 1 | (2 − 1 − 1/4)·log 2 = (3/4)log 2 = 0.5199 |
| p = 11 | 1 | ord₅(11) = 1 | 0 | (1 − 1 − 0)·log 11 = 0 |

`p = 5 = l` is **not** a bad prime with `p ∤ l`; it is the `p=l` (special) case below.

## 1. Definitions and green references

* paper normalization (ROUTES §6.1, line 71):
  `vol(log O^×) = 1/(q_k·p^r)`, `q_k = p^f`, `p^r = #μ_{p^∞}`;
  `μ(𝓘_v) = (1 + [p=2] − 1/e − r/n)·log p`, normalized by `n = [k:ℚ_p]`.
* `e` = ramification index of `K_w/ℚ_p`; `n = [K_w:ℚ_p] = e·f`; `r = log_p #μ_{p^∞}(K_w)`.
* Green: `Mzk1PaperNormMuActual.paperMuCoeff/logMuPaper/logMuPaper_eq`;
  `Mzk1LocalVolumeAssemblyActual.logMuPaper/tameShellExponent` (L1/L2);
  `Mzk1ThetaCancelActual.logMuPaper_11_eq_zero`, `candidate_sum_nonneg`;
  `Mzk1P2DeficitActual.logMuPaper_2_r1_eq_zero`.
* Source: `Iut/Cor312/ThetaData/Basic.lean` (`K` = `prime.torsionField`, `qOrder`);
  `Iut/Concrete/LocalConstruct/LocalLogShell.lean` (`logShell`);
  `Iut/Concrete/LocalConstruct/Volume.lean` (`componentVol`).

## 2. Why `e = 1` at `p ∤ l` (multiplicative reduction)

Multiplicative reduction: `E(ℚ̄_p) = ℚ̄_p*/q^ℤ` with `q ∈ ℚ_p^*` (`qOrder`).
Since `p ∤ l`, inertia acts trivially on `q` and on `μ_l ⊂ ℚ̄_p`
(the `l`-cyclotomic extension is unramified at `p`), hence trivially on `E[l]`.
So `K_w/ℚ_p` is unramified: `e = 1`, `n = f`.

## 3. `r` at `p ∤ l` (p-power roots of unity)

`K_w/ℚ_p` unramified.  For odd `p`, `ℚ_p` has no nontrivial `p`-power roots of unity
and neither does its unramified extension, so `#μ_{p^∞} = 1`, `r = 0`.
For `p = 2`, `μ_{2^∞}(ℚ_2) = {±1}` and unramified extensions keep `±1`, so
`#μ_{2^∞} = 2 = 2^1`, `r = 1`.

## 4. `n` via Frobenius (examples)

Split multiplicative reduction: Frobenius acts on `E[l]` by `p` (or `p^{-1}`) on the
1-dim `μ_l` and by 1 on the quotient, so `f = ord_l(p)`.  Nonsplit: replace `p` by `-p`,
`f = lcm(2, ord_l(p))`.  Examples:

| l | p | ord_l(p) | (e,n,r) | logMuPaper |
|---|---|---|---|---|
| 5 | 2 | 4 | (1,4,1) | (3/4)log 2 |
| 5 | 11 | 1 | (1,1,0) | 0 |
| 11 | 2 | 10 | (1,10,1) | (9/10)log 2 |
| 11 | 5 | 5 | (1,5,0) | 0 |
| 11 | 11 is p=l (special) | — | (10,10,1) | (4/5)log 11 = 1.9183 |
| 5 | 5 is p=l (special) | — | (4,4,1) | (1/2)log 5 = 0.8047 |

## 5. Adjudication of the p=11 ambiguity

The CHAIN2-RESULTS table uses `p=11, e=10, r=1, n=10`, which is the **`p = l = 11`**
special case `K_w = ℚ_11(ζ_11)` (fully ramified, `e=n=10`, `μ_11 ⊂ K_w`, `r=1`),
giving `logMuPaper = (1 − 1/10 − 1/10)log 11 = (4/5)log 11 = 1.9183`.

But CHAIN2's numerical model uses **`l = 5`** (`c = 0.15 = (l+4)(l−3)/(24l)`), so
`p = 11` is a bad prime with `p ∤ l`; the correct data are
**`(e,n,r) = (1,1,0)`**, `logMuPaper = 0`.
The `(10,1,10)` row is therefore a **category error for the l=5 context**: it silently
uses the `p=l` normalization while the rest of the model uses `l=5`.

Consequences for the p=11 CHAIN2 window (`V_req = 0.46365`, `U = 5.9947`, `log11 = 2.3979`):
`V_shell(t) = 0 − t·log11`.  `t=0` gives `0 < V_req` (fails); `t=-1` gives `2.3979 ∈ [V_req,U]`
(survives); `t=-2` gives `4.7958` (survives); `t=-3` gives `7.1937 > U`.  So the integer window
becomes `t ∈ {−2,−1}` (not `{−1,0}`): the correct p=11 local data shifts the middle case.

## 6. What remains external

* The split/nonsplit alternative for the specific Frey curve (affects `n = f`, not `e` or `r`);
* the actual Frobenius eigenvalue (needed to fix `f=ord_l(p)` vs `lcm(2,ord_l(p))`);
* for `p = l`, the identification `K_w = ℚ_l(ζ_l)` and `e=n=l−1, r=1` (paper's local
  cyclotomic computation; green shape only).

**Bottom line:** for a multiplicative bad prime `p ∤ l`, `(e,n,r) = (1, f, [p=2])` with
`f = ord_l(p)` (split) or `lcm(2,ord_l(p))` (nonsplit); `r = 0` for odd p and `r = 1` for p=2.
For l=5: p=2 → (1,4,1), logMu=(3/4)log2; p=11 → (1,1,0), logMu=0.  The `(10,1,10)`
p=11 data are the p=l=11 special case, not a p∤l bad prime.
