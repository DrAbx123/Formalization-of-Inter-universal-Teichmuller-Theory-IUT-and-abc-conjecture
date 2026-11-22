# C9 audit：anti-diagonal trace Gram for the actual Kondo y basis

任务：task-259（prove/disprove anti-diagonal trace Gram）。owner：iplsheapt。日期：2026-10-25。短审计/定理；不改 Lean/Project/目标；不引入 arbitrary normalization；只写本文件。

输入：Kondo 2025 source `Kondo-2512.09231v1.html`（Theorem 1.3, Theorem D/E, proof of Theorem 1.3）；Kondo 2026 source `Kondo-2605.25428v2.html`；C9-NEW-BI-SOURCE-20261025.md（kappa dichotomy）；C9-ADJUDICATE-HAFULL-20261025.md（W=ker Tr Q_p-hyperplane）。

## 0. Verdict

**The anti-diagonal Gram as stated for the actual Kondo y-basis is FALSE.**

Kondo Theorem 1.3 for d=41 (odd) gives

```
ker Tr = <y_2, y_3, ..., y_41>_{Q_p};
Tr(y_1) ≠ 0.
```

The proposed formula

```
beta(y_i,y_j)=Tr(y_i y_j)=41 p u  if i+j=43,  else 0
```

for `1≤i,j≤41` gives `beta(y_1,y_j)=0` for all `j` (there is no `j=42`), hence `y_1` is in the radical of beta. But `beta` is nondegenerate, contradiction. Thus the full-basis anti-diagonal Gram is **impossible**, independently of any reconstruction computation.

If the formula is intended only on `W=<y_2,...,y_41>` (indices 2..41), then it is a **possible but unproved normalization**: Kondo's Theorem 1.3 gives only the trace-kernel span, not the Gram matrix entries. The restricted anti-diagonal Gram also does **not** determine `kappa`: it says nothing about `y_1` beyond `Tr(y_1)≠0`, and `y_1=a p+l` can have `a` non-unit without changing any `W`-Gram entry. Thus it cannot decide `kappa∈[0,40]` or `B=O_K/B=I`.

## 1. Kondo indexing and nondegeneracy

Kondo Theorem 1.3 (odd d):

```
Ker(Tr_{k/k^{(d=1)}}) = <y_2,y_3,...,y_d>_{Q_p},  d=41.
```

Here `y_i` are images of the Jannsen-Wingberg generators `x_i`; the `y_i` form a Q_p-basis of `k_+` (Kondo proof uses `{y_1,...,y_d}`). The trace pairing

```
beta(x,y)=Tr(xy)
```

is symmetric nondegenerate (K a finite separable field extension of Q_p). `Tr(y_1)=41≠0` is a p-adic unit? At least nonzero; `Tr(y_1)∈pZ_p` under `y_i∈J` (C9 data).

For `d=41`, `W` has basis `y_2,...,y_41` (40 elements); `y_1` is outside W and has nonzero trace. The anti-diagonal index `i+j=43` pairs `(2,41),(3,40),...,(41,2)` — exactly the W-basis pairs if one identifies `y_i` with `π^{i-1}`. It is **not** a formula for the full Kondo basis including `y_1`.

## 2. Why the full-basis formula is false

Suppose the formula is asserted for all `i,j∈{1,...,41}`. Then

```
beta(y_1,y_j)=0  for every j=1,...,41
```

because `1+j=43` would require `j=42`, which is outside the basis. Hence `beta(y_1,∑ c_j y_j)=0` for every vector; `y_1` is in the radical. This contradicts nondegeneracy of beta. Equivalently, the matrix with `i+j=43` has an all-zero first row (and, symmetrically, first column); its determinant is0, while a Gram matrix of a nondegenerate form has nonzero determinant.

Therefore the original kappa theorem's displayed hypothesis, read literally on the actual Kondo y-basis, cannot hold.

## 3. Restricted W-version: what source does and does not say

If one restricts to `i,j=2,...,41`, the matrix

```
B_W(i,j)=41pu if i+j=43 else0
```

is symmetric, anti-diagonal, and nondegenerate on W (pairs `2↔41, 3↔40, ..., 41↔2`). It is a legitimate **possible** Gram matrix for a beta-dual basis of W. But:

1. Kondo Theorem 1.3 proves only `W=<y_2,...,y_41>`, not any pairing values `Tr(y_i y_j)`.
2. Kondo's proof of Theorem 1.3 extends `{y_3,...,y_d}` by an arbitrary vector `w=α_1 y_1+α_2 y_2`; the basis is not normalized by beta. Different admissible choices change the Gram matrix.
3. The generators `x_i` (hence `y_i`) are explicitly non-canonical (Kondo: generators/relations of Theorem D are non-canonical). A beta-dual normalization would be an extra source theorem, not a consequence.

So the restricted anti-diagonal Gram is **not proved**. It is also not excluded (it is one possible normalization); the exact missing source statement is

```
(GRAM-W)  beta(y_i,y_j)=41 p u·δ_{i+j,43}  for 2≤i,j≤41,
```

with a chosen primitive `u∈Z_p^×` and a chosen ordering. No such theorem appears in Kondo 2025/2026 or the current C9 source extracts.

## 4. What follows if one ASSUMES GRAM-W

Assume the restricted anti-diagonal Gram and the C9 data `y_i∈J`, `Tr(y_1)∈pZ_p`.

From the trace table for the π-power basis (or from the anti-diagonal dual basis),

```
J = Z_p p  ⊕  (J∩W),    W=ker Tr;
L := J∩W = Z_p-span(π,...,π^40).
```

Write `y_1=a p+l` with `a∈Z_p`, `l∈L`. Then

```
Tr(y_1)=a Tr(p)+Tr(l)=a·41p,   since l∈W;
```

and

```
v_pi(y_1)=min(41, v_pi(l))  (unless the two terms cancel);
kappa := e v_p(Tr(y_1))-v_pi(y_1)=41-v_pi(y_1)   if a∈Z_p^×.
```

If `a` is a unit and `l∈L` is primitive (`0≤v_pi(l)≤40`), then

```
kappa∈[0,40];   kappa=0 ⇔ l=0 or v_pi(l)=41?;
1≤kappa≤40 ⇔ y_1 has a nonzero L-component of valuation <41.
```

Then the C9-NEW-BI-SOURCE dichotomy would give B=O_K for kappa≤0 (here kappa=0) and B=I for 1≤kappa≤40. **But this range is not derived from GRAM-W alone**: if `a` is not a unit (e.g. `a∈pZ_p`), then `kappa` can be ≥41, and GRAM-W on W is unchanged. The missing extra hypothesis is `a∈Z_p^×`, equivalently `y_1` is primitive in `J/pJ` along the p-direction. Kondo's non-canonical generators do not supply this.

## 5. Exact obstruction to deciding kappa/B

The full Gram formula is **false** by nondegeneracy. The restricted W-Gram is unproved and, even if granted, leaves `a=v_p(Tr(y_1))-1` and `v_pi(l)` free. The exact missing inputs are:

```
(G1) a beta-dual normalization of y_2,...,y_41 (GRAM-W);
(G2) a primitivity/normalization of y_1: a∈Z_p^× in y_1=a p+l;
(G3) the actual v_pi(l), equivalently kappa=41-v_pi(y_1).
```

Without (G1)-(G3), the anti-diagonal Gram cannot decide whether kappa is in [0,40]. If (G2) fails, kappa can be outside [0,40] and the branch B is not well-posed inside I (C9-NEW-BI-SOURCE).

## 6. Classification

| item | status |
|---|---|
| Kondo odd-d kernel W=<y_2,...,y_41> | PROVED source |
| beta nondegenerate; Tr(y_1)≠0 | PROVED |
| full-basis anti-diagonal Gram i+j=43 | **FALSE** (y_1 row zero) |
| restricted W anti-diagonal Gram | **UNPROVED** possible normalization |
| GRAM-W ⇒ L=J∩W | conditional/derivable from lattice decomposition |
| GRAM-W + y_1 primitive ⇒ kappa=41-v_pi(y_1) | conditional |
| kappa∈[0,40] from source | **NOT DERIVED** |
| B=O_K/B=I decision | **NOT OBTAINED** |
| exact missing | G1/G2/G3 |

## 7. Conclusion

The anti-diagonal trace Gram **cannot be proved** for the actual Kondo y-basis as stated: the full-basis formula makes `y_1` a radical vector, contradicting nondegeneracy. The only defensible version is the restricted W-Gram, which is a possible beta-dual normalization but is not in Kondo 2025/2026; even granting it, `y_1` primitivity and `v_pi(y_1)` are missing, so the kappa range [0,40] and the B=O_K/I decision are not obtained. No arbitrary normalization is added; P6 open.

