# C9 corridor：b=3 B=I 与 h_inf ≥ −S3

任务：direct work（no board task）。日期：2026-10-25。owner：iplsheapt。短定理/证明；不改 Lean/Project/目标；不引入 arbitrary point/radius；只写本文件。

## 0. Verdict

在 `kappa=e v_p(Tr(y1))-v_pi(y1) ∈ [1,40]` 的 conditional B=I 分支（C9-NEW-BI-SOURCE Theorem 3.1），b=3 的精确式是

```
S3 = (12/41) log 12301 = 2.7563226845469613…;
F := Q_C - h_C = -S3 - h_inf;
F <= 0  ⇔  h_inf >= -S3.
```

本文件证明：

1. **若** `B_I ⊂ H_C,inf`，则 h_inf≥0，故 F≤−S3<0；这不是 counterexample，而是 **P6 holding**（h_C≥Q_C）在 corridor 内。IV 只给反向 upper container `H_C,inf ⊂ π^{j+1}B_I`，不给 B_I 的 lower inclusion。
2. **若** H_C,inf 含 global unit 的 unit region，product formula 给 h_inf≥0；含 global point x with `Σ α_p v_p(x)log p ≤ S3` 的 region，给 h_inf≥−S3。两者都 sufficient；但 source 没有 point-to-hull map。
3. **qUnit** 是 local finite object，不是 global unit；E[6] torsion 是 global 的但没有 source map 到 H_C,inf，且不是 global units；`i∈F` 是 global unit 但没有 map 到 H_C,inf。
4. **kappa 只决定 finite B branch**，不决定 h_inf；没有 source theorem 把 kappa 转为 archimedean lower bound。

Therefore：no target-compatible source proof of h_inf≥−S3. The corridor remains conditional/undecided; B_I inclusion/global unit would prove P6 in this corridor (not produce a counterexample).

## 1. Exact arithmetic and sign

Uniform profile F_mod=Q, single bad p=12301, e=41, b=3, conditional B=I:

```
h_fin = (9/41) log p,   Q_p = (-3/41) log p;
h_C = h_fin + h_inf;
F = Q_C - h_C = -(12/41)log p - h_inf = -S3 - h_inf.
S3=(12/41)log12301=2.7563226845469613….
```

Sign table:

```
h_inf > -S3:  F<0  => h_C>Q_C, P6 holds in this profile;
h_inf = -S3:  F=0  boundary;
h_inf < -S3:  F>0  => h_C<Q_C, would be counterexample corridor.
```

The desired lower bound `h_inf≥−S3` is exactly the **P6-holding** side of the corridor, not the counterexample side. This sign must be kept.

## 2. Conditional B=I from kappa

C9-NEW-BI-SOURCE Theorem 3.1 (source-conditional):

```
kappa <= 0:       H_A-full, B=O_K;
1 <= kappa <= 40: B=I (actual A=-I nonintegral; Sp-orbit spans I/J);
kappa >= 41:      branch B not well-posed inside I.
```

Thus assumption `kappa∈[1,40]` gives B=I **at the source-conditional level**. It gives the finite value `h_fin=9/41 logp`; it does **not** give h_inf and does not impose an archimedean bound. No equation in the source couples kappa to the archimedean radius/angle; the two are independent inputs.

## 3. Route A: B_I ⊂ H_C,inf

### 3.1 Conditional theorem

If the actual archimedean hull contains the unit ball B_I (at the appropriate level; see §3.2), then by B_I-zero normalization and monotonicity

```
H_C,inf ⊃ B_I  ⇒  h_inf ≥ logvol(B_I)=0  ⇒  F ≤ -S3 < 0.
```

So this route would prove P6 in the B=I b=3 corridor; it does not produce a counterexample.

### 3.2 Exact obstruction / type issue

At level j, H_C,inf lives in the tensor packet `π^{j+1}B_I`; `B_I` is a one-factor unit ball. The statement `B_I ⊂ H_C,inf` therefore needs a canonical level/diagonal/tensor embedding. The source supplies:

```
IV:  H_C,inf ⊂ π^{j+1} B_I    (upper container only);
B_I-zero: logvol(B_I)=0      (normalization, not inclusion).
```

It does **not** supply:

```
(BIH)  a canonical embedding of B_I into H_C,inf;
(BIH-lower) B_I ⊂ H_C,inf at the relevant tensor level.
```

Because π>1, `B_I⊂π^{j+1}B_I`; hence IV does not contradict (BIH), but also does not imply it. For j≥1, `B_I` is not literally a subset of the tensor packet without the missing embedding. This is the exact obstruction: **B_I-zero + IV give only the reference normalization and an upper container, not a lower hull inclusion**.

## 4. Route B: global unit / torsion

### 4.1 Product formula theorem

Let x be a global point and suppose its archimedean profile/region R_x is contained in H_C,inf with normalized volume at least `Σ_v α_v log|x|_v`. Then product formula gives

```
h_inf ≥ Σ_v|∞ α_v log|x|_v = -Σ_p α_p v_p(x) log p.       (PF)
```

If x is a global unit (v_p(x)=0 for all finite p), then h_inf≥0; if x has finite weighted valuation sum ≤S3, then h_inf≥−S3.

### 4.2 The three candidate points

| candidate | global? | unit? | map to H_C,inf? | result |
|---|---|---|---|---|
| qUnit | no (local q-pilot) | local unit | none | not applicable |
| E[6] torsion | yes over F | no (coordinates not units) | none | no PF bound |
| i∈F | yes | yes (all arch |i|=1) | none | no PF bound |
| p^{-1} / q-root | not constructed as global | non-unit | none | arbitrary |

Exact obstruction: H_C,inf is an archimedean tensor-packet possible-image set, not a subset of F or E_j(C). The source gives no canonical map

```
F^×, E_j(C), E[6](F), or qUnit  →  H_C,inf.
```

Without that map, the product formula cannot be applied. E[6] torsion being rational over F does not put it in the IUT hull; `i` being a global unit does not identify it with a hull point. Choosing any of them as a hull point would be arbitrary.

## 5. Route C: global point with controlled finite valuations

The sharp conditional criterion is

```
(GP)  ∃ global x and region R_x ⊂ H_C,inf with
      Σ_p α_p v_p(x) log p ≤ S3,
then h_inf ≥ -S3 and F≤0.
```

This is the only route that could give the exact threshold rather than the stronger h_inf≥0. But no canonical x is constructed: qUnit is local, E[6] finite valuations are not computed and not units, and p^{-1} is a local normalization step, not a source global point. The missing data are:

```
(GP1) a canonical global x (unit/torsion/controlled non-unit);
(GP2) its finite weighted valuation sum ≤S3;
(GP3) a source map/region R_x into H_C,inf.
```

## 6. Corridor theorem/dichotomy

**Theorem C3 (conditional corridor closure).** 在 conditional B=I、b=3、κ∈[1,40] 下，若下列任一成立：

```
(A) B_I ⊂ H_C,inf (level-appropriate);
(B) H_C,inf contains a global unit region;
(C) H_C,inf contains a global point region with finite valuation sum ≤S3;
```

则 `h_inf≥0`（A/B）或 `h_inf≥−S3`（C），故 `F≤0`，即在 b=3 B=I corridor 内 **P6 holds**。

Proof: §3/§4/§5 product formula, monotonicity, and the exact sign `F=−S3−h_inf`. QED

**Obstruction theorem.** 当前 source 不提供 A/B/C 中任一项：A 只有 upper IV container 和 B_I-zero normalization，缺 level embedding/lower inclusion；B 缺 F^×/E[6]/qUnit→H_C,inf map；C 缺 canonical x/valuation/map. 因此 h_inf≥−S3 **not proved**，corridor remains undecided.

Note: if B=I is not actual (kappa uncomputed), even proving A/B/C would only close a conditional profile, not all C. Conversely, without A/B/C there is no lower bound; h_inf could be below −S3 in another realization, so no counterexample is constructed either.

## 7. Proved / conditional / impossible

**Proved exact:**

- S3=(12/41)log12301=2.7563226845469613…;
- F=−S3−h_inf; sign table;
- conditional B=I from κ∈[1,40] (C9-NEW-BI-SOURCE Theorem 3.1);
- product-formula implication (PF);
- A/B/C ⇒ F≤0 in corridor;
- IV only gives H_C,inf⊂π^{j+1}B_I (upper), not lower B_I inclusion.

**Conditional / missing:**

- actual κ; actual B=I complete C;
- B_I⊂H_C,inf (level-appropriate);
- global unit/point-to-H_C,inf map and finite valuation sum;
- actual h_inf/H_C,inf; actual TC.

**Impossible / not allowed:**

- deriving h_inf≥−S3 from IV upper bound, B_I-zero, or kappa alone;
- treating qUnit as a global unit or E[6]/i as hull points without a map;
- arbitrary global point/p^{-1} or arbitrary r_v;
- claiming the corridor is a counterexample when h_inf≥−S3 (the sign is opposite: it is P6-holding).

## 8. Conclusion

The b=3 B=I + h_inf≥−S3 corridor is exactly the **P6-holding side** of the conditional B=I profile. A target-compatible lower bound would follow from B_I⊂H_C,inf (stronger h_inf≥0) or from a global unit/point in H_C,inf with controlled finite valuation (product formula). None is supplied by the current source: IV gives only an upper container, B_I-zero is only normalization, qUnit is local, E[6]/i have no map to H_C,inf, and kappa only decides the finite B branch. Therefore no h_inf≥−S3 theorem is obtained; the corridor remains conditional, and no counterexample follows. No arbitrary point/radius; no Lean/Project edits; P6 open.

