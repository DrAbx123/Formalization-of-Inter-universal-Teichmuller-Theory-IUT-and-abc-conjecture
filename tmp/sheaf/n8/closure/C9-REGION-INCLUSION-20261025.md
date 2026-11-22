# C9 region inclusion：R_A (B=O_K) ⊂ R_B (B=I)?

任务：task-291（Prove B=O_K region contained in B=I hull）。owner：iplsheapt。日期：2026-10-25。短定理/证明；不改 Lean/Project/目标；不引入 arbitrary region；只写本文件。

输入：C9-TAME-LOG-DOMAIN-20261025.md §6（L_A/L_B/ν_A/ν_B）；C9-NEW-BI-SOURCE-20261025.md（B 分支）；C9-TC-EQUALITY-20261025.md（C1 lower）；C9-B273-ADMISSIBILITY/EXCLUSION；C9-B273-BPS-EXCLUSION。

## 0. Verdict

**Inclusion 成立（r≥2 且 strict；r=1 equality）。** 对 C9 all-bad r-tuple，TAME §6 的 row lattices

```
L_A = Σ_i p^s π_i D_r        (B=O_K branch),
L_B = p^{s-r+1} J^{⊗r}       (B=I branch),   J=πO_K,
D_r = O_K^{⊗r}
```

满足

```
L_A ⊂ L_B,   hence R_A=Hull(L_A) ⊂ R_B=Hull(L_B).
```

Proof 见 §1；r=1 时 equality，r≥2 时 strict，and

```
ν_A/log p = -s - 1/e,   ν_B/log p = -s + (r-1) - r/e,
ν_B-ν_A = (r-1)(1-1/e) > 0.
```

**Consequence for b=273:** inclusion proves B=I row hull is the **maximal** of the two row hulls, so any target upper envelope consisting of these row hulls reduces to B=I. If one additionally has the target-upper row-saturation `H_C⊂Hull(L_B)` (not merely TC-B lower saturation), then for b=273

```
h_C ≤ H_B + h_inf ≤ H_B + A_proc;
F=Q_C-h_C ≥ D_B - A_proc = 8821.538890956… >0,
```

which is the b=273 counterexample/upper-side repair. **Inclusion alone does not give this upper bound**; TC-B is a lower/saturation statement and full target possible images may be larger. The exact obstruction to using the inclusion for the upper side is the missing target-upper row-saturation `H_C⊂Hull(L_B)` / TC-C-upper. No arbitrary region is added.

## 1. Lattice inclusion proof

For each i, `p/π_i ∈ O_{K_i}` because `π_i^e=p u_i`, `u_i∈Z_p^×`, so

```
p/π_i = π_i^{e-1} u_i^{−1}  ∈ O_{K_i}.
```

Let `e_i` be the generator `p^s π_i D_r` of L_A (π_i in the i-th tensor factor, the unit in the other factors). The corresponding generator of L_B is

```
b = p^{s-r+1} π_1⋯π_r  (tensor unit).
```

Multiplying b by `∏_{j≠i}(p/π_j) ∈ D_r`:

```
b · ∏_{j≠i}(p/π_j)
 = p^{s-r+1} π_i ∏_{j≠i}(π_j·p/π_j)
 = p^{s-r+1} π_i p^{r-1}
 = p^s π_i = e_i.
```

Thus every generator e_i of L_A lies in L_B; since L_B is a lattice and L_A is its generated span, `L_A⊂L_B`. For r=1 the coefficient product is empty; both are `p^s π_i O` (equality). For r≥2 the coefficient `∏ p/π_j` is integral but has positive p-adic/π-adic content; the inclusion is strict (e.g. `b=p^{s-r+1}π_1⋯π_r` is in L_B but not in L_A: its per-factor π-valuation is one in every factor, while L_A generators have π-valuation one in only one factor). QED

## 2. Hull inclusion and volumes

The linear/tensor hull is monotone under lattice inclusion (taking the same tensor order and normalization):

```
L_A⊂L_B  =>  R_A=Hull(L_A)⊂Hull(L_B)=R_B.
```

From TAME §6 (17):

```
ν_A/logp = -s - 1/e;
ν_B/logp = -s + (r-1) - r/e;
ν_B-ν_A = (r-1)(1-1/e).
```

For e=41, r=j+1≥2, the difference is positive; at r=1 both values coincide. Thus B=I row hull is strictly larger than B=O_K row hull for every r≥2.

## 3. b=273 upper side

The b=273 C1 lower baseline uses B=O_K/B=I finite values, but the row hulls are

```
R_A (B=O_K) ⊂ R_B (B=I)   (this file).
```

If the target possible-image family is **contained in the union of these two row hulls** and includes the B=I branch, then its hull is `R_B` (because R_A⊂R_B); upper

```
h_C ≤ H_B + h_inf ≤ H_B + A_proc.
```

Then

```
F=Q_C-h_C ≥ Q_C-H_B-A_proc
  = D_B - A_proc
  = (38463/41)log12301 - 11.5logπ
  = 8834.703284644… - 13.164393687…
  = 8821.538890956… >0.
```

So under the target-upper row-saturation `H_C⊂R_B + arch`, b=273 gives F>0; the b=273 no-go/upper side would be repaired. For b=O_K branch alone, inclusion says its row hull is contained in B=I; if the target upper envelope is B=I, the same B=I value applies.

### Exact obstruction

Inclusion `R_A⊂R_B` only says B=I hull **contains** B=O_K hull. It does **not** prove `H_C⊂R_B`: TC-B says H_C is the hull of the full possible-image family, which may contain additional regions/other branches; saturation is a lower-bound object. Without an upper/row-saturation theorem `H_C⊂R_B`, one cannot conclude `h_C≤H_B+h_inf`; C1 remains only `h_C≥...`. This is the same TC-C-upper gap (task-266), not removed by the inclusion.

The inclusion therefore **proves the row-hull ordering** and reduces the **upper envelope of the two B branches** to B=I, but does not by itself repair the b=273 upper bound. An additional source theorem `H_C⊂R_B` (or an exact target volume equality) is required; without it, the b=273 counterexample remains conditional/missing.

## 4. Proved / conditional / obstruction

Proved exact:

- `L_A⊂L_B` for all r≥1, strict for r≥2; proof via `p/π_i∈O`;
- `R_A⊂R_B`;
- `ν_B-ν_A=(r-1)(1-1/e)>0`; r=1 equality;
- B=I is the maximal row hull of the two branches.

Conditional:

- target possible-image family contained in union of B=O_K/B=I row hulls;
- target-upper row-saturation `H_C⊂R_B + arch` / TC-C-upper;
- actual B branch, CFTH/TC, complete C;
- b=273 counterexample under these.

Obstruction:

- TC-B gives only lower/saturation; no upper `H_C⊂R_B`;
- unknown additional possible images may enlarge H_C beyond row hulls;
- without upper, b=273 F>0 not proved; inclusion alone insufficient.

## 5. Conclusion

**Inclusion R_A⊂R_B is proved** from the TAME row lattices; B=I row hull strictly contains B=O_K for r≥2 and has larger normalized volume by `(r-1)(1-1/e)`. This is a genuine row-hull ordering and reduces the **upper envelope of the two B branches** to B=I. However, it does not prove the target hull is contained in R_B: TC-B is lower-bound only. Under the extra target-upper row-saturation `H_C⊂R_B+A`, b=273 yields `F≥D_B-A_proc=8821.538891>0`; without it, the b=273 upper side remains blocked by the missing TC-C-upper theorem. No arbitrary region; no Lean/Project edits; P6 open.

