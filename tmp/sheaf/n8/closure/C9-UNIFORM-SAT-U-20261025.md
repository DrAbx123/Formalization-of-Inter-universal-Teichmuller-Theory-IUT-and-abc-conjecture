# C9 uniform SAT-U：H_C ≤ R_B+arch

任务：task-319（Uniform SAT-U proof: H_C subset R_B+arch）。owner：iplsheapt。日期：2026-10-25。短定理/证明或 exact obstruction；不改 Lean/Project/目标；不引入 arbitrary region；只写本文件。Mixed profiles are E3 excluded。

输入：C9-TAME-LOG-DOMAIN-20261025.md §6（row classification 及其 scope disclaimer）；C9-RA-SUBSET-RB/REGION-INCLUSION（R_A⊂R_B）；C9-TARGET-UPPER-SAT（task-301）；C9-SATURATION-MAXIMALITY（task-300）；C9-UNIFORM/BC 文件；C9-ARCH-HULL。

## 0. Verdict

**U_uniform 没有证明；得到 exact obstruction 和一个 conditional row-saturation theorem。** Uniform scope 排除了 mixed profiles（E3、not actual），也给出 good finite volume=0/非正的 source-level 解释；但 target H_C 的 finite bad part 是否**恰好**由 B=O_K/B=I row hulls 生成，仍缺 source theorem。TAME §6 只分类 actual subfamily（Gaussian 整数区域、per-factor Γ、factor permutations），并明确声明它不是整个 C 的 log/Θ/∞ output family 的上界；full Ind1/Ind2/Ind3/Theta-log possible images 未被纳入。

因此：

```
(UNIF-ROW)  finite bad row subfamily 由 R_A/R_B 生成;   TRUE/conditional;
(UNIF-BAD)  full finite bad target H_C equals row hull;     NOT PROVED;
(U_uniform) h_C <= H_B + h_inf;                            NOT PROVED.
```

**Row j=1 check（§1.5）：** j=1 的 `nu_B,1` 确实大于 average `H_B`（b=3 39/41>9/41；b=273 -207/41>-38736/41），但 binding 的 procession normalization 是 label average，不是 max/sup；因此 row j=1 不 refute U_uniform，max 读法是另一种 normalization。

若额外假设 `U_bad⊂Hull(R_A∪R_B)` 且 good finite volume≤0、arch component 为 h_inf，则 U_uniform 成立，b=273 给 F≥8821.538。当前没有 source-valid uniform extra region；也没有 proof of the missing upper；所以 obstruction 是**缺少 source theorem**，不是 b=273 的 arithmetic defect。

## 1. Conditional row-saturation theorem

Let `U_bad` be the finite bad possible-image family of the fixed F_mod=Q uniform rho=1 C. TAME §6 classifies the actual subfamily

```
U_bad^row ⊂ Hull(R_A∪R_B)=R_B   (since R_A⊂R_B, task-291).
```

Assume the two missing target-upper conditions:

```
(G1) U_bad ⊂ R_B   (full finite bad possible-image family, not only the row subfamily);
(G2) good finite possible-image contributions have normalized volume <=0;
(G3) the archimedean component is h_inf (already the definition of the readout).
```

Then

```
h_C = h_bad + h_good + h_inf <= H_B + 0 + h_inf = H_B + h_inf.
```

**Theorem U_uniform-cond.** Under (G1)-(G3), `h_C≤H_B+h_inf`; with `h_inf≤A_proc=13.164393687`,

```
h_C <= H_B+A_proc = (-38736/41)log12301 + A_proc = -8884.245232030…,
Q_p = (-273/41)log12301 = -62.706341073…,
F=Q_p-h_C >= 8821.538890956… >0.
```

This is the b=273 uniform counterexample under U_uniform-cond. It is **conditional on (G1)**, not a source theorem.

## 1.5 Average vs max：row j=1 是否 refute U_uniform

这是 task-319 的关键 normalization check。C6-STAGE1 §1.5 明确：paper 的 **procession-normalized log-volume 是 label set `j in F_l^*` 上的 average**，带 III Rmk3.1.1(ii) 的 normalized weights；C9-BI-REGION-CONSTRUCTION (3.1)-(3.2) 把 uniform row family 定义为 `R_B=union_j T(R_B,j)`，weight `1/m`，并得到

```
H_B/logp = (1/m) sum_{j=1}^m [-s_j+j-(j+1)/41] = 9/41  (b=3);
H_B/logp = -38736/41  (b=273).
```

The row values at j=1 are larger:

```
b=3:   nu_B,1/logp = 39/41 = 0.951219512… > H_B/logp = 9/41 = 0.219512195…;
b=273: nu_B,1/logp = -s_1+1-2/41 = -6+1-2/41 = -207/41 = -5.048780488…
       > H_B/logp = -38736/41 = -944.780487805… .
```

**Resolution: the target finite readout is the weighted average H_B, not max/sup over rows.** A single row j=1 is a possible-image component, but under the procession normalization it enters with weight `1/m=1/20`; it does not impose `h_C>=nu_B,1`. The other b=273 rows are strongly negative (e.g. j=20: `nu_B,20=-2663+20-21/41=-108384/41≈-2643.512…`), so the average is `-944.7805`. If one instead defined `h_C` as max/sup over rows, U_uniform would fail; for b=273 `h_C>=nu_B,1≈-5.0488`, and P6 would hold whenever `h_inf>=Q-nu_B,1=-66/41≈-1.6098` (not the F>=8821 counterexample). But max/sup is **not** the binding C9/III procession normalization; it is a different normalization (profile/normalization change, analogous E3) and is not used.

The row j=1 check therefore does **not** refute U_uniform; it confirms that H_B must be read as the weighted-average row height. The remaining obstruction is still (G1): full finite bad target possible-image family beyond the row subfamily.

## 2. Good places and arch

Uniform rho=1 means every selected bad place is all-bad; mixed profiles are not possible images (E3). At a good finite place, the q-parameter is trivial/unit and the local possible-image integral hull is the reference unit structure; under B_I-zero, its normalized finite volume is 0. Thus good finite contributions do not add positive finite volume; if the actual target has a negative good contribution it only helps the upper. Arch is exactly the component h_inf; IV only gives the upper cap `h_inf≤A_proc`, not a new positive region. These two parts are consistent with (G2)/(G3) at source level.

## 3. Why (G1) is not available

TAME §6 says: the exact classification

```
L_A=Σ_i p^s π_i D_r,   L_B=p^{s-r+1}J^{⊗r}
```

is for the fixed all-bad r-tuple and only the listed actual subfamily (original Gaussian integer region, all per-factor Γ, factor permutations); its classification is **not an upper bound for the entire C's log/Theta/infinity output family**. It is a lower-bound/row classification. TC-B likewise says `H_C` is the hull of the full possible-image family, which is **larger** than the row subfamily; it does not give `H_C⊂R_B`.

Full Ind1 includes capsule-full poly-automorphisms, not only the per-factor Γ/factor permutations; Ind2/Ind3 and Theta/log/gluing can add possible images. TAME's saturation statement is inside the finite row type, not a global exhaustion theorem. Therefore (G1) is not proved. Uniform scope removes mixed profiles, but does not remove these other possible-image branches.

## 4. Exact obstruction / no uniform counterexample

No source-valid uniform `E_extra` outside `R_B` is constructed in the current corpus:

```
- other local types: not part of fixed uniform tame local type; shell volume nonpositive/unknown;
- good places: zero/nonpositive by G2;
- arch: already in R_B+arch;
- aggregate B=I / Theta-log / Ind3: possible branches but no volume computation or explicit region.
```

So U_uniform is neither proved nor refuted by a source-valid counterexample. The exact obstruction is the missing theorem

```
(G1) full finite bad possible-image family lies in the B=O_K/B=I row hull (equivalently,
     no positive finite bad target complement beyond R_B).
```

This is the same TC-C-upper/EQ1 gap as task-266/301, now specialized to the uniform profile.

## 5. Classification

| item | status |
|---|---|
| uniform rho=1, mixed profiles excluded | ACTUAL/scope |
| R_A⊂R_B (task-291) | PROVED |
| row subfamily R_A/R_B classification | conditional/source-level |
| good finite volume≤0 | source-level/conditional |
| arch h_inf component | definition/upper A_proc |
| (G1) full finite bad U_bad⊂R_B | NOT PROVED |
| U_uniform h_C≤H_B+h_inf | NOT PROVED |
| U_uniform-cond ⇒ b=273 F≥8821.538 | PROVED conditional |
| uniform source-valid E_extra | NOT CONSTRUCTED |

## 6. Conclusion

Uniform scope removes the mixed-profile E3 counterexample, and good/arch parts are consistent with the desired upper. But TAME §6 classifies only the actual all-bad row subfamily and explicitly disclaims the full C output upper; (G1) — full finite bad possible-image family contained in R_B — is missing. Therefore U_uniform is not proved. Under (G1), it implies `h_C≤H_B+h_inf` and b=273 `F≥8821.538`; without (G1), no uniform source-valid extra region is constructed and the obstruction is exact. No arbitrary region; no Lean/Project edits; P6 open.

