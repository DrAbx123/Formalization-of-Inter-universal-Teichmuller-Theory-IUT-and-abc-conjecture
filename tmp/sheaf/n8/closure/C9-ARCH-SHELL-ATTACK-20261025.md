# C9 attack：archimedean shell containment r_v ≤ π 与实际半径门槛

任务：task-166 / C9 attack（archimedean shell containment）。owner：iplsheapt。日期：2026-10-25。stage1 自然语言/精确算术；不改 Lean/Project，不改目标，不新增 arbitrary assumption。只写本文件。

输入：

- C9-ARCH-GLOBAL-20261025.md（task-156）；C9-ARCHIMEDEAN-20261025.md（task-150，SHA256 F4C7AFE112C238D7F5547461C1500AC45A73E49075BDDF366FE8B1E5A53E9957）；
- C9-GLOBAL-ASSEMBLY-CORRECTED-20261025.md（task-162；其中 D1/D2 使用 base 41 的半径需按本文件修正为 p=12301）；
- C9-SYMPLECTIC-SOURCE-20261025.md（task-147，SHA256 3F98F68A5E143DCD51ED6790B1C839AE7B8811E4E418D48B02E37E7C4D5B9C70）；C9-IND1-GLOBAL-20261025.md（task-149，SHA256 94785726EE890F6BC672861C570238F040636A6273A7722B2621949C48AF9AB8）。

前两条纠偏保持生效：TAME §2/§4–§6 的辛 donor、J=m、轨道生成、volume gain 是 inferred，不是 Kondo 定理；TAME (11)–(14) target containment 不是目标证明，需 TC-A..H/TC-S。finite deficit D 在本文件中仍标 conditional。

## 0. 结论（简版）

1. **不能证明 `r_v≤π`**。`I_v={|a|≤π}` 是**单个 archimedean factor**的 log-shell；Θ-pilot 在 level j 是 `j+1` 个 factor 的 tensor packet。IUT IV Prop1.5(iii)(iv) 的实际容器是 `π^{j+1}B_I`，因此 source-level 的半径上界是 `π^{j+1}`，不是 `π`。`r_v≤π` 若成立是额外的强假设，不能由 source shell 直接推出。
2. 因而不应从 `r_v≤π` 推出 `h_inf≤0`，更不能用它作为 arch-only 补偿不可能的证明。`h_inf=0` 也没有被假定。
3. 即使不使用 `r_v≤π`，IUT IV Thm1.10(vii) 的**最大 source container** 也给出 archimedean 上界

   `h_inf(C) ≤ (l+5)/4 · logπ ≈ 13.164394`（natural log），

   它与 p、q-exponent b 无关（只依赖 l）。对 conditional finite deficit，b=3、e=41、p≥43 的 natural deficit 至少为 `(408/41)log p ≥ (408/41)log43 ≈37.43`，已大于 13.16；b=273 更大。因此在该 conditional profile 中，**即使取最大 tensor-shell 容器，archimedean-only 也不可能补偿**；这比 `r≤π` 更强，且只要 finite D 被接受即可。
4. `r_v≤π` 的**实际**真假仍缺完整 C 的 archimedean hull 半径；本文件给出正确半径机制与精确必要门槛，不伪造 actual 半径。
5. 精确半径门槛是 `r_inf ≥ π p^{d_p}`（F=Q、单 bad p、`d_p=D_p^Sp/log p`），不是 `π e^{d_p}`。C9-ARCH-GLOBAL A17/A18/A19 和 task-162 的 D1/D2 的 base 41 版本必须按下式修正。
6. 数值：b=3 `d_p=408/41`，`r_inf ≥ π·12301^{408/41} ≈1.574146e41`；b=273 `d_p=38883/41`，`log10(r_inf/π)≈3878.7598`，`log10 r_inf≈3879.2570`。

## 1. 源 shell、tensor packet 与实际半径

### 1.1 单 factor 的 archimedean shell

IUT III Remark1.2.2(ii)（PDF p.36）在复 archimedean 域定义

```
I_v = { a ∈ F_v : |a|_v ≤ π }.
```

III Def1.1(ii)/(vii)、Prop1.2(iii)(v) 给出 angular/radial log-volume 与 log-link 的相容性；AbsTopIII Prop5.7(ii)/Cor5.10(ii) 给出实际 archimedean log-volume；AbsTopIII §I3 还把 archimedean `log(O_k^×)` 的 universal cover 描述为 “canonical rigid line segment of length 2π”。这些是 shell 的 per-factor 数据，不是整个 tensor packet 的半径。

### 1.2 tensor packet 的真实 container

Θ-pilot 在 level j 是 `|I|=j+1` 个 archimedean factor 的 tensor packet。IV Prop1.5(iii)(iv)：若每个 factor 的长度 ≤π，则 tensor product 落在

```
π^{j+1} · B_I ⊆ M_I,   B_I 是各 direct-summand unit ball；
```

IV Thm1.10(vii) 取 normalization 使 `log-volume(B_I)=0`，得到容器 log-volume `(j+1)logπ`。因此：

- `I_v` 只给 `r_v≤π`（单 factor）；
- 全 packet/hull 的 source 上界是 `r_v≤π^{j+1}`（按 tensor component）；
- 说整个 hull 满足 `r_v≤π` 等于额外假设所有 packet factor 的乘积半径不超过 π，source 不提供。

`π^{j+1}` 是**上界**，不是 attained radius；完整 C 的实际值仍要计算。task-166 要的 “prove or disprove” 在这里的正确结论是：**`r_v≤π` 不是 source theorem；把它当作普适 containment 是 invalid**。没有 actual complete C 时，不能给 actual `r_v>π` 反例，但也不能用 `r≤π` 去证明 h_inf≤0。

## 2. 从 source 最大 container 能得到什么

IV Thm1.10(vii) 的 container 对全部 possible images 取，故任何 actual archimedean output hull 都在其中；结合 IV Thm1.10(vii) 的 procession average：

```
h_inf(C) ≤ A_arc := ((l+5)/4) log π.
```

l=41 时 `A_arc=11.5·logπ≈13.164394` natural。注意这是 **natural log**；C9 的 finite deficit 表以 `log p` 为单位，比较时必须乘以 `log p`。

### 2.1 与 finite deficit 的比较

conditional uniform profile，e=41，单 bad p，F=Q：

```
D_p^Sp/log p = 408/41  (b=3),   38883/41 (b=273),   191928/41 (b=1347);
D_p^Sp = (D_p^Sp/log p)·log p   (natural).
```

对 b=3，`p>e+1=42`，`log p ≥ log 43`：

```
D_p^Sp ≥ (408/41)log43 ≈37.43 natural > A_arc≈13.16.
```

b=273/1347 的 deficit 更大。因此 **source maximum container** 已不足以补偿这些 finite deficit；arch-only 失败，且无需 `r_v≤π`。这个比较的 finite 侧仍是 conditional（task-147/149），但 arch 上界是 donor-independent 的。

### 2.2 若仅用 per-factor shell r≤π

若额外假设 `r_v≤π`，则 `h_inf≤0`，arch-only 更不可能补偿正 D；但该假设未被 source 证明，且与 tensor container `π^{j+1}` 的自然读法冲突。因此不能把它作为“已证 shell containment”；只能作为一个**更强的条件分支**。

## 3. 实际半径机制与精确门槛

对 F=Q（一个实 archimedean place，`α_inf=1`），C9-ARCH-GLOBAL 的径向读出是

```
h_inf(C) = log(r_inf/π),   r_inf = sup{|x| : x ∈ H_C,inf}.
```

若 finite residual 为 `D_C^Sp`（natural），补偿条件是

```
h_inf ≥ D_C^Sp   ⇔   r_inf ≥ π exp(D_C^Sp).
```

单 bad p 时 `D_C^Sp = d_p log p`，其中 `d_p=D_p^Sp/log p` 是有理数（log p 单位），所以

```
r_inf ≥ π p^{d_p}.                                  (R)
```

这是本任务要求的精确门槛；**base 是 p，不是 e=41**。

### 3.1 b=3 的精确数值

`p=12301`，`d_3=408/41`：

```
r_inf ≥ π · 12301^{408/41}
      = π · exp((408/41)log 12301)
      = exp(logπ + (408/41)log 12301)
log10(r_inf) = log10π + (408/41)log10 12301
             ≈ 0.4971499 + 9.9512195·4.0899404
             ≈ 41.1970448
r_inf ≈ 1.574146e41.
```

（`log10(r_inf/π)=40.6998949`；`r_inf/π≈5.011e40`。）

### 3.2 b=273 的精确数值

`d_273=38883/41`：

```
r_inf ≥ π · 12301^{38883/41};
log10(r_inf/π) = (38883/41)·log10 12301 ≈ 3878.7598364;
log10(r_inf) = 3878.7598364 + 0.4971499 ≈ 3879.2569863.
```

注意常见简写 “log10 ~3878.76” 是 `log10(r/π)`；半径本身还要加 `log10π≈0.49715`，即 `log10 r≈3879.257`。

### 3.3 b=1347

uniform rho=1：`d=191928/41`，`r_inf≥π·12301^{191928/41}`，巨大；rho=1/2 的 b=1347 direct-domain gap 已为负（lower bound 已高于 Q_p），不需要 arch 补偿；b=3 rho=1/2 direct-domain 仍有正 deficit，其 `d=4930615951/429916160≈11.468`，所需半径同式 `π p^{d}`（conditional）。

## 4. 对 C9-ARCH-GLOBAL A18/A19 与 task-162 D1/D2 的纠错

C9-ARCH-GLOBAL A14 定义 `D_C^Sp=Σα_p D_p^Sp log p`（natural），A17 的 `log(r/π)≥D_C` 正确；但 A18/A19 把 `D_p^Sp=408/41`（log p 单位）直接当成 natural exponent，写成 `π exp(408/41)≈65903.669`。这相当于把 base 取成 e/41，而不是 p，**错误地低估了半径**。task-162 的 D1/D2 使用 `41^{d_p}` 也仍是 base 41，而不是 p=12301；应统一为 (R)。

正确替换：

```
A18: r_inf ≥ π·12301^{408/41} ≈1.574146e41;
A19: r_inf ≥ π·12301^{38883/41}, log10(r/π)≈3878.7598;
D1/D2: r_inf ≥ π·p^{d_p}, p=12301.
```

只有 `F_mod=Q` 且 `p` 确为 12301 时才用该数值；一般 p 保留 `π p^{d_p}`。同时保留 conditional 标记：这些半径是在 finite D 被接受时的必要条件，不是实际 attained radius。

## 5. Shell containment 分支的准确状态

### 5.1 不能证明 r_v≤π

source 只给 `I_v` 的单 factor 半径 π 和 tensor container `π^{j+1}B_I`；没有定理把完整 C 的 archimedean hull 限制在 `I_v`。`r_v≤π` 是一个额外条件，不是 IV Thm1.10(vii) 的结论。

### 5.2 也不能用 r_v≤π 去杀 arch-only

因为 (i) 该 containment 未证；(ii) 即使没有它，最大 source container 上界 A_arc 已使 b=3/273 的 arch-only 不足（conditional finite D）。所以正确攻击结果是：**archimedean-only 补偿在 source-max 层已被排除于这些 profile，而不依赖 r≤π**。

### 5.3 实际半径仍缺

要给出 actual `r_v` 或 actual `r_v>π`，需要完整 C 的实际 archimedean output hull 和 angular 项；当前没有完整 C，故不能给 actual counterexample。任何把 `r_v` 设为 π、1 或 0 的做法都是 arbitrary，均禁止。

## 6. 剩余 gap / 下一步

1. **实际完整 C 的 archimedean hull**：计算实际 `r_v`/angular 区域；不是只取 container。
2. **确认 shell containment**：若是 source theorem，需给出 `H_C,inf⊆I_v` 的源级证明；若是 extra assumption，需明确标为条件，不能用于全局结论。
3. **finite D 的 corrected donor/TC 条件**：task-147/task-149 未完成前，D 仍 conditional。
4. **半径门槛**：在 F=Q、单 bad p、conditional D 下，必要门槛为 `r_inf≥π p^{d_p}`；b=3 ~1.57e41，b=273 log10(r/π)~3878.76。
5. **angular 项**：非径向 hull 还有 h_ang，不能把 (A3) 的径向公式当作全读出。

## 7. 结论

- 不能证明 `r_v≤π`；source-level 的实际容器是 `π^{j+1}B_I`，不是单 factor shell。
- `h_inf≤0` 不能由 source shell containment 推出；`h_inf=0` 也没有被假定。
- 但最大 source container 的 arch 上界 `((l+5)/4)logπ≈13.164` natural 已小于 b=3/e=41/p≥43 的 conditional finite deficit `≥37.43`，b=273 更大；因此 arch-only 补偿在这些 profile 中不成立，且不需要 `r≤π`。
- 正确精确门槛：`r_inf≥π p^{d_p}`；C9-ARCH-GLOBAL A18/A19 与 task-162 D1/D2 的 base 41 写法应修正为 p=12301。
- 实际 r_v 仍缺，P6 open；target_accepted=false。

## 8. 引用与状态

- IUT III Rmk1.2.2(ii) p.36: `I_v={|a|≤π}`；Def1.1(ii)/(vii)、Prop1.2(iii)(v): angular/radial log-volumes/log-link。
- IUT IV Prop1.5(iii)(iv): `π^{j+1}B_I`；Thm1.10(vii) pp.29–30: `log-volume(B_I)=0`, `(j+1)logπ`, procession bound `(l+5)/4 logπ`。
- AbsTopIII Prop5.7(ii)/Cor5.10(ii), §I3: archimedean log-shell/log-volume and canonical rigid segment length 2π; 转引自 task-156/ARCH，本文件未重证其内部细节。
- task-147/149 纠偏与 TC-A..H/TC-S；C9-ARCH-GLOBAL A14–A19；C9-GLOBAL-ASSEMBLY-CORRECTED C6/C7/D1/D2。

未运行 Lean/Project/kernel/comparator；没有独立审查；没有 global attack/counterexample。target_accepted=false，P6 open。

