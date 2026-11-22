# C9 审计：archimedean maximal-container bound 与 normalization/B_I critique

任务：task-172（audit arch maximal-container bound vs normalization critique）。owner：iplsheapt。日期：2026-10-25。stage1 独立自然语言/精确算术审计；不改 Lean/Project/目标；不新增 attack 命题；只写本文件。

审计输入：

- C9-ARCH-SHELL-ATTACK-20261025.md（task-166，SHA256 DCE3C07BB6739378CC34A0EB204CDFFC4080553D151E9F1BDCCEC72E78A93163）
- C9-AUDIT-ARCH-GLOBAL-20261025.md（task-163，SHA256 7D719850564C1550D9D525EBE01AE395FE2AE5D70214F21AA83293EC73154825）
- C9-AUDIT-LOG-ARCH-20261025.md（task-161，SHA256 F7AD81083A1772BF5A300B1B05886C28831B8BBE11BAB1B097C5A817C12547EC）
- C9-ARCHIMEDEAN-20261025.md（task-150，SHA256 F4C7AFE112C238D7F5547461C1500AC45A73E49075BDDF366FE8B1E5A53E9957）

前两条纠偏生效：task-147 corrected symplectic donor；task-149 (11)–(14)/target containment withdrawn，TC-A..H/TC-S 未证。finite deficit 在本文件中仍标 conditional。

状态：只读审计；无 Lean/Project/kernel/comparator/独立审查；P6 open；target_accepted=false。

## 0. 结论

1. **Task-166 的 maximal source container bound 是 paper-level valid 的**：IUT IV Prop1.5(iii)(iv)/Thm1.10(vii) 给实际容器 `π^{j+1}B_I` 且 `log-volume(B_I)=0`，所以 archimedean hull 的 normalized log-volume 至多 `(j+1)logπ`；procession average 为 `(l+5)/4 logπ`。这个 bound 不依赖 `h_inf=log(r/π)` 的 shell-pi convention，也不受 task-163 指出的 `d_v`/`log(r/π)` 公式不一致影响，因为它用的是 container volume，不是 local radial formula。
2. **与 conditional finite deficits 的比较是 arithmetic-valid 的，但 finite 侧 conditional**。A_arc≈13.164394 natural；b=3/e=41/p≥43 的 conditional deficit `(408/41)log p≥37.43` natural >13.164；b=273 为数千。故只要接受 task-147/task-149 的 finite D，archimedean-only 不足；这不是 original target 的证明。
3. **`r_v≤π`/`h_inf≤0` 只在 shell-pi normalization 下成立**。IV B_I=0 normalization 下 `h_inf` 不是 `log(r/π)` 而是 `log r`（up to local dimension convention）；`r≤π` 只给 `h_inf≤logπ>0`，不杀 compensation。Task-166 自己已声明 `r≤π` 不是 source theorem；但其 §2.2 的 “r≤π ⇒ h_inf≤0” 只能作为 shell-pi 条件，不能作为 paper-level B_I 结论。这一点按 task-163 修正。
4. **精确半径门槛是 normalization-dependent**：shell-pi 下 `r_inf≥π p^{d_p}`；IV B_I 下 `r_inf≥p^{d_p}`（无 π）。Task-166 的 `π p^{d_p}` 在 C7/shell-pi convention 下有效；但作为 paper-level 无前缀形式必须先固定 normalization。base-p 纠错（不是 e/41）仍然 valid。
5. **Task-163 的 b=273 branch 纠错本身有 branch-label error**：C9-UNIFORM 的 A=O_K 是 `-39156/41`，residual `38883/41`；B=I 是 `-38736/41`，residual `38463/41`。MODP natural alignment 条件性选 A=O_K。因此 task-166 用 `38883/41` 对 b=273 A 分支是正确的；task-163 说 `38883` 属于 h_A **不等于** “B=O_K 应为 38463”；38463 是 B=I。Task-163 的这句 label 错误需纠正。
6. Task-166 的 main result（max-container arch-only exclusion）survives；其 shell containment sign 和 π-factor radius 降为 normalization-conditional；其 `r_v`/actual radius 仍未构造。

## 1. Maximal container bound 的独立复核

### 1.1 Source formula

IV Prop1.5(iii)(iv)：对 `|I|=j+1` 个 archimedean factor，若每 factor 长度 ≤π，则

```
tensor ∈ π^{j+1} B_I,   B_I 是 direct-summand unit balls 的 direct product.
```

IV Thm1.10(vii) 的 normalization 令 `log-volume(B_I)=0`，故

```
log-volume(π^{j+1}B_I) = (j+1)logπ.                  (1)
```

实际 Θ-pilot possible images 的 union/hull 在 container 内（IV 的 all possible images 已含 Ind1/2；Ind3 用 upper bound），因此

```
h_inf(C) ≤ (j+1)logπ.                                (2)
```

对 `j=1..m` 取 procession average，`m=(l−1)/2`：

```
(1/m)Σ(j+1) = (m+3)/2 = (l+5)/4;
A_arc := ((l+5)/4)logπ.                             (3)
```

l=41: `A_arc=11.5·logπ=13.164393687...` natural。

### 1.2 为什么 task-163 的 normalization critique 不推翻 (3)

Task-163 正确指出：

- `h_v=d_v log(r/π)` 与 `h_inf=Σα_v log(r/π)` 有 d_v 不一致；
- 以 `I_v`(π) 为零 reference 与 IV `B_I=0` 不同；
- B_I 下 `r≤π` 给 `h_inf≤logπ` 而非 ≤0；
- `π p^{d_p}` 与 `p^{d_p}` 取决于 normalization。

这些反对的是 **task-166/ARCH 的 local radial formula 与 shell containment 结论**，不反对 (1)–(3)。(1)–(3) 直接使用 IV container volume，normalization 固定为 `B_I=0`；没有 `log(r/π)`，没有 local d_v 重复，没有 `r≤π` 假设。因此 maximal-container bound 仍是 paper-level valid；它是本审计要保留的 task-166 部分。

注意：若把 h_inf 定义为 shell-pi normalized `log(r/π)`，则 `r≤π^{j+1}` 只给 `h_inf≤j logπ`，比 (2) 更小；但 (2) 仍是其 upper bound（因为 `jlogπ≤(j+1)logπ`）。因此 (3) 在两个 normalization 下都可作为（可能 non-sharp）upper bound 使用。

## 2. 与 conditional finite deficits 的比较

finite residual 仍取 task-151/task-166 的 conditional notation：

```
D_p^Sp/log p = b(e+1)/12 − (b−1)/e − T_p,   T_p=(1/(e m))Σt_j.
D_C^Sp = Σ α_p D_p^Sp log p   (natural).
```

e=41 uniform ρ=1、B=O_K/A 分支（MODP natural alignment 下的 conditional actual branch）：

| b | D_p^Sp/log p | D_C^Sp natural |
|---:|---:|---:|
| 3 | 408/41 ≈9.951220 | (408/41)log p |
| 273 | 38883/41 ≈948.365854 | (38883/41)log p |
| 1347 | 191928/41 ≈4681.170732 | (191928/41)log p |

与 `A_arc=13.164394` 比较（p≥43）：

```
b=3:  (408/41)log43 ≈37.428528 > 13.164394;
b=273:(38883/41)log43 ≈3566.993758 > 13.164394;
b=1347:(191928/41)log43 ≈17606.819898 > 13.164394。
```

p=12301 时 b=3 为 `(408/41)log12301≈93.714971`。因此只要 conditional finite D 被接受，max-container arch 上界也不足以补 b=3/273；b=1347 更大。

重要：这个比较的 finite 侧依赖 task-147 corrected donor、basis alignment、J=m、orbit generation、target container/TC；不能把它写成 original target 的证明。Arch 侧 (3) 不依赖这些 donor，是 donor-independent 的 upper bound。

## 3. B_I vs shell-π 的 reconciliation

### 3.1 两个 normalization

Shell-pi convention：

```
h_inf = Σ α_v log(r_v/π);   r_v≤π ⇒ h_inf≤0;
F=Q: h_inf=log(r/π);  补偿需 r≥π p^{d_p} (D=d_p log p).
```

IV B_I=0 convention：

```
h_inf^B = Σ α_v log r_v (local dimension fixed by B_I);
r_v≤π ⇒ h_inf^B≤logπ (>0), NOT ≤0;
F=Q: h_inf^B=log r; 补偿需 r≥p^{d_p} (D=d_p log p).
```

两者不能混用。C9-ARCH-GLOBAL A2/A3 用 shell-pi；同文件又引用 IV `B_I=0`。Task-163 这个 critique 是正确的。

### 3.2 Task-166 哪些部分受影响

- **不受影响**：max-container bound (3)；dimension factor zero；base-p correction `π p^{d_p}` vs `π e^{d_p}` 中的 **p** 部分；arch-only insufficiency via (3)。
- **受影响/conditional**：`r≤π ⇒ h_inf≤0` 只在 shell-pi 下；B_I 下它变成 `≤logπ`，不排除 compensation。因此该 implication 只能标 shell-pi conditional，不能作为 B_I paper-level。
- **半径门槛**：`π p^{d_p}` 是 shell-pi；B_I 是 `p^{d_p}`。C7 若采用 shell-pi convention，则 task-166 的 π 因子正确；若采用 IV B_I，则 π 因子应去掉。C7 的 base `p` 纠错在两种 convention 下都 valid。
- **actual r_v**：仍未构造；两种 convention 都不能给 actual 数值。

### 3.3 b=273 branch label 的独立纠正

Task-163 声称 b=273 的 `38883/41` 是 h_A，而 “B=O_K/B=h_B 是 38463/41”。这句话的 label 错了：

```
C9-UNIFORM: A=O_K: h=-39156/41, D=38883/41;
            B=I:    h=-38736/41, D=38463/41;
MODP natural alignment: B=O_K (conditional).
```

所以 B=O_K/A 的 residual 是 **38883/41**，不是 38463/41；38463/41 属于 B=I（unproved）。Task-166 使用 38883/41 对 b=273 A 分支正确；其早期 C9-ARCH 文件用 `-38736/41` 作 h_p 的错误也已由 task-158 审计记录。Task-163 在这一点上应更正。

## 4. Task-166 的 survival 分类

| task-166 内容 | 分类 | 说明 |
|---|---|---|
| max-container `h_inf≤(l+5)/4 logπ` | VALID paper-level (conditional on IV container/actual hull inside) | 独立于 shell-pi，donor-independent |
| dimension factor zero | VALID | B_I=0，Prop1.5(iii) |
| arch-only insufficiency via max bound vs conditional finite D | CONDITIONAL arithmetic | finite D conditional task-147/149 |
| `r_v≤π` as source theorem | NOT PROVED / invalid as paper-level | source per-factor shell; tensor container π^{j+1} |
| `r≤π ⇒ h_inf≤0` | CONDITIONAL shell-pi only | B_I gives ≤logπ>0 |
| radius `π p^{d_p}` | CONDITIONAL normalization | shell-pi; B_I `p^{d_p}` |
| base p correction vs e/41 | VALID | 与 normalization 无关的 base |
| actual r_v | OPEN | 完整 C 未构造 |
| target h_C≥Q_C | NOT CLAIMED | TC-A..H/TC-S missing |

## 5. 精确数值表

l=41: `A_arc=11.5 logπ=13.164393687268102` natural；
`11.5 logπ/log43=3.500051...` log p units；`11.5 logπ/log12301=1.3978745...`。

Conditional natural finite deficits (A branch):

| b | p=43 | p=12301 |
|---:|---:|---:|
| 3 | 37.428528 | 93.714971 |
| 273 | 3566.993759 | 8931.174579 |
| 1347 | 17606.819898 | 44084.625017 |

（b=1347/p=43 的 `(191928/41)log43≈17606.819898`；p=12301 值 `≈44084.625017`。）

Radius thresholds：

- b=3: shell-pi `r≥π·12301^{408/41}`; log10 r≈41.197044769; r≈1.574145126e41. B_I `r≥12301^{408/41}`; log10 r≈40.699894896.
- b=273: shell-pi `log10(r/π)≈3878.759836402`, `log10 r≈3879.256986274`; B_I log10 r≈3878.759836402.
- b=1347: `log10(r/π)=d·log10p` huge; exact formula `π p^{191928/41}` (shell-pi) or `p^{...}` (B_I).

## 6. 剩余 gap / 结论

1. **Max-container bound valid**：`h_inf≤(l+5)/4 logπ` 作为 IV B_I container bound 通过；task-163 的 `log(r/π)`/`d_v` critique 不能推翻它。
2. **Arch-only exclusion conditional**：finite D 依赖 corrected donor/basis/target；在 conditional D 下 b=3/273 的 arch-only 不足成立。
3. **Shell containment branch**：`r≤π` 未证；且其 `h_inf≤0` 只在 shell-pi；B_I 下不成立。Task-166 不能把这一分支当作 B_I paper-level。
4. **Radius normalization**：C7 的 `π p^{d_p}` 需明确是 shell-pi；B_I 下为 `p^{d_p}`。base-p 纠错保留。
5. **Actual r_v / complete C / target** 仍 open；P6 未证。

本审计不新增 attack，不修改 Lean，不声称 target accepted。

