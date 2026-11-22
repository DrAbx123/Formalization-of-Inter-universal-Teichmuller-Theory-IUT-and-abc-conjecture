# C9 attack：其他局部类型 / e ≥ p−1 的补偿能力

任务：task-179（C9 attack: other local types / e>=p-1 compensation）。owner：iplsheapt。日期：2026-10-25。stage1 自然语言/精确算术研究；不改 Lean/Project/目标；不引入 arbitrary positive branch；只写本文件。

输入：

- C9-FULLC-WEIGHTS-ATTACK-20261025.md（task-169，SHA256 142B63C7E22DA681EFB6CFC2E3C45E0A58C0BB5135F4E995FC35B1E488CC249C）
- C9-LOG-DOMAIN-CORRECTION-20261025.md（task-170，SHA256 882DFDEF2BF11377EBC6FDC488205623804100CC54DEEACD5EC805E75F481655）
- C9-TAME-LOG-DOMAIN-20261025.md（SHA256 23B3514B94972DE511F1B17E23AB3DA832ED5BC63E89DACA3875ADEB07961F06）

前序纠偏保持：task-147 corrected symplectic donor；task-149 target containment withdrawn/TC-A..H/TC-S；task-170 log/exp 域修正（log 全域收敛，exp 严格阈值 `n_exp`，restricted shell，f 因子）。finite deficit 仍 conditional。

## 0. 结论

1. **严格修正后的 log 域不允许 e≥p−1 产生正的 restricted-shell 绝对体积**。对任意 e≥1，`n_exp=floor(e/(p−1))+1 ≤ e`；restricted shell 为 `I_K^{res}=m^{n_exp-e}`。按 task-170 的 exact formula

   `logvol_O(I_K^{res}) = ((n_exp-e) f/e) log p ≤ 0`，

   等号只在 e=1 或 (p=3,e=2) 等边界；其余类型严格负。f>1 只会把负值放大，不能把它变成正补偿。
2. **其他局部类型可产生一个非负的 normalization shift，而非已证 positive output**：把 `n_exp=1` 的 tame shell 与一般 `n_exp` 比较，

   `Δ_shell := ((n_exp-1) f/e) log p ≥ 0`，  `n_exp-1=floor(e/(p−1))`，

   因而 `Δ_shell ≤ (f/(p−1)) log p`。这是把 shell 的负 log-volume 往 0 方向移动的差；**没有 source theorem** 把这一个 normalization 差直接算进完整 C 的 h_C，也没有为 wild/e≠ℓ 给出 actual output hull 公式。故它是 unknown 的潜在项，不是 actual compensation。
3. 对 b=3/b=273 residual，B=O_K 的 tame bad places 全部加重亏损（task-169/F6）；B=I 的 b=3 局部 surplus 12/41 只是 conditional/unproved，不是 actual。其他 local types 没有已证 output 公式，不能用来抵消。
4. **Impossible（不能作为 source theorem）**：把 tame `J=m`、`B=O_K/B=I`、trace/W、T14/T15 公式无条件搬到 e≥p−1；或声称任何 other local type 自动给出正的 normalized-volume 贡献。**Unknown**：wild/ramified/e≠ℓ 的实际 output hull positive part、完整 bad set、f、B 分支、TC 条件。
5. Archimedean 上界仍独立：`h_inf≤(l+5)/4 logπ=13.164394` natural；b=3 conditional residual 408/41 logp，即使 p=43 也 ≥37.43 natural；other local types 的 shell shift 若真要补 b=3，需要 f 足够大（见 §4），但 current source 没有这样的实际构造。

## 1. 修正后的 log/exp 域与 shell

记 K/Q_p 有限，p 奇，ramification e，residue degree f，`q_res=p^f`，`m=πO_K`，`U^1=1+m`。Task-170 的严格结论：

```
log: U^1 → m  converges for all U^1;
n_exp := floor(e/(p−1)) + 1;  exp converges on m^{n_exp};
e=p−1 ⇒ n_exp=2;  e<p−1 ⇒ n_exp=1;  e>p−1 ⇒ n_exp≥2.
```

source Teichmuller convention (b)：

```
D_K = μ_{q_res−1}(K)·U^{n_exp},
J_K = log(D_K) = m^{n_exp},
I_K = p^{-1}J_K = m^{n_exp-e}.
```

注意：full analytic convention (a) 下 `log(U^1)` 不是 `m^{n_exp}`；本文件的 shell 公式只属于 restricted convention (b)，必须带此条件。

### 1.1 `n_exp ≤ e` 与 shell 指数

对 p≥3、e≥1：

- e=1：`n_exp=floor(1/(p−1))+1=1=e`；
- e≥2：`e/(p−1)≤e/2`，故 `floor(e/(p−1))≤e/2`，`n_exp≤e/2+1≤e`（e≥2）。

所以 `n_exp-e≤0`，restricted shell 是 `m` 的非正幂（包含 O_K 或等于 O_K）。按 task-170 (3.2)：

```
logvol_O(I_K) = ((n_exp-e) f/e) log p ≤ 0.             (L1)
```

边界：e=1 或 (p=3,e=2) 时指数0、volume=0；其他 e 严格负。f>1 只乘负值，使 (L1) 更负。

### 1.2 `Δ_shell` 的正性

若比较一般 restricted shell 与 tame `n_exp=1` shell，

```
Δ_shell = ((n_exp-1) f/e) log p = (floor(e/(p−1)) f/e) log p ≥0.   (L2)
```

上界：`floor(e/(p−1))≤e/(p−1)`，故

```
Δ_shell ≤ (f/(p−1)) log p.                              (L3)
```

(L2) 是**nonnegative normalization shift**，不是正 absolute volume；它把 (L1) 的负值向0移动。若 h_C 的 normalization 以 n_exp=1 shell 为 reference，(L2) 可能是候选增量；但 task-170 只给 shell volume，未证明完整 h_C 的 this shift 被 source output 实现。不能把它当 actual compensation。

## 2. 各局部类型的表格

| 类型 | e | n_exp | n_exp−e | (L1) 符号 | 可用的 actual output 公式 |
|---|---:|---:|---:|---|---|
| unramified bad/good | 1 | 1 | 0 | 0 | good finite=0；bad 的 B 分支无 tame 公式 |
| tame 但 e≠ℓ | 1<e<p−1 | 1 | 1−e<0 | 负 | tame trace/W 的 e=ℓ 假设不适用，无公式 |
| tame boundary | e=p−1 | 2 | 2−e≤0 | ≤0（e=2 时0） | wild boundary；B 分支/trace 无公式 |
| wild | e>p−1 | floor(e/(p−1))+1≥2 | <0 | 严格负 | J=m^{n_exp} 有定义，但 trace/W/B/T14/T15 不能搬 |

结论：**在 restricted-shell normalization 下，没有任何局部类型有正的 absolute shell volume (L1)**。f 因子对负值的放大与“positive f”直觉相反：f 越大，shell 负体积越大；(L2) 的 shift 才随 f 增大，但它只是 normalization 差。

## 3. 其他类型能否补偿 b=3/b=273?

### 3.1 已知 tame B=O_K baseline

Task-169/F6：对 e=41 tame uniform ρ=1、B=O_K：(L1) 不适用（低分歧），但有限 residual 为

```
D_p/log p = 408/41 (b=3), 38883/41 (b=273);
D_p = (408/41)log p, (38883/41)log p  natural.
```

对 p≥43，b=3 至少 `37.43` natural，b=273 至少 `3566.99`；arch max 13.164。B=O_K 的每个 additional bad place 都增加正 deficit，不能补偿。

### 3.2 其他类型可提供的最大 normalization shift

若把 (L2) 作为候选正 shift，每个 place 至多 `(f/(p−1))logp`；要覆盖 b=3 的 conditional `408/41 logp`，需

```
f/(p−1) ≥ 408/41  ⇒ f ≥ (p−1)·408/41.
```

b=273 需 `f ≥ (p−1)·38883/41`。f 由局部域 K/Q_p 决定，source **没有**给出 f 的构造/上界；大 f 在数域完成中原则上可出现，但没有 actual C/局部类型/输出公式。因此：

- 理论上 (L2) 足够大时数值上可超过 b=3/273 residual；
- 但 (L2) 不是 actual output volume，f 和局部类型未构造，不能登记为补偿；
- f 越大 (L1) 的负 absolute shell volume 也越大；因此 (L2) 只是 reference shift，不能直接说“大 f 提供正补偿”。

### 3.3 Good/unit/Kummer/Ind 分支

- good finite：相对 O_E=0；
- Kummer zero/unit small domain：O_K 或更小 lattice，相对 volume 0/负；
- B=I：仅 conditional b=3 surplus 12/41，B=O_K under natural alignment，B=I 不是 actual；
- Ind1/Ind2/Ind3、factor permutation、+infinity：没有独立 actual positive normalized volume；TC-A..H/TC-S 未证。

## 4. actual / conditional / unknown / impossible

### 4.1 Actual / donor-independent（在 task-170 convention 下）

A1. `n_exp=floor(e/(p−1))+1`，strict threshold；`e=p−1 ⇒ n_exp=2`，不是1。
A2. `n_exp≤e`，`I_K=m^{n_exp-e}`，`logvol_O(I_K)=((n_exp-e)f/e)logp≤0`。
A3. `Δ_shell=((n_exp−1)f/e)logp≥0`，上界 `f/(p−1)logp`；这是 normalization shift，不是 absolute positive volume。
A4. Good finite=0；B=O_K tame each adds positive residual（conditional finite D）。
A5. Archimedean max-container upper bound 13.164 natural（donor-independent）。

### 4.2 Conditional / inferred

C1. restricted convention (b) 是 source convention；full log convention (a) 下 (L1)/(L2) 只是另一个 normalization，不自动等于 h_C。
C2. B=O_K/B=I、d_p、b=3/273 residual 条件于 corrected donor/basis/target；B=I 未 actual。
C3. `Δ_shell` 计入 h_C 的 normalization；没有 source theorem。
C4. f、bad set、完整 C、TC 条件。

### 4.3 Unknown

U1. wild/e≠ℓ 的实际 output hull positive part；
U2. f 的可能范围/实际局部类型；
U3. B 分支/full barGamma；
U4. actual arch r_v/angular；
U5. complete h_C/Q_C。

### 4.4 Impossible（作为 source theorem）

I1. 把 tame `J=m`、B=O_K/B=I、trace/W、T14/T15 无条件搬到 e≥p−1；
I2. 从 (L2) 的 normalization shift 直接推出 actual positive h_C contribution；
I3. 用正 f 造成 positive absolute restricted-shell volume（(L1)≤0，f 只放大负值）；
I4. 用 additional B=O_K bad places 补偿已知 residual（它们加重）；
I5. 用 arch max-container 补 b=3/273（13.164 < 37.43/3566.99 natural）；
I6. 声称 other local types 已提供补偿/完成 P6。

## 5. 精确结论与剩余 gap

1. 在 task-170 修正域下，other local types 的 restricted-shell **absolute** normalized volume 对任意 e≥1 都 ≤0；f 只使负值更大。
2. 唯一的非负量是 `Δ_shell=((n_exp−1)f/e)logp≤f/(p−1)logp`，它是 normalization shift；要成为 actual compensation，需要额外的 source output/target normalization 定理，当前没有。
3. 因此对 b=3/b=273，other local types 没有已证 actual positive compensation；B=O_K tame bad places 只会加重；B=I 仅 conditional；wild/e≠ℓ 是 unknown，不是正分支。
4. 精确剩余 gap：actual C 的局部类型/f/bad set；wild trace/B 分支；`Δ_shell` 是否进入 h_C；TC-A..H/TC-S；actual arch/angular；完整 global weights。

## 6. 状态

Stage1 natural-language/exact arithmetic only；无 Lean/Project/kernel/comparator/独立审查；target_accepted=false；P6 open。没有把 `Δ_shell` 的数值可能当作 actual compensation，也没有假设 positive branch。

