# C9 stage1：actual archimedean 区域与 log-Kummer 列间复合的补偿能力

任务：task-150 / C9 stage1（archimedean and log-Kummer compensation）。owner：iplsheapt。日期：2026-10-25。自然语言研究，不写 Lean，不改 Project，不改目标，不引入 arbitrary assumption。消费者：n8-c9-output-region-source-route；原目标仍为每份原文合格完整 C、固定 native q/BPS/gluing/目标列/normalization，排除完整最终输出族的统一严格亏损 h_C<Q_C。

前包：C9-TAME-LOG-DOMAIN-20261025.md（下称 TAME；SHA256 23B3514B94972DE511F1B17E23AB3DA832ED5BC63E89DACA3875ADEB07961F06）§7–§8 给出 finite bad-profile 的 actual 子族下界；本包只回答其 §8 指出的下一项：actual archimedean 区域和原 log-Kummer 列间复合能否提供同一量纲的补偿。

**task-147 correction（2026-10-25）**：TAME §2 的 symplectic donor 叙述有错误；corrected audit 为 `C9-SYMPLECTIC-SOURCE-20261025.md`（SHA256 3F98F68A5E143DCD51ED6790B1C839AE7B8811E4E418D48B02E37E7C4D5B9C70）。本包不复制 boundary-word-preserving free-group substitution 作为 actual Galois automorphism，也不把 rho 当同态。Archimedean 上界（§3）独立于该 donor；但 §4 的 finite deficit 数值取自 TAME §7，因而继承该 inferred donor assembly 的条件性，见 §0.1 与 §9。

状态：stage1 自然语言研究。没有 Lean/Project/kernel/comparator/独立审查；没有证明原 P6；没有把局部失败写成全局反证。

## 0.1 task-147 correction 与本包依赖标记

Corrected symplectic donor（C9-SYMPLECTIC-SOURCE-20261025，task-147）明确指出 TAME §2 的以下问题，本包不采用原始强形式：

1. `rho : Mod(S\{P}) -> Out(G_K)` 不是已知群同态（2025 Remark 2.18），不存在被假定的 homomorphic section；correct donor 是闭 preimage `H = Phi^{-1}(Sp_{2g}(Z_p))`（`Phi(H)=Sp`），不是“rho 的像等于 Sp”。
2. 保持 JW boundary word 的自由群自同构**不自动**是 actual `G_K` 自同构；actual source 是 mapping class/Dehn twist 的 `rho`，以及 2026 Lemma 3.3 / 2025 §2 的闭包论证。
3. 2025 trace basis 与 2026 symplectic basis 的 alignment 是 inferred convention，不是两篇论文明确陈述的 cross-paper theorem；`G|U=id, G|W=Sp` 应读作 `H` 的 preimage 作用，而不是显式构造的子群。
4. 2025 Theorem 1.3 的 trace 是 `Tr_{K/K^{(d=1)}}`；tame totally ramified（e=ell, f=1）才有 `K^{(d=1)}=Q_p`，不能无条件替换成 `Tr_{K/Q_p}`。
5. `J=m`、standard-lattice 分类、orbit generation、normalized volume gain `((t-1)/e)log p` 是 context 的 inferred consequences，不是 Kondo 论文的定理。

因此本包的依赖分为两层：

- **Paper-level / donor-independent**：IV Prop1.5/Thm1.10(vii) 的 archimedean container、normalized `B_I`、upper bound (3.2)，以及 §5/§6 的列间复合方向分析；这些不使用 symplectic donor。
- **Conditional on TAME §7 finite lower bound**：§4 的 b=3 / b=273 数值和“arch-only 不足”的比较。TAME §7 的 finite values 依赖上述 inferred donor assembly；在 task-147 的 corrected `H=Phi^{-1}(Sp)`、basis alignment、trace target 和 orbit-generation 未逐项重验之前，§4 只能作为**条件性数值比较**，不能当作 paper-level theorem。若 finite 下界在 corrected donor 下改变，§4 的数值比较需重算；§3 的 arch 上界仍独立成立。

## 0.2 结论

1. **Archimedean 分支不能提供与 q-exponent b 同量纲的补偿**。在 IUT III/IV 的实际 normalization 下，一个 archimedean vQ 的 Θ-hull 容器 log-volume 至多为

   `A_arc(vQ) ≤ (j+1) log π`（第 j 层 container），

   对 j 取 procession average 后为

   `A_arc(vQ) ≤ ((l+5)/4) log π`。

   它与 b 无关，只随 l 线性。C9 的 uniform bad-profile finite 子族亏损（条件性地取自 TAME §7；见 §0.1）随 b 线性增长；TAME §7 的精确 b=3 与 b=273 两行在 corrected donor 下重验之前，只能作为该 subfamily 的条件性数值比较（见 §4）。
2. **Tensor packet 的维数不是 log-volume**。IV Prop1.5(iii) 的 direct-sum/tensor dimension factor `2^{|I|-1}|V|^{|I|}` 在 normalization 中被 `B_I` 的零 log-volume 消去；只有 radial factor `π^{j+1}` 给出 `(j+1)log π`。因此“维数很大”不提供补偿。
3. **原 log-Kummer 列间复合在 archimedean 侧没有额外的 b 方向**。archimedean log-link 是 `exp`（不是 p-adic log）；Kummer 是单位群的 roots/powers；Ind1/Ind2 是 rotation/conjugation；Ind3 是 upper semi-compatibility。IV Thm1.10(vii) 的容器 `π^{j+1}B_I` 已经包含全部 possible images，故任何 archimedean 列间复合的 log-volume 仍受 §0.1 的 O(l) 上界。
4. 论文只给出 archimedean 的**上界**，没有给出 actual archimedean output 的**下界**；不能把“上界可覆盖 deficit”当作“补偿存在”。本包在 corrected donor 与 TAME §7 finite 下界的条件下，只能证明 archimedean-only 补偿在该 uniform 子族中不足；不能据此宣布完整 h_C<Q_C，也不能把 §4 的数值当作 Kondo 论文的定理。
5. 精确剩余计算：actual archimedean q/Θ 的值（不是仅容器）、radial/angular 的实际 normalization、全部 V_arc 权重、q-side arch component，以及所有 finite log-Kummer 分支的加入。它们中任何一个都还没有在 Lean 或原 source construction 中给出。

## 1. 对象、阶段与问题

固定原完整 C、原 selected bad finite place v、原 q、原 BPS/Θ-gluing、目标列和 normalization。TAME 的 all-bad local type 为

```
K/Q_p tame totally ramified cyclic, e = l ≥ 5,
p > e+1, μ_e ⊂ Q_p, π^e = p u, u ∈ Z_p^×,
b j² = s_j e + t_j, 1 ≤ t_j < e, s_j ≥ 0.
```

TAME 的 finite bad-profile 子族给出 `h_p^aligned`（在 log p 单位）；native q 的对应值为 `Q_p = -ρ b/e`（ρ 为该 p 的 bad weight）。本包要问：把 actual archimedean 区域和原 log-Kummer column composites 加入后，能否把这些 deficit 补到 `Q_p` 以上？

注意两个量纲不能混：finite bad log-volume 是 `log p` 的倍数；archimedean 的自然 log-volume 在除以 `log p` 后才能与 TAME 的表格比较。本包所有比较都显式写出换算。

## 2. 论文的 archimedean 归一化与符号

### 2.1 log-shell 与 log-link

IUT III Def1.1(ii)/Rmk1.2.2(ii)：对 `v ∈ V_arc`，`k=K_v` 为复 archimedean 域，

```
O_k = {a : |a| ≤ 1},   O_k^× = {a : |a| = 1},
I_k = {a : |a| ≤ π},   O_k^× ⊆ exp_k(I_k).
```

finite bad 的 log-link 是 p-adic `log`（principal units），archimedean 的对应方向是 `exp`；后者的定义域是 `I_k` 的加性 log-shell，而不是 `O_k^×` 的普通 p-adic log。**不能把 finite p-adic log 的定义域直接搬到 archimedean**。

### 2.2 符号

论文的 archimedean log-volume 使用 radial 坐标：`π^{j+1}B_I` 的 log-volume 是正的 `(j+1)log π`；`B_I` 的 log-volume 被 normalization 设为 0（IV Thm1.10(vii)）。

当前 Lean 的 `Example36ArchimedeanLocal.absLogAddHom` 定义

```
absLogAddHom K u = -Real.log ‖(u : K)‖,   archimedeanDelta r = -Real.log r.
```

因此 Lean 的 additive character 是论文 radial log-volume 的**负值**：若用 Lean 的 `absLogAddHom` 或 `archimedeanValueGroupKernel.realification` 直接比较，必须先取负号，或统一用 `-archimedeanDelta`。否则会把 archimedean 的正贡献读成负贡献，符号错误。

### 2.3 权重与 procession average

III Rmk3.1.1(ii)(iv)：每个 v 的 log-volume 用 weight `1/[K_v:(F_mod)_v]`；对 vQ 求和时用 normalized weight，使乘以 `p_{vQ}` 对 log-volume 的影响为 `±log p_{vQ}`：nonarch 是减法，archimedean 是加法。archimedean 的 `p_{vQ}` 是自然底 `e`，故乘 e 的贡献为 `+1`（自然 log 单位）。这不是一个可任意缩放的参数；它来自原 normalization。

procession normalization 对 `j ∈ F_l^⋆` 取平均；本包的 arch bound 已经按这个 average 写出。

## 3. 论文给出的 archimedean 精确上界

IV Prop1.5(iii)(iv)：在 `|I|=j+1`、`V=V(F_mod)_{vQ}` 的 tensor packet 中，若每个因子长度 ≤π，则 tensor 属于

```
π^{j+1} B_I ⊆ M_I.
```

IV Thm1.10(vii) 进一步说明：取 normalization 使 `log-volume(B_I)=0`，则这个 container 的 log-volume 恰好是

```
log-volume(π^{j+1} B_I) = (j+1) log π.        (3.1)
```

对 j=1,...,m（`m=(l−1)/2`）取 average，并用 `Σ_{j=1}^m (j+1)/m = (m+3)/2 = (l+5)/4`：

```
A_arc(vQ) ≤ ((l+5)/4) log π.                  (3.2)
```

这是**上界**：实际 Θ-pilot 的 possible images 在 container 内，故其 archimedean hull log-volume 不超过 right-hand side。论文没有给出该区域包含某个固定大球的**下界**；`B_I` 只是 unit ball，可能实际 image 远离半径 π。

IV Thm1.10(viii) 把各 vQ 的 local bound 相加；本包不需要其全局最终常数，只需 per-vQ 的 (3.2)。在 `F_mod=Q`、`F` 含 `i` 的情形，V_arc(Q) 只有一个 complex vQ；normalized weight 已把 archimedean places 的权重合计为 1（Rmk3.1.1(iv)），所以不额外乘 archimedean place 个数。对一般 F_mod，按同一 normalization 的 weighted sum 使用 (3.2)。

### 3.1 为什么 direct-sum 维数不进入体积

IV Prop1.5(iii) 给出 direct sum decomposition 的 copy 数 `2^{|I|-1}|V|^{|I|}`，且 direct-sum metric 与 tensor metric 相差 `2^{|I|-1}`。但 `B_I` 是各 copy 的 unit ball direct product，normalization 令其 log-volume 为 0；`π^{j+1}B_I` 只把 radial factor 放大 π^{j+1}。因此

```
log-volume(dimension factor) = 0,
log-volume(π^{j+1}B_I) = (j+1)logπ, not 2^{j}...·logπ.
```

这是本包对“same-dimension compensation”的核心否定：tensor packet 的指数级维数并不产生指数级 log-volume。

## 4. Finite bad deficit 与 archimedean 上界的直接比较

TAME (10) 对 uniform bad profile `ρ=1`（所有 bad factor 同一 local type）给出

```
ell_j^Sp = -c j - [s_j + e^{-j-1}],   c=(e-1)/(2e),
h_p = (1/m) Σ_{j=1}^m ell_j^Sp,   Q_p = -b/e,
m=(e-1)/2,   b j²=s_j e+t_j.
```

TAME §7 的精确表（e=41, m=20）给出两个可核对的点。**重要**：这些 finite values 继承 §0.1 的 inferred symplectic donor / orbit-generation 条件性；本包没有重验 corrected `H=Phi^{-1}(Sp)`、basis alignment 和 trace target。因此下表是 conditional comparison，不是 paper-level theorem。

| b | h_p（log p 单位） | Q_p（log p 单位） | Q_p−h_p |
|---:|---:|---:|---:|
| 3 | −411/41 ≈ −10.024390 | −3/41 ≈ −0.073171 | 408/41 ≈ 9.951220 |
| 273 | −38736/41 ≈ −944.780488 | −273/41 ≈ −6.658537 | 38463/41 ≈ 938.121951 |

Archimedean 上界 (3.2) 在 `l=41` 为

```
A_arc ≤ (46/4) log π = 11.5·1.1447299 ≈ 13.164394   (自然 log 单位).
```

TAME 表格用 `log p` 单位；对最小允许的 `p>e+1=42`，即 `p≥43`，有

```
log π / log p ≤ log π / log 43 ≈ 0.304403,
A_arc / log p ≤ 3.500052   (log p 单位).
```

对 `p=12301`（TAME §7 的 local realization），上界更小：

```
A_arc / log p ≤ 1.397875   (log p 单位).
```

因此：

- b=3 时 finite deficit 已是 `408/41 ≈ 9.951220`，大于 archimedean 最大正贡献 `3.500052`；
- b=273 时 deficit 为 `38463/41 ≈ 938.121951`，远大于同一上界；
- 更大的 b 只会增大 finite deficit（TAME 的 b↦b+e affine-period formula 中 uniform profile 的差仍下降）；
- 故在 TAME 的 uniform rho=1 子族中，archimedean-only 正贡献不能补偿 finite bad deficit。

这是本包的主要可验证结论。它**不**说明完整 `h_C` 不大于 `Q_C`，因为 full h_C 还可能包含其他 finite log-Kummer 分支、其他 bad places/weights、q-side 修正；这些没有在本包上界中。它只排除“把 archimedean 区域当作这个 subfamily 的补偿项”这一条。

### 4.1 符号核对

TAME 的 `Q_p` 和 `h_p` 都是负量；`Q_p−h_p>0` 是 deficit。archimedean 的 `+logπ` 若能进入 h_C，会增加 h_C（使其更不负），最多加 §3.2 的上界。上面的比较是 `deficit > A_arc`，所以 `h_p + A_arc < Q_p` 在这个 subfamily；没有用“正负项可能抵消”的猜测。

## 5. 原 log-Kummer 列间复合在 archimedean 侧能做什么

必须区分三条箭头：

1. **log-link（水平）**：finite bad 是 p-adic log（principal units）；archimedean 是 `exp`（III Def1.1(ii)/Rmk1.2.2(ii)）。archimedean `exp` 把 `I_k` 的加性 log-shell 送到 `O_k^×` 的单位球面附近；它不会把 q 的整数指数 b 变成 archimedean 半径的 b 次幂。
2. **Kummer（垂直）**：单位群的 roots/powers；在 archimedean 只改变相位/模长的 root，所有 possible image 仍由 IV container `π^{j+1}B_I` 控制。
3. **Ind1/Ind2/Ind3**：Ind1 是 procession automorphism；Ind2 是 independent `Ism`/order-2 automorphism（archimedean 的 conjugation/rotation）；Ind3 是 upper semi-compatibility（非阿 `⊆`，阿 `↠`）。archimedean Ind2 的 rotation 保持半径；conjugation 也保持模长。因此它们只能改变 angular log-volume，不能把 radial log-volume 推过 container 上界。

IV Thm1.10(vii) 的 container 已经是对**全部 possible images**（包括这些 Kummer/log/Ind 操作）取的；因此列间复合的 archimedean 输出仍满足 (3.2)。不存在一条由原 source 给出的、额外把 archimedean 半径乘以 `q^{b}` 的箭头。

## 6. q-pilot 的 archimedean 侧

q-pilot object 由 finite bad places 的 q_v zero locus 给出（III Def3.8(i)/intro；q-pilot log-volume `-|log q|`）。它不以 archimedean q 参数为源；archimedean 部分对应 structure sheaf/`O(-)` normalization，`B_I` 的 log-volume 为 0（IV Thm1.10(vii)）。因此：

- q-pilot 的 `b` 依赖只来自 finite bad q_v；
- archimedean q-side 不提供另一个 `b` 方向的负量/正量；
- 即使某个 global arithmetic line bundle 有 archimedean component，它由固定 C 的 archimedean 数据决定，是与 b 无关的常数，不能补偿随 b 增长的 finite deficit。

这一点必须和“archimedean 上界可加”区分：上界是 Θ-hull side 的 positive allowance；q-side 没有对应的 b 可调项。

## 7. “同一量纲”到底是什么意思

TAME 的 finite deficit 由 `s_j≈b j²/e` 产生，主导项是 `b·(e+1)/12`（uniform profile，忽略 O(e) 常数）；它随 b 线性增长。Archimedean 的 upper bound 是 `O(l)`，固定 C 后与 b 无关。因此：

```
finite bad deficit = Ω(b),   archimedean positive allowance = O(l),
```

二者不同量纲；不存在对所有 b 的统一补偿。b 很小时二者都可能是 O(l)（因为 b=O(1)），但 b=3 的精确比较已显示 arch 上界仍小于 deficit；更大的 b 更不可能。

Tensor packet 的 dimension factor 也不改变这一结论（§3.1），因为 normalized `B_I` 的 log-volume 为 0。

## 8. 要证明补偿存在，还缺什么

以下都是 exact source computations，不是新增假设：

1. **Actual archimedean image**：把 q/Θ-pilot 的实际 archimedean absolute values 算出来，而不是只用 container `π^{j+1}B_I`。需要逐 `v∈V_arc` 的 `log|a|_v`，并保留论文的**正号**径向 log-volume（与 Lean `absLogAddHom` 的负号相反）。
2. **Exact procession weight**：`j∈F_l^⋆` average、`1/[K_v:(F_mod)_v]`、archimedean place 权重、以及 `p_{vQ}=e` 的 normalization。不能把 different vQ 的 arch bound 相加成 b 的倍数。
3. **Actual lower bound**：IV Thm1.10(vii) 只给 upper bound；要说明补偿，需要 actual Θ-hull 包含一个足够大的 archimedean ball，或 actual image 的 radial log-volume 有正下界。当前 source 没有这个下界；`B_I` 只有 unit ball。
4. **q-side arch component**：确认 q-pilot 在 V_arc 的 arithmetic line bundle 的实际 normalization；若它不是 0，则其依赖 C 的常数要计入 Q_C，但仍不是 b 的线性项。
5. **Finite log-Kummer 分支**：archimedean 不能补偿后，仍需计算其他 finite bad/column composites；这不属于本包，不能把 arch 上界当作全局 h_C 上界。

这些量一旦算出，比较规则仍是：

```
h_C = h_finite_bad + A_arc + h_other_finite,
需要 h_C ≥ Q_C;  arch-only 已由上界排除于 TAME uniform 子族。
```

## 9. 与 TAME/STRICT-DEFICIT 的 consistency

TAME 的 `h_p` 是（在 corrected donor 与 basis alignment 条件下）finite bad **subfamily lower bound**；本包的 `A_arc` 是 actual Θ-hull archimedean **upper bound**（此上界独立于 symplectic donor）。不等式

```
h_p + A_arc < Q_p      (e=41, uniform rho=1, b=3 and b=273)
```

只说明这个 subfamily 的 finite+arch 部分仍不足；它允许其他 finite log-Kummer 分支使 full `h_C` 更大。原 P6 仍未证明。若 task-147 的 corrected donor 重验后 finite 下界改变，本比较不自动保持；§3.2 的 arch 上界与 §5/§6 的 arch 方向结论不受影响。

C9-STRICT-DEFICIT 的 `Q_C` 用 `-(6/ell)ΣρM` 的符号约定（M=L/12）；本包的 `Q_p=-b/e` 与之在 uniform local type 下一致。`-|log Θ|` 与 `-|log q|` 的论文不等式方向（`-|logΘ| ≥ -|logq|`）没有被本包改变。

## 10. 验证与交付边界

- 本包只写本文件；没有修改 Lean、Project、目标、定义或其他 owner 文件。
- `source_initial_theta_data` 与 actual archimedean q/Θ 值未在 Lean 中构造；本包不声称它们已存在。
- 未运行 Lean/Project/kernel/comparator；未做独立审查；target_accepted=false。
- TAME/IV 的引用通过本文件符号与精确公式；没有把 IV Thm1.10(vii) 的 upper bound 当作 lower bound。
- 所有数值比较都可复算：`408/41`、`38463/41`、`(46/4)logπ`、`logπ/log43`、`logπ/log12301`。

## 11. 精确引用

- IUT III, Def1.1(ii), Rmk1.2.2(ii): archimedean log-link/exp, `I_k={|a|≤π}`, `O_k^×⊆exp(I_k)`。
- IUT III, Prop3.1/3.2, Prop3.9(i)(ii), Rmk3.1.1(ii)(iv): tensor packets, procession-normalized log-volumes, normalized weights; Thm3.11(i)(a), (ii), (iii): LGP/log-Kummer compatibility and Ind1–3; Cor3.12/Theorem B: `-|logΘ| ≥ -|logq|`。
- IUT IV, Prop1.5(iii)(iv): direct-sum/tensor metric and `π^{j+1}B_I`; Thm1.10(vii) pp.29–30: container `π^{j+1}B_I`, `log-volume(B_I)=0`, local upper bound `(j+1)logπ`, procession bound `(l+5)/4 logπ`; Thm1.10(viii): sum over vQ。
- TAME (C9-TAME-LOG-DOMAIN-20261025) (10), (15), §7 table; C9-STRICT-DEFICIT-LOOP-20261024 (4.4)。
- C9-SYMPLECTIC-SOURCE-20261025.md, task-147: corrected actual `Aut(G_K)` symplectic donor; `rho` not a homomorphism, `H=Phi^{-1}(Sp)`, mapping-class/Dehn-twist source, basis-alignment and trace-target caveats; TAME §2 correction. SHA256 3F98F68A5E143DCD51ED6790B1C839AE7B8811E4E418D48B02E37E7C4D5B9C70。
- Lean actual readout: `Example36ArchimedeanLocal.lean` (`absLogAddHom=-log`, `archimedeanDelta=-log`, exact sequence); `Example36PrimeStripBridge.lean` (`archimedeanValueGroup`, degree=identity, realification=`toAdd`, sign opposite to paper radial log-volume)。

本文件只作 stage1 research note，不是 P6/ABC 完成声明。

