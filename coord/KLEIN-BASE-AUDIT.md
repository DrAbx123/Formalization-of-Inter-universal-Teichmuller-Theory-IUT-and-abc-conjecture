# KLEIN-BASE-AUDIT — FEAS-KLEIN 的底座/算术模型审计（A1096）

日期：2026-11-13。**Status: READ-ONLY AUDIT；不编译、不新增 Lean。**
对象：`coord/FEAS-KLEIN.md`；相关：`coord/OUTSIDE-DELIGNE.md`、`coord/THETA-SECTION-PLAN.md`、`tmp/sheaf/xif/paper/DeterminantLogVolumeActual.lean`、`S2735QPilotLineBundleActual.lean`。

## 0. 结论先行

**MAPPING 需要算术模型与有理性，不能只靠上半平面的 theta/Klein 标量恒等式。**

* Klein forms / Siegel units 是**模曲线**（相对 `Spec Z[1/N]` 或 `Spec O_K` 的 modular curve）上的截面/函数；
* 我们的 `LineBundle k := FractionalIdeal (nonzeroDivisors O_k) k` 是 `Spec O_K` 上的线丛（fractional ideal class）；
* 二者不是同一底空间：没有 `Spec O_K → X(N)` 的截面/level structure，就没有从 modular curve 的 Klein/Siegel 乘积到 `Spec O_K` 线丛的拉回；
* FEAS-KLEIN 的 `MAPPING` 只写 `∏θ(u_j)^{j²} = ∏𝔨·η^M·const`（复标量恒等式），**不能说成 O_K 线丛的截面相等**；
* 有限位整性（Siegel units integral）也依赖**整模型/正则模型**与 q-展开整性，不能由上半平面标量恒等式自动得到。

## 1. FEAS-KLEIN 的主张与缺口

文档 §2/§4 的 MAPPING：
```
∏_j θ(u_j)^{j²} = (∏_k 𝔨_{(a_k,b_k)}(z)) · η(z)^M · const
```
Claim：这是标准 theta 变换/eta 乘积恒等式，形式化后 arch 范数可由 Kronecker 极限/Siegel 显式公式给出，有限位由 Siegel units 整性给出。

缺口：
1. **底空间/模型**：`θ(u_j)` 是复值（或 p 进值）theta 值，`𝔨`/Siegel 是模曲线上的截面；我们的线丛底是 `Spec O_K`。缺少：
   * `X(N)` 在 `O_K` 上的 canonical/integral model（或至少 `Z[1/N,μ_N]` 模型 + base change）；
   * 一个 `Spec O_K → X(N)` 的截面（等价于 O_K 上的椭圆曲线 + level structure + torsion 点 `u_j`）；
   * 拉回 `π^*` 后与 `qPilotLineBundle`（S2735 的 fractional ideal）的**理想类相等**；
2. **有理性**：`u_j` 是 torsion 点，theta/Klein 值在 C 中；要成为 `O_K`-线丛的截面，需证明这些值在 `O_K`（或某有限扩张）中、Galois 不变、且 q-展开整；
   仅“经典恒等式”不证明有理性/整性；
3. **arch 度量**：Kronecker 极限/Siegel 公式给 modular curve 上的 arch 度量；拉到 `Spec O_K` 的线丛需 Deligne pairing/Arakelov 度量与我们的归一化 `−sF·A` 对齐；文档只写“显式表达式”，没有 metric 比较；
4. **有限位整性**：Siegel units 在模曲线整模型上整；拉回到 `Spec O_K` 需该截面的整模型与 q-展开分母控制；FEAS-KLEIN 直接把 “Siegel units 整性 ⇒ v_p≥0” 当结论，缺拉回/模型论证；
5. **theta 侧对象**：我们的截面是 `∏θ(u_j)^{j²}`，但 `u_j` 来自模 l 表示的 torsion 点；需要把 `u_j` 与 Klein 参数 `(a_k,b_k)` 的对应写成 level structure 的映射，并证明该映射与 `qPilotIdeal` 匹配；文档只说“theta 变换公式给出”，未给精确对应。

**判定：MAPPING 不是纯复分析恒等式；它需要算术模型（modular curve over O_K / integral model）、O_K-截面、有理性与 ideal-class 比较。**

## 2. 对 FEAS-KLEIN 判定的审计

### 2.1 “A-候选”是否成立

文档判定 Klein/Siegel 是 A-候选，前提 (i) MAPPING 形式化、(ii) 公式形式化、(iii) 显式不等式。问题：
* 这些前提里，**(i) 不是“标准恒等式形式化”那么简单**：缺少算术模型/有理性，属于新的几何/算术构造；
* (ii) Kronecker 极限/Siegel 公式本身标准，但要在 `O_K` 线丛上使用，仍需 metric 与模型；
* (iii) 显式不等式依赖前两者；
* 因此当前最多是 **B+ / PARTIAL**，不是 A-候选；文档把它列为 A 过于乐观。

### 2.2 Lean 草案：INVALID/占位

FEAS-KLEIN §5 的 Lean 草案有多处问题：
1. `KleinArchFormulaData.formula : Prop` 是任意 Prop，没有显式公式；`y,N,archLogNorm` 自由；
2. `ThetaAsKleinProduct (s : Real) (kleinProduct : Real) : Prop := s = kleinProduct` 只是 Real 等式，不涉及线丛/模型；
3. `arch_le_of_klein (h : F.archLogNorm ≤ 0) : F.archLogNorm ≤ 0 := h` 是恒等，不产生 arch 估计；
4. `SiegelIntegralityData.integral : 0 ≤ finiteIndex` 是字段，不是 Siegel units 整性证明；
5. `thetaSectionDataOfKlein` 构造 `ThetaSectionData` 时：
   * `Bundle := Unit`、`section := ()`、`section_nonzero := True`、`nC := 0`、`theta := Fin.elim0`、`section_eq_prod := True`：完全是空占位；
   * `degree := I.finiteIndex - F.archLogNorm`：与 A1088 审计的 deg 符号错同型（应为 `arch − finite`）；
   * 字段 `arch_source := True`、`finite_source := True` 不在 A1088 的 `ThetaSectionData` 结构中（会类型错误）；
6. 该草案没有构造任何 theta 乘积截面、没有 Klein/Siegel 模型、没有有理性/整性；
7. 结论：**Lean 草案 INVALID/占位，不能作为 MAPPING 或 A 候选的证据**。

## 3. MAPPING 需要什么（判定）

要判定 MAPPING 可行，至少需要以下**算术模型/有理性**数据（缺一即不是 A）：

1. **整模型**：`X(N)` over `Spec O_K`（或 `Spec Z[1/N, μ_N]` 后 base change）的 proper/regular model；
2. **截面/点**：`Spec O_K → X(N)` 对应 O_K 上的椭圆曲线 E 与 full level N structure，且 `u_j` 是该 E 上的 torsion 点；
3. **拉回线丛**：`π^*` 的 universal theta/Klein line bundle 与 `qPilotLineBundle`（S2735 的 fractional ideal）在 `Pic(O_K)` 中相等（或差一个显式已知类）；
4. **有理性/整性**：theta/Klein 值在 `K` 的整数环中、Galois 不变、q-展开整；Siegel units 的整性经整模型拉回；
5. **度量**：Kronecker/Siegel arch 公式与 Deligne pairing/Arakelov 度量在拉回线上一致；
6. **归一化**：`−sF·A` 与 `deg` 的符号/因子 `2l`/`[K:Q]` 对齐（与 A1088 的 deg 符号错误同风险）。

如果 MAPPING 只是“上半平面上的 theta 恒等式”，它既不能给出 `v_p(s)≥0`，也不能给出 `Spec O_K` 线丛的截面；
因此 **MAPPING 必须带算术模型与有理性，不能只当解析恒等式**。

## 4. 判定汇总

| 对象 | 判定 | 说明 |
|---|---|---|
| `FEAS-KLEIN` 整体 | **PARTIAL/INVALID** | 文献公式标准，但 MAPPING 缺算术模型/有理性；有限位整性与 metric 未论证；Lean 草案占位且符号/字段错 |
| MAPPING 是否需要算术模型/有理性 | **需要（YES）** | 模曲线截面到 Spec O_K 线丛必须经 integral model + O_K-截面 + Pic 比较 + 有理性；标量恒等式不够 |
| Klein/Siegel arch 公式 | **LITERATURE（未形式化）** | 可作为输入，但不能单独推出我们的 arch_le；需 metric/归一化 |
| 有限位整性 | **GAP** | Siegel units 整性需整模型拉回；不能由上半平面恒等式直接得 |
| Lean 草案 | **INVALID/占位** | Unit/True/Fin.elim0、deg 符号错、字段不存在；无对象构造 |
| 循环性 | **无 CIRCULAR** | 文档未用目标证目标；问题是底座/模型缺失与占位，不是循环 |

**总判定：FEAS-KLEIN 不是 A-候选，最多 B+；MAPPING 需要算术模型与有理性。当前不能把 Klein/Siegel 公式当作 `arch_le`/`finite_ge` 的证明。**

## 5. 修正建议

1. 先把底座写清：`X(N)` 的整模型、`Spec O_K`-截面、E/O_K with level N、u_j 的 torsion 点；
2. 证明拉回线丛与 `qPilotLineBundle` 的 ideal class 关系；这是 MAPPING 的真正内容，不是 theta 标量恒等式；
3. 证明 theta/Klein 值的有理性/整性（Galois、q-展开）；
4. 把 Kronecker/Siegel arch 公式作为**显式输入**（带 metric 比较），不要直接写成 `arch_le`；
5. 有限位整性用整模型 + Siegel units，不能只用“标准”二字；
6. 修 Lean 草案（或删除）：不要用 `Unit/True/Fin.elim0` 填 `ThetaSectionData`；若保留，必须用真实 `Bundle/section/theta` 且修正 `degree=arch−finite`；
7. 未编译/无 olean ⇒ gate PENDING-WATCHDOG，不写 PROVED。