# FRESH-GREEN-AUDIT — 新 green 文件语义审计（A1102）

日期：2026-11-13。**Status: READ-ONLY AUDIT；不编译。**
对象与状态（ole 存在 = watchdog 已产出；本审计不做 gate 复核）：
* `Mzk1StructuralTargetActual.lean` SHA16 `B66BEDDDD12AB681`，ole=True；
* `Mzk1ThetaSectionActual.lean` SHA16 `D8473CDD57536D07`，ole=True；
* `Mzk1LogMeasureSubmodularActual.lean` SHA16 `40D7D0FF4879BEAD`，ole=True。

## 0. 结论先行

1. **StructuralTarget**：两个 `target_of_*` 定理本身正确、无循环，但 `QPilotThetaContainment`/`QPilotThetaDetMorphism` 的字段**可被 q=θ、G=id、M=1 平凡满足**；因此 “GAP-XID: no inhabitant” 不准确；实际是“抽象接口可居住，实际 q/θ 对象未构造”；
2. **ThetaSection**：`deg_eq` 已修正为 `degree = arch_bound - finite_index`，`hcmp_of_theta_section` 的算术正确；但 `arch_source`/`finite_source` 仍是 **UNLINKED 的任意 Prop**，`section_nonzero`/`section_eq_prod` 也是任意 Prop，`theSection` 抽象；结构可空洞满足，arch/finite 估计未与 section 连接；
3. **LogMeasureSubmodular**：real 核心正确；measure 版**显式依赖 `hadd` 假设**，没有把假设当证明；无循环；作为条件工具可 PASS，但 GAP-MEAS-ADD 未消；
4. 三文件均未发现 CIRCULAR（没有假设目标推目标）；问题集中在“条件接口/空占位被算作对象构造”。

## 1. Mzk1StructuralTargetActual

### 1.1 定理内容

`QPilotThetaContainment` 字段：`qRegion⊆θRegion`、`-A=log μq`、`-R=log μθ`、正性/有限性；
`target_of_containment` 用 measure_mono + log 单调推出 `-A≤-R`；证明正确。

`QPilotThetaDetMorphism`：`G : Ω→Ω`、`M≥1`、`hchar : vol(G image q)=M*vol q`、`subset_scaled`、`hmono`；
`target_of_detMorphism` 用 `vol q≤M*vol q≤vol(G image q)≤vol θ`；当前用 `mul_le_mul_of_nonneg_right`，方向正确。

### 1.2 “对象存在性=GAP”是否成立

**不成立（对抽象结构）**：
* 取任意正有限测度集 `S`，令 `qRegion=θRegion=S`、`A=R=-log μS`，则 `subset` rfl、`q_norm/θ_norm` 成立、`hq_fin/hq_pos` 可满足；
* `QPilotThetaDetMorphism` 取 `G=id`、`M=1`、`q=θ`，`hchar` 为 rfl；
* 因此抽象结构**可平凡居住**；“no inhabitant” 只对**实际 Ω/μ/实际 θ-hull/q-pilot** 成立；
* 文件没有字段强制 actual 对象，也没有 strictness（`qRegion=θRegion` 允许）；
* 结论：`target_of_containment`/`target_of_detMorphism` 是**条件恒等**，不能当 xi-d 几何内容；header 的 GAP-XID 应改为 “actual instantiation GAP”。

### 1.3 判定

**PARTIAL（green 条件定理 + 空对象接口）**：定理正确、无循环；对象不存在构造；`existence=GAP` 标注不精确。

## 2. Mzk1ThetaSectionActual

### 2.1 deg 与 hcmp

当前 `deg_eq : degree = arch_bound - finite_index`，与 Plan §1/§4 的 `deg=arch−finite` 一致；
`hcmp_of_theta_section`：`arch_le : arch_bound≤0`、`finite_ge :0≤finite_index` ⇒ `degree≤0`；算术正确。
之前 A1088 指出的 `degree=finite−arch` 已修正；此点 PASS。

### 2.2 `arch_source`/`finite_source` 仍 UNLINKED

```lean
arch_source : Prop   -- UNLINKED placeholder
finite_source : Prop -- UNLINKED placeholder
```
* 它们**不是**等式 `arch_bound = Σ_σ log‖theSection‖`、也不是 `finite_index = Σ_p log#(...)`；
* 任意 Prop 都可以填入（True/False），没有证明义务；
* `arch_bound`/`finite_index` 仍是自由 Real，没有与 `theSection`、`theta`、`Bundle` 连接；
* 因此 arch/finite 估计没有“source equation”；它们只是**两个假设字段**，不是已构造估计；
* `section_nonzero : Prop`、`section_eq_prod : Prop` 同样任意；`theSection : Bundle` 抽象；
* 结构可由 `Bundle:=Unit`、`theSection:=()`、`nC:=0`、`theta:=Fin.elim0`、`arch_bound:=0`、`finite_index:=0`、`section_nonzero:=True`、`section_eq_prod:=True`、`arch_source:=True`、`finite_source:=True` 空洞满足；
* `hcmp` 仍只连接到 `degree`，没有连接到 StructuralLineBundle 的 `globalLogVolume det≤q`；bridge 缺。

### 2.3 判定

**PARTIAL/EMPTY**：算术定理正确、deg 已修；但 arch/finite/section 全是 UNLINKED 占位，对象未构造；无循环；不可把 green 当 theta 乘积截面已构造。

## 3. Mzk1LogMeasureSubmodularActual

* `submodular_real`：`p≤a,b, q=a+b−p, p>0 ⇒ p*q≤a*b`；由 `(a−p)(b−p)≥0` 得，正确；
* `log_submodular_real`：由 `Real.log_le_log` + log_mul 得，前提 `q>0` 由 `q=a+b−p≥b>0`/`a>0` 可推；正确；
* `log_submodular_of_measure`/`submodular_of_measure`：显式假设 `hadd : μ(A∪B)=μA+μB−μ(A∩B)`（Real 形式）与 `hinter_pos/hinter_le`；
  **没有把 measure 加性当已证**，GAP-MEAS-ADD 明标；
* 无目标假设；纯 measure/real 代数；无循环；
* 作为条件工具 **PASS**（但 GAP-MEAS-ADD 未消，不能当无条件 measure 定理）。

## 4. 判定汇总

| 文件 | 判定 | 说明 |
|---|---|---|
| `Mzk1StructuralTargetActual` | **PARTIAL** | 条件定理正确；抽象结构可平凡满足（q=θ/G=id），existence=GAP 标注不精确 |
| `Mzk1ThetaSectionActual` | **PARTIAL/EMPTY** | deg 已修；`arch_source/finite_source` UNLINKED、section/prod 任意 Prop；对象空洞可满足 |
| `Mzk1LogMeasureSubmodularActual` | **PASS（条件工具）** | real 核心正确；measure 版显式 `hadd` 假设；无循环 |
| 循环性 | **无 CIRCULAR** | 三文件均未假设目标；问题为条件/空占位 |

## 5. 修正建议

1. StructuralTarget：
   * 增加 strict/non-vacuity 字段：`qRegion ≠ θRegion` 或 `μ qRegion < μ θRegion`；
   * 绑定 actual `thetaHullRegion`/`qPilotRegion`（S2807/S2717）或明确标“abstract interface”；
   * 把 GAP-XID 改为 “actual instantiation GAP”，不要写 “no inhabitant”。
2. ThetaSection：
   * 把 `arch_source : Prop` 改为真实等式字段（如 `arch_bound = sum_sigma log‖theSection‖`）并提供证明或显式 GAP；
   * 把 `finite_source : Prop` 改为 `finite_index = sum_p log#(...)`；
   * 把 `section_nonzero`/`section_eq_prod` 改为真实定理/等式（或删除），增加 `nC>0`、theta 点、乘积关系；
   * 补 `degree` 与 `globalLogVolume det−q` 的 bridge；
   * 修 header：green 只是算术模板，非对象构造。
3. LogMeasure：保留 `hadd` 条件；下一步从 `measure_union_add_inter` 移植 Real 形式（需有限性/无 top），消 GAP-MEAS-ADD；
4. 所有文件 gate/olean 由 mainline 汇总；本审计不编译；green 仅表示条件定理 kernel 通过，不等于对象存在/目标已证。