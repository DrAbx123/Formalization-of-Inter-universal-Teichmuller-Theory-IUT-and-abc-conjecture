# MESTRE-USE-DIRECTIVE（MO 输入可消费性判定）

日期：2026-11-14（mainline lane）。判定对象：当前活动缺口能否消费 Mestre–Oesterlé 外部输入。
MO 在本项目有**两个显式 Prop 版本**（均为 class-B 外部输入，不伪造证明）：

- **ABC 版** `LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorABCActual.MestreOesterleBound (logq logd C : ℝ) : Prop` := `logq ≤ 6 * logd + C`（Mzk1PrimeConductorABCActual.lean:32）；
- **素导子版** `LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorRouteActual.MestreOesterleBound : Prop` := `∀ C : PrimeConductorCurve, C.e ≤ 5 ∧ (37 < C.p → C.e ≤ 2)`（Mzk1PrimeConductorRouteActual.lean:54）。

## 判定表（当前活动缺口）

| 缺口 | 能否写成 MO 形状 | 判定 | 依据/精确理由 |
|---|---|---|---|
| `thetaR13Defect = 0` / `defect ≥ 0` | 否 | **NOT APPLICABLE** | defect := nativeLSideThetaReadout T b + p2WeightedDetLog T（Mzk1P0NativeThetaR13DefectActual.lean:18），是解析 readout 的恒等/符号，不是 log q ≤ 6 log d + C 或 e_p 界；无 log q/d 量纲。 |
| `NativeComparison` | 否 | **NOT APPLICABLE** | 对比 native L-side 与 paper 归一化读数（对象/归一化不匹配）；MO 只给判别式/导子型不等式，无法推出 readout 相等。 |
| `R21Bridge` | 否 | **NOT APPLICABLE** | 局部 DVR 生成元 valuation = count（局部分支）；MO 是全局算术不等式。 |
| `IdealLocalizedCount` | 否 | **NOT APPLICABLE** | `Ideal.map`/completionIdeal^count 局部理想论；MO 无关。 |
| residue-one（`localResidueDegree=1`） | 否 | **NOT APPLICABLE（但同属 paper 输入）** | MO 给 e_p≤5/2，不给 f_v=1；residue degree 是 tame/split 输入（来自 SourceReductionClause 等），不是 MO 推论。 |
| det-Haar 最后两步 | 否 | **NOT APPLICABLE** | Haar 测度 transport 因子/归一化（量纲为 measure），MO 不含测度信息。 |
| `P2ArchLogSourceIdentification` | 否 | **NOT APPLICABLE** | 存在 global f 使 `archimedeanLogNorm f = p2WeightedDetLog T`（Mzk1P2ArchLogSourceActual.lean:83）；解析 source 元素识别，非不等式。 |
| `R37R13` | **部分是** | **PARTIAL / 已在 P3 消费** | 其算术不等式形（log 差/e_p 界）正是 MO 形状；P3 链已用 `hMO : MestreOesterleBound` 得 `ssIneqExplicit_final`（Mzk1P3FinalAssemblyActual.lean:50）与 `C.e ≤ 5`（Mzk1P3DictDOrdInterfaceActual）。当前 `R37R13NativeMassIdentification` 本身是**质量等式**（Mzk1P3MassIdentificationActual.lean:59），非 MO 形状。 |
| `D_exact` 下界 | **是** | **CONSUMABLE，已接线** | `Mzk1DExactLowerActual` 已带 `(hMO : MestreOesterleBound)`（:74/:84），ABC 版形状直接消费。 |
| blockEquiv / unitMass | 否 | **NOT APPLICABLE** | C3LogShellTensorBlock ≃ S1902Carrier 的等变/测度数据；MO 无关。 |

## 结论

1. MO 在本项目中**已经被消费**：ABC 版用于 `D_exact` 下界与 P3 `ssIneqExplicit` 链；素导子版用于 `C.e ≤ 5`（class-B 显式 hMO）。不需要新的 `hMO` 接线来关闭剩余缺口。
2. 剩余活动缺口（thetaR13Defect/NativeComparison/R21Bridge/IdealLocalizedCount/residue-one/det-Haar/P2ArchLogSource/R37R13 mass identity/blockEquiv-unitMass）**均不属于 MO 形状**；它们分别是解析 readout 恒等、局部理想论/生成元、paper tame/split 输入、测度归一化和 source 元素识别。
3. 唯一“方向接近”的是 `R37R13` 的**不等式形**，但该形式已在 P3 链中消费；其 mass identity 形式不是 MO 推论。
4. 因此：不新增任何“用 MO 假证缺口”的接线；MO 维持 class-B 输入，判定表即为本条 directive 的交付。

## 现有 MO 消费者（已验证/引用）

- `Mzk1DExactLowerActual.lean:74/84`（hMO : MestreOesterleBound）；
- `Mzk1P3FinalAssemblyActual.lean:50` `ssIneqExplicit_final (hMO) (C)`；
- `Mzk1P3DictDOrdInterfaceActual.lean:30` `C.e ≤ 5` from hMO；
- `Mzk1P3DictDLogDiscBoundActual` / `Mzk1P3DictL7SSIneqArchActual` / `Mzk1L7ProofActual:102`：`ssIneqExplicit_of_L7 (hMO)`。

## 更正节（Lead 2026-11-14 02:15）：genuine MO vs normalized surrogate

**genuine MO = Zbl 0693.14004**：
- Thm 1：E/Q 半稳定 Weil 曲线，若 |Δ| 是 m 次幂，则 m ≤ 5 且 E 有 Q-有理 m-除点；
- Thm 2：素数导子 p ⇒（明确例外外）Δ = ±p。

**本项目 Lean 里的 `MestreOesterleBound` 不是原文定理**：
- `Mzk1PrimeConductorABCActual.MestreOesterleBound (logq logd C) := logq ≤ 6 * logd + C` 是
  **normalized surrogate**（Szpiro-6 形状，用于 P3/ssIneq 链）；
- `Mzk1PrimeConductorRouteActual.MestreOesterleBound := ∀ C, C.e ≤ 5 ∧ (37 < C.p → C.e ≤ 2)`
  是**打包的素导子指数形式**（同样不是原文 Thm 1/2 的直接陈述）。
- 因此 `Mzk1MestreUseWiringActual` 的 rows/docstring 已改为
  “normalized surrogate；genuine MO Thm 1/2 见 `coord/EXTERNAL-CITATIONS-20261114.md` §7”，
  **不声称**是原文定理的直接形式化。

判定表结论不变：剩余活动缺口均非 MO/surrogate 形状；MO/surrogate 已在 D_exact、P3 ssIneq、
`C.e ≤ 5` 处消费。
