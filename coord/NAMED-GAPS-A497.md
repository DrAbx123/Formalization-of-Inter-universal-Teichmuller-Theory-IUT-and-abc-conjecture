# NAMED-GAPS-A497 — 我们 Cor312 链的真实缺口（A497 空转审计后）

updated: 2026-11-11 05:39 (lattice)

## 1) 真实 named 缺口（不得用空转 q≤target 替代）

| id | 缺口 | 现状/位置 | 需要 |
|---|---|---|---|
| `named-gap:hcomp-iut4-comparisons` | IUT IV §2 两条逐 ε 比较：`height_le_normalizedRegionVolume` 与 `regionVolume_le_normalizedWeight`（`hcomp`） | `Cor312ToABCBridgeInterface` 的显式 named input；`r4_literal_assembly`/`r4_endgame_composition` 接受但未构造 | 在 literal/actual 对象上写出两条 explicit/effective 比较 |
| `named-gap:independent-theta-pilot-readout` | 独立 Θ-pilot 读法：literal thetaPilot region / hull 的真实 log-volume | 当前 `thetaPilotLogImage := qPilotLogImage/(2ℓ)` 为空转定义（`Mzk1QPilotR4Stage5AlignActual:50`） | 定义 `thetaPilotReadout`（hull/thetaPilot region 真实 log-volume），证 `qPilotReadout ≤ thetaPilotReadout` |
| `named-gap:contract-provenance` | StepXIContract `qSigned/thetaSigned/targetSigned` 与 paper 对象的绑定 | `Contract.lean` 只含自由实数+字段，`target := theta`/`target_le_theta := rfl` 可自动满足 | 构造定理固定 q= q-pilot 体积、θ= Θ-pilot hull 体积，并给出两条比较 |
| `named-gap:literal-hull-finiteness` | literal hull log-volume 有限性 | `Mzk1LiteralIQHullFinitenessActual` olean=True（条件内容）；需与独立 θ 读法组合复核 | 复核读法独立性 |
| `named-gap:external-lana-reference` | LANA `NumericalWallInput` 等 | A496 归档 reference-only；不再接线 | 不进入本链 |

## 2) 空转禁用清单（VACUOUS，不计 3.12 进度）

- `Mzk1QPilotR4Stage5AlignActual`: `thetaPilotLogImage`、`qPilotLogImage_lt_thetaPilotLogImage`、`thetaPilotLogImage_neg`、`qThetaReadout_ordered`、`qThetaStepXIContract`、`qThetaFourTriangleSynthesis`、`cor312Conclusion_of_qThetaFourTriangle`、`qThetaHDD/qThetaDSC/qTheta_fourTriangleReadout`、qTheta volume 系列。
- `Mzk1Step3115ComparisonActual`: `qThetaHDD`、`step3115_comparison_proved`、`detReadout_twoL_mul_eq_hull`、`qThetaFourTriangleSynthesis`、`cor312Conclusion_of_qThetaSynthesis`。
- `Mzk1Step3115WiringActual`: `qTheta_r4_literal_assembly` 的 Cor312 分量、`Step3115WiringEvidence.qTheta_step3115_filled`/`step3115WiringEvidence`。
- `Mzk1QThetaHullDetAlignActual`: qTheta 对齐的 `qThetaReadout_ordered_iff_packetDet_mul_le_one`/`qThetaPacketDet_mul_q_le_one`（对被空转读法）。
- `cor312Conclusion_qThetaSynthesis`、`cor312Conclusion_qThetaHullDet`。

## 3) 仍可用的真实候选（条件/模型层）

- `Mzk1HullDetStep3115Actual.hullReadout`（packetLogVolume）/`detReadout`（-log|q|）/`hullReadout_le_detReadout_iff`（`packetDet*q≤1`）：真实数值比较；但 `HullDetState` 是抽象输入数据，未连接到 paper Θ-pilot region。
- `Mzk1R4LiteralAssemblyActual.r4_literal_assembly` / `Mzk1R4EndgameCompositionActual.r4_endgame_composition`：真实条件定理（hcomp 显式）；Cor312 分量须用非空转 S。
- `Mzk1LiteralIQHullFinitenessActual`、`Mzk1IUTIVStage5ABCFormActual`（Stage5 数值条件）、`Mzk1ExplicitABCWeakeningActual`（ExplicitABC⇒ABCConjecture）。
- `Mzk1FourTriangleSharedActual`：泛型结构可复用，但 `step3115_comparison` 必须由独立读法填充。

## 4) DAG-BLOCKED 登记（A497，lattice）

- CHAIN-BROKEN: `vacuity:qtheta-thetaPilotLogImage`、`vacuity:qthetaStepXIContract`、`vacuity:step3115_comparison_proved`、`vacuity:qThetaFourTriangleSynthesis`。
- OBSTRUCTION/named: `named-gap:hcomp-iut4-comparisons`、`named-gap:independent-theta-pilot-readout`。
- 结论: **空转声明不计入 3.12 进度**；真正的未证内容 = 独立 Θ 读法 + hcomp 两条 IUT IV 比较。

## A508 路线必要性分类（追加）

- `named-gap:hcomp-iut4-comparisons`: **ABC/height（Stage 5）**；非 3.12 前提（IUT IV §2；IUT III Cor3.12 proof 无 IUT IV 引用）。
- `named-gap:request-P-received-hull`: **ABC/height（IUT IV Thm1.10 Step(v)）**；非 3.12。
- `named-gap:takkun-hull-bound`: **ABC/height（IUT-IV Prop1.1–1.9 体积计算，Takkun 自述）**；非 paper 3.11.5 路线输入。
- PNT/Chebyshev（Section2 资产）：**ABC/height（Formalization Stage 5）**；非 3.12。
- `named-gap:independent-theta-pilot-readout`: **3.12 对象需求**（-|log Θ| 定义；4th △ HDD）。
- `named-gap:literal-hull-finiteness`: **3.12 必需**（-|log Θ| ∈ R；IUT III L10351/L10408-10411）。
- `named-gap:contract-provenance`: **neither**（我们 StepXIContract artifact，应重做/绕过，不属 paper 步骤）。
- `named-gap:takkun-containment`: **3.12 桥（若走 Takkun 路线）**；paper 路线用 HDD/SHE 4th △。
- `named-gap:external-lana-reference`: neither；`vacuity:qTheta-*`: neither（无效空转）。
- 详见 `coord/ROUTE-NECESSITY-A508.md` §7 与 DAG-BLOCKED meta a508_*。

