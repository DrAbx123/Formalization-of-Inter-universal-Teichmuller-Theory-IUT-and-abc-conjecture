# NUMERICAL-WALL-PLAN — A490 NumericalWall 分工/审计（lattice 维护）

updated: 2026-11-11 05:28 (lattice audit; read-only)

## 0) 背景（Lead A490）

LANA 生态（`tmp/sheaf/lana/iut/Iut`）把显式 ABC 归约到 `Iut.Wall.NumericalWall`：
- `Iut/Wall/EtaAlg.lean`: `wall_iff_forall`、`exists_out_of_wall`、`cor312VariantHolds_of_wall`、`classicalABC_of_wall`；
- `Iut/Wall/Checks.lean`: `def NumericalWall := ∃ U, IsAdelic D U ∧ InHullOfImage D U ∧ (qVal D.bpsDegrees).eta (logVol D U) = etaQ D`；`numericalWall_iff : NumericalWall D ↔ Corollary312Variant (concreteVariantData D)`；`numericalWall_iff_rss : NumericalWall D ↔ ∃ (U) (hU : IsAdelic D U), InHullOfImage D U ∧ Rss.mk D U hU = (rssEquiv D).symm (concreteVariantData D).qPilot.lhs`；
- `Iut/Wall/Rss.lean`: `etaQ`、`logVol_etaQ_pilot`、`etaQ_bijective` 及体积计算引理；
- `Iut/Wall/{Constraints,MultiConstraints,MultiContainer,Pilots,QPilotRegion,Scaling,IdentifiedCopies}.lean`：SHE/IPL/APT、q-pilot region、scaling 等。

## 1) 5 项交付文件与审计状态（Lead A490 澄清后）

| # | 文件 | owner | 角色 | imports LANA | sorry/True | olean | 字段/证明审计 |
|---|---|---|---|---|---|---|---|
| ① | `tmp/sheaf/xif/paper/A490WallNumericalAlignmentActual.lean` | abc | `numericalWall_of_wall : Wall D A → NumericalWall D`；`corollary312Variant_of_wall`（经 `numericalWall_iff`） | `Iut.Wall.Checks` ✓ | 0 | 待编译 | **字段对应 NumericalWall 定义 ✓**：`exists_out_of_wall` 给 `⟨U, IsAdelic, InHullOfImage, logVol=qPilot.lhs⟩`，第 4 槽 `rw [hVol]; unfold etaQ`；`Corollary312Variant` 用 `numericalWall_iff.mp`。 |
| ② | `tmp/sheaf/xif/paper/A490WallThetaShiftAlignmentActual.lean` | abc | `wall_thetaShift_logVol`（wall+ThetaShift ⇒ ∃Ind3，`-s|log q|+logVol(S)=qPilot.lhs`）；`wall_region_logVol_eq_qPilot` | `Iut.Wall.MultiContainer`（仅） | 0 | 待编译 | **间接输入，未直接给 Rss 等式**：用 `wall_iff_forall`/`etaAnab_eq_etaQ_iff`/`A.ThetaShift`；风险: 仅 import MultiContainer 却用 `sFactor/nC/logVol/lgp`，import 闭包待日志核实。 |
| ③ | `tmp/sheaf/xif/paper/Mzk1LANAQPilotWallRegionActual.lean` | qpilot | q-pilot region/scale 显式数据 + `numericalWall_iff_rss_qPilotScale`（Rss 字段写成 `symm(-qPilotScale)`） | `Iut.Wall.{QPilotRegion,Pilots,Checks}` ✓ | 0 | 待编译 | **字段对应 numericalWall_iff_rss ✓**：`Rss.mk D U hU = symm(-qPilotScale D)` 经 `qPilot_lhs_eq_neg_scale` 等价；`QPilotRegionWallData` 由 `logVol_qRegion` 等支撑。 |
| ④ | `tmp/sheaf/lana/iut/Iut/Wall/NumericalWallHullActual.lean` | hull | hull 侧归约：`hullActual_numericalWall_iff_exists_logVol : NumericalWall D ↔ ∃U, IsAdelic∧InHullOfImage∧logVol=qPilot.lhs`；archScale 构造 `hullActual_exists_adelic_inHullOfImage_logVol` 等 | `Iut.Wall.IdentifiedCopies` ✓ | 0 | 待编译 | **与 numericalWall_iff_rss 字段一一对应 ✓**：把 eta 等式化为 logVol 等式；archScale 的 lambda*O 保持 InHullOfImage、logVol 加 log t；依赖 LANA `thetaImage_isAdmissible`/`InImage.inHullOfImage`/`isAdmissible_hullOf`/`logVol_archScale`/`rhs_eq_logVol_image`/`isAdelic_archScale`。 |
| ⑤ | `tmp/sheaf/lana/iut/Iut/Wall/NumericalWallActual.lean` | mainline | **已创建（A491 审计）**: `NumericalWallInput := qPilot.lhs ≤ rhsData.rhs`；`numericalWall_iff_rhs_ge_lhs`、`numericalWallInput_iff`、`numericalWallInput_iff_variant` 与 `numericalWall_holds_of_qPilotRegion_inHull`(sufficient-only)、`qPilotRegionInHull_implies_input` | ④ hull + ③ QPilot + Checks | 0 | 待编译 | **显式 named 缺口**: input 恰是 Cor 3.12 variant 的实不等式本身；与 NumericalWall/variant 均等价但未证明；无 hidden axiom/True；不构成 NumericalWall 的证明。详见 `coord/FAITHFULNESS-AUDIT-A491.md`。 |

辅助（非 5 项，mainline 已写）: `tmp/sheaf/lana/iut/Iut/Wall/NumericalWallRssActual.lean` — Rss 等式桥: `rss_mk_eq_symm_qPilotLhs_of_logVol`、`rss_mk_qRegion_eq_symm_qPilotLhs`、`rss_mk_archScale_eq_symm_qPilotLhs_of_logVol`、`numericalWall_of_adelicHull_logVol`（用 `numericalWall_iff_rss.mpr`）；imports Checks+QPilotRegion ✓，0 sorry，待编译。该文件可直接支撑 ⑤ 的 Rss 侧。

## 2) 与 `numericalWall_iff_rss` 的字段对应（审计口径）

| RHS 字段 | ① WallNumerical | ② ThetaShift | ③ QPilotWallRegion | ④ HullActual | ⑤ NumericalWallActual |
|---|---|---|---|---|---|
| `∃ U : Region D` | `exists_out_of_wall` | `A.out ι S` | `qRegion D` | `hullOf D (thetaImage D l)` / archScale | 待写（用 ④ 的存在性） |
| `hU : IsAdelic D U` | `(A.realisation ι S).1` | `(A.realisation ι S).1` | `isAdelic_qRegion` | `isAdmissible_hullOf` / `isAdelic_archScale` | 待写（取 ④ 字段） |
| `InHullOfImage D U` | `(A.realisation ι S).2` | `(A.realisation ι S).2` | 输入保留（③ 不直接证） | `hullActual_*_inHullOfImage` / archScale 保持 | 待写 |
| `Rss.mk D U hU = symm(qPilot.lhs)` | 未直接给；LANA `numericalWall_iff_rss` 承担 eta↔Rss 等价 | 未直接给（logVol 等式可作输入） | `numericalWall_iff_rss_qPilotScale`（symm(-scale)） | `hullActual_numericalWall_iff_exists_logVol`（把 eta 换 logVol） | **待写：④+③/RssActual 组合** |

## 3) 当前风险/待办

1. ①–④ 源码齐全、0 sorry、均入 extra-targets，但**全部暂无 olean**（watchdog 待编译）；编译后按日志修 4.32.0→4.32.2 差异。
2. ② 仅 import `Wall.MultiContainer`，使用 `sFactor/nC/logVol/lgp` 等，需确认 import 闭包；若不闭，补 import（owner abc）。
3. ⑤ mainline `NumericalWallActual` 已创建（A491 审计）：input=目标不等式本身，等价但不证明 NumericalWall；详见 `coord/FAITHFULNESS-AUDIT-A491.md`。
4. ④ 在 `tmp/sheaf/lana/...` 而 ③/⑤ 在 xif：注意 import 路径为 `tmp.sheaf.lana.iut...`，且 LANA 目录文件纳入 queue 后由 watchdog 编译。
5. value-model 结论不得作 rung（F2 规则不变）；本计划全部基于 LANA literal/explicit 对象。

## 4) 维护说明

- 本文件由 lattice 维护（只读审计 + 状态表）；不修改他人组件。每次 watchdog 出 olean/FAIL 后更新 olean 列与风险。
- 交叉引用: `coord/INTEGRATION-A486.md`（接线）、`coord/GAP-CONSTRUCTIBILITY-A483.md`（rung 可构造性）、`coord/A486-WIRING-AUDIT-shehdd.md`。

## 5) A491 保真审计结论（`coord/FAITHFULNESS-AUDIT-A491.md`）

- **NumericalWall D 未被证明**；所有相关定理是等价/重述/条件蕴含（numericalWall_iff、_iff_rss、_iff_rhs_ge_lhs、Wall⇒、ThetaShift⇒、InHullOfImage(qPilotRegion)⇒）。
- **NumericalWallInput（`qPilot.lhs ≤ rhsData.rhs`）是显式 named 缺口**：等于 Cor 3.12 variant 实不等式，已定义并与 wall/variant 证等价，但未证明；非 hidden axiom/True。
- 各项判定: ValBPS C ①（value-level）/④（paper 实际值群）；localPilot/pilot ④；EtaAlg ④ interface（T1 ③、T2 ①、T3 ②）；concreteVariantData ①；Rss/rssEquiv ④ modelling、etaQ/qPilot.lhs ①；桥接 ③/④ 忠实归约、①② 假设强度问题、⑤ named 缺口；6 桥接文件无 True/PUnit/IsTrivial/trivialAlg。


## 6) A496 归档：LANA 仅参考，NumericalWall 路线停止

- A491/A495 审计后，LANA `Wall`/`NumericalWall` 不再作为接线/目标（简化/过强/2ℓ 归一化差/True toy 模型）。
- LANA 文件已移出 watchdog 队列（2026-11-11，queue lana-lines=0），磁盘保留 reference-only。
- `NumericalWall` 记为 named gap（非 obstruction）；本计划转入只读历史，不再新增 A490 LANA 接线文件。
- 主链回归见 `coord/MAIN-CHAIN-AUDIT-A496.md`；权威对象/陈述为我们自己的 `step3115_comparison_proved`、shared `FourTriangleSynthesis`、`Cor312Conclusion`、`r4_literal_assembly`/`r4_endgame_composition`。

