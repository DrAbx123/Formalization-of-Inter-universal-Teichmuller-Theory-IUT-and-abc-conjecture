# A496 决定：以我们自己的对象为准，LANA 仅作参考（不再接线）

## 依据（A491/A495 审计）
- LANA `ValBPS` 是 1 维实线 value-level 抽象，`localPilot` 任意非零向量，非 p-adic 构造；
- `EtaAlg` 是 opaque interface（Steps 1–9 未实现），T1 过弱、T3 过强（已把 adelic+hull 结论塞进假设）；
- `Rss/rssEquiv` 是 modelling choice（按 log-volume 相等商、直接等同 ℝ）；
- LANA `variant ≠ published Cor 3.12`；`rhs` 是 procession 平均（sFactor），与我们 native 读法差 2ℓ 归一化；
- 其 `True` toy 模型（`Adelic := True` 等 7 处）不能作证据。

## 决定
1. **停止**把 `NumericalWall`/`Wall`/LANA `rhs` 当 rung 或目标；`lana:Iut.Wall.NumericalWall` 保留为 named gap（非 obstruction）。
2. LANA 移植文件**移出编译队列**，仅保留磁盘作源码参考（需要时再单文件读）。
3. 3.12 以**我们自己的对象与陈述**为准：
   - 权威比较：`Mzk1Step3115ComparisonActual` 的 `step3115_comparison_proved`（q/Θ 双像读法 hull/det 比较）；
   - 权威结论：`FourTriangleSynthesis` → `cor312Conclusion_of_fourTriangleSynthesis` → `Cor312Conclusion`；
   - ABC 方向：`r4_literal_assembly`/`r4_endgame_composition`（条件于我们的 `hcomp` 显式 named 输入）。
4. 团队工作回到我们自己文件：Step3115 链、R4/endgame、A482b/literal hcomp、P1/f4b、ExpEst02 Class B。
5. LANA 的 Chebyshev/PNT 证书仅作写法参考；若使用，只引用其定理名与证明思路，不把其对象当源对象。

## A496 执行状态（lattice，2026-11-11 05:35）

- LANA 移出队列已核验: `dag/watchdog/extra-targets.txt` = 466 条，其中 `tmp/sheaf/lana` 0 条；LANA 文件保留磁盘 reference-only。
- 主链回归审计: `coord/MAIN-CHAIN-AUDIT-A496.md`。当前 green: `Mzk1FourTriangleSharedActual`、`Mzk1R4LiteralAssemblyActual`、`Mzk1R4EndgameCompositionActual`、`Mzk1HullDetStep3115Actual`；无 olean: `HullDetFourTriangle`（源码已完成，待 plan 重编）、`Step3115Comparison`、`Step3115Wiring`、`QThetaHullDetAlign`（qpilot 已按 shared B 新 API 修补，待前置 olean）。
- 主链 9 文件无 LANA import、无代码级 sorry/True/axiom；`Mzk1QPilotR4Stage5AlignActual` olean stale（src 05:24 > olean 04:59），需重编后才算 gate 证据。
- 权威链保持: `step3115_comparison_proved` → shared `FourTriangleSynthesis` → `cor312Conclusion_of_fourTriangleSynthesis` → `Cor312Conclusion`；`r4_literal_assembly`/`r4_endgame_composition` 为 ABC 方向（条件于我们的 `hcomp` 显式输入）。


## A497 执行状态：qTheta 链标 VOID（空转）

- A497 vacuity 审计（`coord/VACUITY-AUDIT-A497.md`）确认 `thetaPilotLogImage := qPilotLogImage/(2ℓ)` 导致 qTheta/step3115 链空转；`step3115_comparison_proved`、`qThetaFourTriangleSynthesis`、`cor312Conclusion_qTheta*`、`qTheta_r4_literal_assembly` 的 Cor312 分量 **不构成 3.12 证据**。
- 真实 named 缺口: `coord/NAMED-GAPS-A497.md`（hcomp 两条 IUT IV 比较；独立 Θ-pilot 读法；contract provenance）。`DAG-BLOCKED.json` 已登记 4 条 CHAIN-BROKEN + 2 条 named gap。
- 后续主链审计只把条件/模型候选（`HullDetStep3115` 真实数值比较、R4/endgame 的 hcomp 条件、literal hull finiteness、ExplicitABC 收口）当候选；qTheta 链一律标 VOID，不计进度。

