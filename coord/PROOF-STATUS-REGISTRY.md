# proof/status 文件登记（避免 status 污染 proof 比，2026-11-14 Lead）

## 规则
- **proof file**：含至少 1 个实质性新定理/构造（能缩小/关闭某个具体缺口）。
- **status/aux file**：`List String` / `Prop` 行表、精确缺失清单、迁移/审计表；不算实质进展。
- 每波 proof:status 建议 ≥4:1（status ≤20%）；status 文件集中登记于此，不参与“新 green”计数（但 olean 仍由 watchdog 正常产出）。
- 已确认冗余/被取代的 status 文件可从 `dag/watchdog/extra-targets.txt` 移除（保留源文件作历史）。

## 已登记 status/aux 文件（截至 2026-11-14 04:20）

| 文件 | 内容 | 来源 lane |
|---|---|---|
| Mzk1P0LSourceRowsActual | L 状态行 | stepxi |
| Mzk1P0LNormalizationFactorActual | factor 定义/gap | stepxi |
| Mzk1P0LRegionOpenActual | open 条件/gap | stepxi |
| Mzk1P0LSignedLogFinalActual | signed log 状态 | stepxi |
| Mzk1P1R21BridgeProofActual | R21 状态行（真证另立） | mainline |
| Mzk1P1CountValuationSummaryActual | P1 summary rows | mainline |
| Mzk1P1ResidueOneActual | residue-one 状态 | mainline |
| Mzk1P1IsPrincipalInstanceRowsActual | instance rows | shehdd |
| Mzk1P7ContractMapEvidenceFinalActual | #8 evidence rows | mainline |
| Mzk1P2DetHaarActual | det-Haar gap 清单 | qpilot |
| Mzk1P2NativeProductEquivActual | product equiv 状态 | qpilot |
| Mzk1P2TensorProductIsometryActual | isometry 状态 | qpilot |
| Mzk1GapDetHaarSNFActual | SNF 步骤状态 | qpilot |
| Mzk1GapDetHaarScalarActual | scalar 步骤状态 | qpilot |
| Mzk1GapDetHaarGLInvarianceActual | GL 不变步骤状态 | qpilot |
| Mzk1GapDetHaarDiagonalActual | diag 步骤状态 | qpilot |
| Mzk1GapDetHaarFinalActual | det-Haar 组装状态 | qpilot |
| Mzk1GapDualTransposeActual | dual transpose 状态 | qpilot |
| Mzk1P2Route2SummaryActual | 路线二 summary | qpilot |
| Mzk1P3SummaryRowsActual | P3 summary | stage4 |
| Mzk1P3TensorCoreScalingConsistencyActual | C3 一致性 blocker | stage4 |
| Mzk1P3NetGainSourceGapActual | net 负例/gap（含真例） | stage4 |
| Mzk1NativeUnitMassNormalizedFactorActual | unitMass 因子状态 | lattice |
| Mzk1UnitMassRowsActual | #10 rows | lattice |
| Mzk1BlockEquivFiberActual | fiber 状态 | lattice |
| Mzk1BlockEquivCandidateActual | candidate 清单 | lattice |
| Mzk1BlockEquivInhabitantAttemptActual | inhabitant 尝试状态 | lattice |
| Mzk1NativeBadPrimeDataSourceActual | bad prime 来源状态 | lattice |
| Mzk1NativeBadModuliFixedPrimeAttemptActual | fixed prime 尝试状态 | lattice |
| Mzk1BlockEquivDegreeFactorActual | degree factor 状态 | lattice |
| Mzk1BlockEquivNextStepsActual | next steps rows | lattice |
| Mzk1RootExtensionTensorRowsActual | tensor rows | lattice |

## 说明
- 登记基于 Lead 抽检与 lane 自报；`proof` 文件不在此表。
- 若某 status 文件后来补上实质定理，移到 proof（改名/备注）。
