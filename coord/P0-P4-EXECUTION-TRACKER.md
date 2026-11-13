# P0–P4 批量执行追踪（2026-11-13 晚，R29 之后）

背景：`S1429CompletionRootObstructionActual.sourcePilotRegionData_isEmpty` 证明旧 C3 类型为空；旧 C3 参数一切“actual”结论 = vacuous/historical。按 `P7-GAP-ATTACK-PLAN` §0/§4 迁移到 native 源（P0），再 P1/P2/P3。

## 批量包（每 lane 6 文件，先写后统一等待编译）

| owner | 文件 | 内容 | 状态 |
|---|---|---|---|
| hull | Mzk1P0NativeSourceCoreActual | native source core（qVFamily/C3Roots/qVFamTensor*） | 修红中（binder/instance） |
| hull | Mzk1P0NativeReadoutActual | core→qRead/thetaRead 实际读数 | 待写/编 |
| hull | Mzk1P0NativeS3137ChainActual | S3137 L-side 消费 native core | 待写/编 |
| hull | Mzk1P0NativeTensorLandingActual | native tensor landing | 待写/编 |
| hull | Mzk1P0MigrationRowsActual | 迁移行表（43/100/13/5） | 待写/编 |
| hull | Mzk1P0NativeEquivActual | 可迁移字段投影/Equiv | 待写/编 |
| mainline | Mzk1P1LocalizedSpanActual | localizedLine(span x)=span{algebraMap x} | 待写/编 |
| mainline | Mzk1P1IdealLocalizedCountActual | localizedLine I v = maxIdeal^count | 待写/编 |
| mainline | Mzk1P1PrincipalValuationActual | count_v(span a)↔localValuation | 待写/编 |
| mainline | Mzk1P1R21BridgeActual | R21Bridge 实例 | 待写/编 |
| mainline | Mzk1P1B5WithFvActual | 含 f_v 的 B5 输出 | 待写/编 |
| mainline | Mzk1P7ContractMapEvidenceRowsActual | #8 行升级 | 待写/编 |
| shehdd | Mzk1P1LocalizedIsPrincipalActual | IsPrincipal 构造/缺失 | 待写/编 |
| shehdd | Mzk1P1LocalGeneratorFromIsPrincipalActual | LocalGeneratorData | 待写/编 |
| shehdd | Mzk1P1GeneratorNonzeroActual | generator≠0/hH hO | 待写/编 |
| shehdd | Mzk1P1PlaceVolumeSignActual | placeLogVolume 符号 | 待写/编 |
| shehdd | Mzk1B5AssemblyNoHproductAttemptActual | 去 hproduct 尝试 | 待写/编 |
| shehdd | Mzk1Ob33B5RowsFinalActual | B5 ② 状态行 | 待写/编 |
| abc | Mzk1P2LabelBlockCoefficientActual | R1.2 秩一/纯张量 | **DONE 14:54:36Z** |
| abc | Mzk1P2LabelBlockSumActual | R1.2 多标签有限和 | **DONE 14:59:39Z** |
| abc | Mzk1P2RelativeMassActual | R1.3 相对质量差非负 + correction | 在编（文件已入队） |
| abc | Mzk1P2R13vsC0RemainderActual | R_exact vs c0RemainderV2 | 待写/编 |
| abc | Mzk1P2LabelBlockCompleteActual | 四来源完整展开 | 待写/编 |
| abc | Mzk1P2QNativeSourceArrowActual | native q→根扩张→qhat | 待写/编 |
| abc | Mzk1P2ThetaAllowedImageActual | theta 允许像→λ | 待写/编 |
| abc | Mzk1P2WeightedSumActual | 标签加权和↔R1.3 | 待写/编 |
| qpilot | Mzk1P0NativeTensorConsumerActual | native tensor consumer | **DONE 14:59:15Z（ole 391,120B）** |
| qpilot | Mzk1P2DetCoefficientActual | 纯张量 det/norm | 待写/编 |
| qpilot | Mzk1P2DetWeightedNonnegActual | 加权 det 非负 | 待写/编 |
| qpilot | Mzk1P2TensorPairingActual | det 配对+product formula | 待写/编 |
| qpilot | Mzk1P0NativeConsumerP2Actual | P0 consumer×P2 系数 | 待写/编 |
| qpilot | Mzk1P2ProductFormulaCancelActual | arch=count 消去 | 待写/编 |
| qpilot | Mzk1P2PureTensorExpansionActual | 纯张量→有限和 | 待写/编 |
| stage4 | Mzk1P3TensorCoreActual | core（无 C3） | 重写待编（universe/instance 已修） |
| stage4 | Mzk1P3TensorCoreNormalizedActual | normalized/p-scaling | 待写/编 |
| stage4 | Mzk1P3TensorCoreHaarActual | per-block Haar/紧性 | 待写/编 |
| stage4 | Mzk1P3DomainDecompositionMapActual | (R3.1) | 待写/编 |
| stage4 | Mzk1P3TraceDualityCoefficientActual | (R3.6) | 待写/编 |
| stage4 | Mzk1P3ExponentNetActual | (R3.7) | 待写/编 |
| lattice | Mzk1NativeFinitePlaceDictionaryActual | native 有限位字典 | **DONE 14:58:15Z（ole 121,504B）** |
| lattice | Mzk1NativeUnitMassOneActual | unitMass=1 尝试 | 待写/编 |
| lattice | Mzk1NativeBlockEquivCandidateActual | native blockEquiv 候选 | 待写/编 |
| lattice | Mzk1P1FinitePlaceFvActual | f_v/local degree | 待写/编 |
| lattice | Mzk1P1LocalUnitProductTActual | T-specific product | 待写/编 |
| lattice | Mzk1P3HaarScaleDockingActual | HaarScale↔native block | 待写/编 |
| lattice | Mzk1P1CountLocalValuationNativeActual | native count↔valuation | 待写/编 |
| stepxi | Mzk1S3137LReadoutActual | L q/θ readout | **DONE 15:01:52Z（55s）** |
| stepxi | Mzk1P0LPaperInstanceActual | LPaper312 实例 | 修红（import/open LQThetaSourceArrow） |
| stepxi | Mzk1P0LReadoutInstanceActual | L 实例 qRead/thetaRead | 待写/编 |
| stepxi | Mzk1P0LQThetaArrowActual | LQThetaSourceArrow 字段 | 待写/编 |
| stepxi | Mzk1P0LRegionMassActual | L region 质量 | 待写/编 |
| stepxi | Mzk1P0LSourceIdentActual | L 源识别 | 待写/编 |
| stepxi | Mzk1P0LSignedLogActual | signed log 约定 | 待写/编 |

## 纪律
- 旧 C3 空类型：不得用 `IsEmpty.elim` 冒充比较；旧 C3 green 只作 historical。
- 每个文件须：实际对象/定理、无 sorry/axiom、缺口精确命名。
- 批量结束统一由 Lead 加入 watchdog（`dag/watchdog/extra-targets.txt`）并统一等待；单文件不单独等待。
