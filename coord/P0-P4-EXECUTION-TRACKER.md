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

## 里程碑验收（按 P7-GAP-ATTACK-PLAN §4，Lead 维护）

| 里程碑 | 完成后应满足 | 当前 |
|---|---|---|
| P0（native 源接回） | native 输入（T,b,p,places,tuple）→ core（roots 代数闭包/qVFamily/qVFamTensor*）→ readout/tensor consumer 的端到端链可编译；旧 C3 消费者有 native 替代或精确不可替代清单；无 IsEmpty 消去 | WIP：core/readout/consumer/L-side 四组文件在编 |
| P1（B5 生成元/count） | `localizedLine I v = span O_v {generator}`、`localValuation v generator = -countExponent v I` 至少其一真证；否则单一精确缺失引理；含 f_v 的 B5 输出 | WIP：mainline span/ideal/count 三 statement 文件 + shehdd IsPrincipal/generator 文件在编 |
| P2（R1.2 一个真实标签块） | 选实际 (p,tuple,label) 写出 `g^q_a = Σ c_ia g^θ_i` 的完整展开，展示四来源（源 q/源 θ/落点/权重）；系数整性证成（单生成元/纯张量/有限和已 green，完整版待） | WIP：abc R1.2 两文件 green；四来源完整展开待 |
| P2（R1.3 质量差） | `R_exact = Σd_b(log‖λ‖−log‖qhat‖) = −Σd_b log‖c_b‖ ≥ 0`，并与 c0RemainderV2 的 correction 对齐（不假设相等） | WIP：Mzk1P2RelativeMassActual 在编 |
| P3（迹下降） | (R3.1)/(R3.6)/(R3.7) 的映射/系数/指数可编译，且给出净量非负的第一步实际计算 | WIP：stage4 P3 6 文件在编（TraceDualityCoefficient 已 green） |
| P4（闭合） | 从原合格输入内部构造全部对象，接回原 q/Theta 目标并完整验收（target_accepted） | 未开始；P0-P3 完成前不做 |

纪律：里程碑报告由 owner 一次发出；Lead 不逐文件/逐错误指挥。
## 批量完成日志（Lead 汇总，2026-11-13 23:22）

- P3（stage4）六文件全 green：TensorCore/TensorCoreNormalized/TensorCoreHaar/DomainDecompositionMap/TraceDualityCoefficient/ExponentNet（core p-scaling 缺口已记录）。
- #10/P1（lattice）六文件全 green：NativeUnitMassOne/NativeBlockEquivCandidate/P1FinitePlaceFv/P1LocalUnitProductT/P3HaarScaleDocking/P1CountLocalValuationNative。
- P1（mainline）六文件全 green：LocalizedSpan/IdealLocalizedCount/PrincipalValuation/R21Bridge/B5WithFv/ContractMapEvidenceRows（精确缺口各一）。
- P1/B5（shehdd）六文件全 green：LocalizedIsPrincipal/LocalGeneratorFromIsPrincipal/GeneratorNonzero/PlaceVolumeSign/B5AssemblyNoHproduct/Ob33B5RowsFinal。
- P2（abc）：LabelBlockCoefficient、LabelBlockSum、RelativeMass（R1.3）green；R13vsC0/LabelBlockComplete/QNativeSourceArrow/ThetaAllowedImage/WeightedSum 在修。
- P2（qpilot）：NativeTensorConsumer、DetCoefficient green；DetWeightedNonneg/TensorPairing/ProductFormulaCancel/PureTensorExpansion/NativeConsumerP2 在修。
- P0（hull）：NativeSourceCore、NativeTensorLanding、MigrationRows、NativeEquiv green；NativeReadout/NativeS3137Chain 在修。
- P0-L（stepxi）：S3137LReadout green；LPaperInstance/LReadoutInstance/LQThetaArrow/LRegionMass/LSourceIdent/LSignedLog 在修。
