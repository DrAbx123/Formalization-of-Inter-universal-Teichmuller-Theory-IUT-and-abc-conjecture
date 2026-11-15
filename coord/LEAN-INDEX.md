# Lean 证明总索引（大审计入口）

更新：2026-11-15 09:40（Asia/Shanghai）

## 0. 强制规则

1. **所有 Lean 编译只走 watchdog**：
   - 把目标 `.lean` 路径加入 `dag/watchdog/extra-targets.txt`；
   - 不要用 `lake env lean` 直接验证/生成 olean；
   - 用 `dag/watchdog/watchdog.log` 的 START/DONE/FAIL、`job_output` 和 `dag/watchdog/logs/` 看结果。
2. watchdog 入口：
   - 启动：`cmd /c tools/run_dag_watchdog.cmd`；
   - 目标白名单：`dag/watchdog/extra-targets.txt`；
   - 主日志：`dag/watchdog/watchdog.log`；
   - 单文件日志：`dag/watchdog/logs/<path with _>.log`；
   - 结果流水：`tmp/xif_guarded_results.log`。
3. 先查本索引再 grep，避免重复找 donor：
   - 大审计：`coord/P7-GATE-REVIEW.md`、`coord/R29-STATUS.md`、`AUDIT_LEDGER.md`；
   - 历史审计表：`coord/AUDIT-05-XIF-S2601-S3286.md` 等 `coord/AUDIT-*.md`。
4. 每个实际 Lean 根目录有 `_INDEX/README.md`；先进该目录的 `_INDEX` 再进子目录。

## 1. Lean 根目录地图

| 根目录 | 作用 | 活跃入口 |
|---|---|---|
| `LeanFormal/` | 项目核心定义与定理：IUT/ABCBridge/IUTII/IUTIII/Foundations | `LeanFormal/IUT/` |
| `tmp/` | 实际工作区；活跃正式化在 `tmp/sheaf/xif/paper` | `tmp/sheaf/xif/paper/` |
| `Iut/` | IUT 相关 port/归档；可作 donor，不是当前目标 | `Iut/_INDEX/README.md` |
| `LocalClassFieldTheory/` | local class field 理论 port | `_INDEX` |
| `tmp/local-cft-port/` | **已可直接 import 的 PadicField donor**：`PadicField.FieldNorm` | `PadicField/FieldNorm.lean` |
| `tmp/external/ported/` | 外部 port 源码/包 | `_INDEX` |
| `Pi1/` | pi1 相关 port | `_INDEX` |
| `Belyi/` | Belyi port | `_INDEX` |
| `WeilCurves/`、`CurvesJacobian/`、`EllipticCurves/`、`FormalSchemes/` | 代数几何/曲线 port | `_INDEX` |
| `Oka/`、`TemperedFundamentalGroups/`、`ContinuousKummerTheory/`、`TateCurvesTheta/`、`PadicLogVolume/` | 专题 port | `_INDEX` |

注意：`tmp` 下大量 `vendor_clone_*` / `vendor_clone_lcft` / 第三方 clone 只是参考副本，**不是活动目标**；只有 `tmp/sheaf`、`tmp/local-cft-port`、`tmp/external/ported` 是当前可复用区。

## 2. 当前活动主线（tmp/sheaf/xif/paper）

### 3.12 / abc
- 数据/比较：`Mzk1ActualRamifiedDataActual.lean`（actual_paper312 条件形）
- 主链：`Mzk1P0FinalS3137ConditionalActual` → `Mzk1P0FinalNoS45AssemblyActual` → `Mzk1P0FinalS3137DictionaryActual`
- 消费者：`Mzk1Cor312ToABCConsumerActual.lean`、`S3171IUTIVSection1DisplayActual.lean`、`Cor312ToABCBridgeInterface`

### IV Thm 1.10
- `Mzk1IVThm110Actual.lean`、`Mzk1IVThm110N5Actual`、`Mzk1IVThm110HCor312Actual`
- floor/unit region：`Mzk1IVThm110FloorUnitRegionActual`、`Mzk1IVThm110UnitRegionScalingActual`
- Galois/completion：`Mzk1GaloisCompletionActual`、`ProbeGaloisIsometryActual`、`Mzk1CompletionTowerActual`

### Principal units / residue
- `Mzk1IVThm110PrincipalUnitsResidueActual.lean`（9 decls，audit accepted）
- `Mzk1IVThm110CardExponentActual.lean`（integralUnitExponent/cardExponent/coprime）

### Norm valuation
- `NormalizedNormValuationResidueActual.lean`（条件；exponent=f）
- `tmp/sheaf/xif/paper/RelativeNormCompletion.lean`（实际 Algebra.norm）
- **直接可用 donor**：`tmp/local-cft-port/PadicField/FieldNorm.lean` 的 `PadicField.v_norm`

### unitLog norm（support-only，非关键路径）
- `Mzk1IVThm110UnitLogNormBoundActual`、`UnitLogNormQpActual`、`UnitLogNormQpTwoActual`、`UnitLogNormHalfActual`、`NormalizedCompletionUnitLogActual`
- 关键路径文件不引用这些：`Mzk1Cor312ToABCConsumerActual`/`S3171...`/`Mzk1IVThm110Actual` 中 unitLog 出现 0 次。

### 结构障碍/审计（不假装已证）
- `Mzk1HqHthetaStructuralObstructionActual.lean`
- `Mzk1IVThm110TensorUnitBallActual.lean`（placeholder，记录 contractive/isometry donor 缺失）

## 3. 当前最关键缺口（先查这里，别重证）

1. **R1 single-local q vs global sum**
   - `C3.q` 是单个 local field 元素，`signedQPilotLogVolume` 是单点 log；
   - 全局 q/除数/加权读数**已存在**：`S3133RealifiedQPilotDivisorActual.lean`、`S3133RealifiedQPilotLogVolumeActual.lean`、`S3133QPilotReadoutActual.lean`；
   - 缺的是把 `C3.q` 与 `S3133` 的 q_v 族/重数 `qVEffectiveMultiplicity` 对齐；不要重新构造 global q。
2. **hq 右端 actualFn 是 residue degree**，不含 q 消失阶；接线必须用 `qVEffectiveMultiplicity`/order 保留 q 重数。
3. **hθ**：region product / product Haar / log=Σlocal 仍缺；`LocalFieldProductHull` 有 subset/compactness 但无 equality。
4. **norm valuation**：`PadicField.v_norm` 已给正确公式（可直接 import）；缺 completion 侧 `Algebra ℚp`/tower/finite 实例与 canonical norm 归一化。
5. **IV stage4**：`UniformContinuous` 卡在 valueGroup iso；`withValMovedSigma_surjective` 已绿。
6. **tensor unit ball**：`FinitePadicTensorFieldDecomposition` 只有 AlgEquiv+连续，无 isometry/contractive norm。

## 4. 大审计/状态文档顺序

1. `coord/P7-GATE-REVIEW.md` — gate 表；
2. `coord/R29-STATUS.md` — Lead 日志；
3. `AUDIT_LEDGER.md` — 研究事实/失败路线；
4. `coord/AUDIT-05-XIF-S2601-S3286.md` — 历史文件/状态索引；
5. 本文件 — Lean 根目录 + 活动文件 + 缺口入口。

## 5. 已存在 donor（不要重造）

### 全局 q / 加权读数 / q 重数
- `tmp/sheaf/xif/paper/S3133RealifiedQPilotDivisorActual.lean`：
  - `qPilotRealifiedDivisor`；
  - `qVEffectiveMultiplicity`；
  - `mult_b = order(q_v(b)) * localResidueDegree`。
- `tmp/sheaf/xif/paper/S3133RealifiedQPilotLogVolumeActual.lean`：
  - `qPilotRealifiedLogVolume = -∑ mult_b * log(residueNormBase b)`。
- `tmp/sheaf/xif/paper/S3133QPilotReadoutActual.lean`：
  - `qPilotSignedReadoutAt`；
  - 加权读数 = `nativeQVPilotNormalizedSignedLogVolume`。
- `tmp/sheaf/xif/paper/S3133QPilotLogVolumeAgreementActual.lean`：
  - 多路读数一致性。
- **接线要求**：hq 右端不能只用 `actualFn`（residue degree）；必须保留 q 的消失阶/重数（`qVEffectiveMultiplicity` 或 `mult_b`）。

### 局部范数公式
- `tmp/local-cft-port/PadicField/FieldNorm.lean`：
  - `PadicField.v_norm`：`v p (Algebra.norm K x) = f p K L * v p x`；
  - `PadicField.nrm_norm`；
  - 已用 `import PadicField.FieldNorm` 验证可加载。
- 接 `NativeFCompletion/NativeBaseCompletionRaw` 需要 `Algebra ℚp`/tower/finite 实例和 canonical norm 归一化；不要重新从零证。

### tensor 有限域乘积分解 / 相对 Haar
- `LeanFormal/IUT/Foundations/LocalFields/FinitePadicEtaleTensorDecomposition.lean`：
  - `exists_finiteNormedFieldProduct_etaleTensor`。
- `LeanFormal/IUT/Foundations/LocalFields/FinitePadicTensorFieldDecomposition.lean`：
  - `exists_finiteNormedFieldProduct_piTensor`（AlgEquiv+连续，无 isometry）。
- `LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceIntegralTensorCovolume.lean`：
  - `arithmeticTupleLogTensorUnitLogVolume_eq_relativeHaarLog`。
- `LeanFormal/IUT/Foundations/LocalFields/FinitePadicHaarScaling.lean`、`FinitePlaceLogShellDiscrepancy.lean`：
  - Haar 推前/relative Haar log.

### 结构障碍文件（已有，不要重复找）
- `tmp/sheaf/xif/paper/Mzk1HqHthetaStructuralObstructionActual.lean`。
- `tmp/sheaf/xif/paper/Mzk1IVThm110TensorUnitBallActual.lean`（记录 contractive/isometry donor 缺）。

## 6. 当前路线修正（用户 2026-11-15 指令）

- **hq 右端必须保留实际 q 重数**：`actualFn` 只是 residue degree；q 的消失阶/多重要从 `qVEffectiveMultiplicity`/`qPilotRealifiedDivisor` 接。
- **θ hull 精确计算降级为单向界**：
  - 在真实 hull 内构造一个体积足够大的满格/lattice；
  - 只需证明 `full lattice volume ≤ hull volume`（或反向 sufficient bound）；
  - 不再要求精确整 θ hull 的等式。
  - 入口：`FinitePadicIntegerTensorLattice`、`tensorIntegerRegion`、`FinitePlaceIntegralTensorCovolume`、`LocalFieldProductHull.unitRegion`。

## 7. 最近 watchdog 结果（只信 watchdog）

- `Mzk1IVThm110SlackReductionActual`：START 01:38:28 → **DONE EXIT=0 01:40:23**（115s）；`thm110_slack_of_hCor312` kernel-closed。
  - 可将 S3171 的 `hSlack` 改为由 `hCor312` 推出（Lead 已批准；同步 S3171/Mzk1Cor312ToABCConsumerActual 等消费者）。
- watchdog 主进程：node PID 26324（2026-11-15 09:39:27 启动）；log 持续更新。

## 8. 接口变更记录

- 2026-11-15：批准 qpilot 把 `S3171IUTIVSection1DisplayActual.Thm110DisplayInputs.hSlack` 改为 derived（由 `hCor312` + `l≥7` + `d≥1` + nonneg 推出），保留结构兼容则加 `Thm110DisplayInputsOfCor312`；同步消费者。这是改我们的答案，不改 paper 对象。
