# tmp/sheaf/xif/paper 索引（当前主工作区）

## 先看这里
- 总索引：`../../../coord/LEAN-INDEX.md`；
- gate：`../../../coord/P7-GATE-REVIEW.md`；
- Lead 日志：`../../../coord/R29-STATUS.md`；
- 研究审计：`../../../AUDIT_LEDGER.md`。

## 管线
- 3.12/abc：`Mzk1ActualRamifiedDataActual`、`Mzk1Cor312ToABCConsumerActual`、`S3171IUTIVSection1DisplayActual`、`Cor312ToABCBridgeInterface`；
- IV Thm 1.10：`Mzk1IVThm110*`、`Mzk1GaloisCompletionActual`、`Mzk1CompletionTowerActual`；
- Principal/residue：`Mzk1IVThm110PrincipalUnitsResidueActual`、`Mzk1IVThm110CardExponentActual`；
- norm valuation：`NormalizedNormValuationResidueActual`、`RelativeNormCompletion`、`NormalizedCompletionPadicBridgeActual`；
- unitLog（support-only）：`Mzk1IVThm110UnitLogNorm*`、`NormalizedCompletionUnitLogActual`；
- 结构障碍：`Mzk1HqHthetaStructuralObstructionActual`、`Mzk1IVThm110TensorUnitBallActual`。

## 缺口
见总索引第 3 节。特别：
- R1 全局 q donor 已在 `S3133RealifiedQPilotDivisorActual`/`S3133QPilotReadoutActual`，不要重造；
- norm valuation donor 在 `../../../local-cft-port/PadicField/FieldNorm.lean`；
- tensor unit ball 缺 contractive/isometry donor。

## 编译
只走 watchdog：目标加入 `../../../dag/watchdog/extra-targets.txt`，等 DONE/FAIL。不要直接 `lake env lean`。
