# LeanFormal 索引

用途：项目核心正式化（IUT/ABCBridge/IUTII/IUTIII/Foundations）。

## 入口
- 核心：`LeanFormal/IUT/`
  - `Foundations/LocalFields/`：local field / completion / unit logarithm / norm；
  - `ABCBridge/Geometry/`：算术桥、tensor、Haar；
  - `IUTII/`、`IUTIII/`：IUT 结构；
- 总索引：`../coord/LEAN-INDEX.md`；
- 大审计：`../coord/P7-GATE-REVIEW.md`、`../AUDIT_LEDGER.md`。

## 重要 donor
- `LeanFormal/IUT/Foundations/LocalFields/IntegralUnitLogarithm.lean`：`integralUnitExponent` 已重定义为 quotient card；
- `LeanFormal/IUT/Foundations/LocalFields/FinitePlaceCompletionNormTransport.lean`：`norm = absNorm^v`、`logNorm_completionMap_eq_mul`；
- `LeanFormal/IUT/Foundations/LocalFields/PadicExpLog.lean`：`norm_log1p_le`；
- `LeanFormal/IUT/Foundations/LocalFields/FinitePadicTensorFieldDecomposition.lean`：只有 AlgEquiv+连续，无 isometry。

## 编译
只走 watchdog：把目标加到 `../dag/watchdog/extra-targets.txt`，等 `watchdog.log` DONE/FAIL。不要直接 `lake env lean`。
