# HULLDET-OBJECT-RED-GAP — `HullDetObjectActual` 长期红：精确缺口与处理建议

日期：2026-11-13；hull lane。

## 状态

- 源文件：`tmp/sheaf/xif/paper/HullDetObjectActual.lean`（351 行）。
- watchdog 最近：FAIL EXIT=1（12:42:31Z）；无 olean。
- 该文件是 O6 hull+det 旧对象构造（A499/A501/A502/A509），不是当前 #3 OB33 的消费者。

## 首错（修复一半后仍红）

1. `:5` 传递依赖 `O2ThetaObjectActual.olean` 不存在（旧 API 链）。
2. `:63` `SourceNativeInitialThetaData` 显式 universe 使用错误（旧命名空间/实例漂移）。
3. `:164/:169/:328/:344` `qPilotLogVolume C3 P`：当前 `qPilotLogVolume` 是 `PaperQPilotObjectActual` 的读法，签名只剩 `P`；旧代码仍按 `(C3,P)` 调用。
4. `:193/:198` `literalIQHullLogVolume C3 n`：当前签名不接受 `C3` 显式参数（C3 是 section 隐式变量）。
5. `:190/:194/:331/:346` 缺实例 `(i : C3.tensorIndex) → Fintype (C3.tensorPlaceIndex i)`；当前 `SourcePilotRegionData` 只有 `tensorFintype`，没有逐 fiber 的 `Fintype` 字段。
6. `:258` `mem_integers_iff` rewrite 与 `↑(Integers ...)` coercion 不匹配（旧 Mathlib/notation）。

## 判定

- 不是数学 GAP，而是**旧 API/旧依赖链文件**；655 条错误绝大多数是第 1 条（缺 olean）与签名漂移级联。
- 要修等于按当前 API 重写整个文件（`qPilotLogVolume`/`literalIQHullLogVolume`/`globalIQ` 实例/Integers coercion），成本高且当前 #3 不需要它。
- **OB33 路径已绕过该文件**：`Mzk1Ob33SourceIdentificationActual`（GREEN 11:40:50Z）已用实际 det degree/unit line bundle identity 替代旧 HullDetObjectActual 的 O6 对象链；#3 不 import 它。

## 处理建议（不删除源码，保留历史）

1. 从 watchdog extra-targets 移除 `HullDetObjectActual`（以及同族 `HullDetObjectActualV2/V3` 如也在名单），标 **DEFERRED/obsolete**；不要为 red 统计强修。
2. 不删除源文件；在文件头加 `-- OBSOLETE: old API; OB33 path replaced by Mzk1Ob33SourceIdentificationActual`（若允许改旧文件）。
3. 若未来需要 O6 hull+det 对象，**新写** `Mzk1HullDetObjectActual.lean`，以当前 API 重述：
   - `qPilotLogVolume (P)`；
   - `literalIQHullLogVolume n`；
   - 显式 `[∀ i, Fintype (C3.tensorPlaceIndex i)]` 作为 named instance input；
   - `Integers` membership 用当前 lemma。
4. consumer 审计：Lean 源码中无 `import HullDetObjectActual`（只有 coord 文档引用）；删除/移出名单不影响任何 green 文件。
