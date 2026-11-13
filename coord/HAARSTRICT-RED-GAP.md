# HAARSTRICT-RED-GAP — `Mzk1HaarStrictActual` 长期红：精确缺口与 DEFERRED 处理

日期：2026-11-13；hull lane（审计，不改 Lean）。

## 状态

- 源文件：`tmp/sheaf/xif/paper/Mzk1HaarStrictActual.lean`（371 行，17,136 B，mtime 2026-11-11T01:02:48Z）。
- olean：**不存在**。
- watchdog 最新：`FAIL EXIT=1 @2026-11-13T13:26:16Z`。
- 性质：旧 API/证明漂移导致的红，不是新增数学 GAP；文件长期未跟当前 Mathlib/项目 API 更新。

## 首错清单（最新 per-file log）

1. `:74:8` `Tactic apply failed: could not unify the conclusion of max_le hz2`：`max_le` 的应用目标形状与当前 `max_le_iff`/序结构不匹配。
2. `:76:10` `Application type mismatch`：该处函数/参数类型随 Mathlib 更新漂移。
3. `:110:25` `don't know how to synthesize placeholder for argument a`。
4. `:110:7` `failed to infer have declaration type`（同处 placeholder 级联）。
5. `:108:51` `unsolved goals`（上述证明未闭合的尾部）。

## 无消费者证据（为什么可 DEFERRED）

1. **watch 名单内无直接 importer**：扫描 `extra-targets.txt` 与源码 import，watch 的 483 项中 **0** 个直接 `import Mzk1HaarStrictActual`。
2. **import 子树不在 watch 名单**：`Mzk1HaarStrictProofActual`、`Mzk1HaarAnnulusCylinderActual`、`Mzk1Cor312UnconditionalStrictAcceptanceActual`、`Mzk1AnnulusMeasurePositiveActual`、`Mzk1AnnulusStrictConsumerActual` 及相关 `HaarStrictScaling*`/`RP*` 文件均不在 `extra-targets.txt`。
3. **无 watched green 文件逆向依赖**：除该子树外，引用它的文件（`Mzk1HullProductLawShaActual`、`Mzk1S1902*`、`Mzk1StepXIHullScalingFormula*`、`Mzk1Cor312AcceptanceResolvedV2*` 等）也不在 watch；它们不是当前构建的 green 认证，不能构成 gate 消费者。
4. 因此从 extra-targets 移除 `Mzk1HaarStrictActual` 不会使任何 **watched green** 目标失去依赖；gate red 计数直接下降。

## 移除路径

1. 从 `dag/watchdog/extra-targets.txt` 删除行 `tmp/sheaf/xif/paper/Mzk1HaarStrictActual.lean`。
2. 该子树其他文件本来不在名单，无需再删；不要删除源码。
3. 在 gate 表中把该 target 标 **DEFERRED（old API, no watched consumer）**。
4. 保留 per-file log 与源码作为历史；未来若恢复 O6/Cor312 acceptance 链，按当前 API 重写而非补旧文件。

## 未来重写建议（若需要）

- `max_le hz2`：先 `rw [max_le_iff]` 或 `exact max_le_iff.mpr ⟨..., ...⟩`，不要依赖旧 `apply max_le` 的隐式结论形状。
- `:76` 参数类型：按当前 `ENNReal`/`Measure`/`Set` 的 coercion 重新检查，显式写 `(μ := ...)`/`(s := ...)`。
- `:108-110` placeholder：把 `have` 的类型写全，避免 autoImplicit 推断 `a`；必要时用 `obtain`/`refine` 显式给值。
- **不要**把旧文件强行改成 `True`/空载体；只需重建实际 Haar annulus/strict 引理簇，消费者另行接。
- 重写后需与 `Mzk1HaarStrictScalingProductActual` 等旧子树分开归档，避免 namespace/instance 冲突。

## 结论

- `Mzk1HaarStrictActual` 的红是旧 API 证明问题 + 无 watched consumer；
- 建议 **移除 extra-targets + 标 DEFERRED，源码保留**；
- 移除后当前 gate red 只剩 B5 系（qpilot 在修），不影响 P7 的 #5/#6/#9 结构化状态。
