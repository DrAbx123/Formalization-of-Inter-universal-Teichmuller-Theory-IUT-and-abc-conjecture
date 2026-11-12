# MATHLIB 4.36 → 4.32.2 移植评估：Analysis/Normed/Algebra/Logarithm.lean（A507）

日期: 2026-11-11。目标: 把 4.36.0-rc2 的 `logSeries`/`NormedSpace.log`（拓扑代数中的对数级数）移植到
`tmp/newmathlib/`，用主构建 4.32.2 编译，作为 p 进 log 对象基础。

## 源与依赖

- 源: `tmp/mathlib4-4.36.0-rc2/Mathlib/Analysis/Normed/Algebra/Logarithm.lean`（199 行，含 module-system 头）
- 依赖检查（4.32.2）：`Mathlib.Analysis.Analytic.OfScalars` **EXISTS**、`Mathlib.Algebra.Algebra.TransferInstance` **EXISTS**
- 名称冲突检查：4.32.2 无 `NormedSpace.logSeries` / `NormedSpace.log`（grep 0），可安全新增

## 已做适配（首版）

- 删除 `module` 行；`public import` → `import`；`@[expose] public section` → `section`
- 4.36 专属 tactic `grind [smul_zero]` → `simp [smul_zero]`
- 其余数学内容原样保留（logSeries 定义、`log` irreducible_def、logSeries_apply_eq/sum_eq、log_eq_tsum、log_one、log_op、star_log、log_mem、Commute.log 系列）
- 落盘: `tmp/newmathlib/Analysis/Normed/Algebra/Logarithm.lean`，已 `tools/extras_add.mjs` 入队

## 状态

- 已入队，watchdog 尚未编译到该文件（当前队列 ~1120，results log 活跃到 22:02，只是未轮到）。
- 待 fresh 日志后逐条适配 4.36→4.32.2 API 差异；已知风险点：
  - `tsum_mem`、`SMulMemClass.ofIsScalarTower`、`Commute.tsum_right` 在 4.32.2 的精确名称/位置需核实（grep 未直接命中，可能在同义名或别处）
  - `RestrictScalars.algebra ℚ 𝕂 𝔸`、`IsEmpty (Algebra ℚ 𝔸)` 等 4.32.2 应存在
  - `irreducible_def`、`@[expose]` 标记已处理（`irreducible_def` 保留）
- 无 sorry/axiom；不改 fragment、不碰 watchdog。

## 若编译通过：作为 p 进 log 对象基础的用法

- `NormedSpace.logSeries ℚ ℚ_[p]` / `NormedSpace.log` 给出通用拓扑环对数（junk-value 语义：无 ℚ-algebra 结构时为 0）
- 与 Takkun `Padic.LogVolume.logVol/logOnePlus` 对接：`log(1+x)` 的级数展开 + `logVol_logOnePlus` 保体积；可构造 `PadicLogSeriesObject`（`_constructed`）把 normed log 级数、μ_log 归一化、aRadius/bRadius 半径放进同一对象层
- 不直接替换 Takkun/Kummer 已有 p 进 log，而是作为其"级数解析基础"的补充（4.36 新数学）
