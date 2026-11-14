# finalDictionaryCombined 源/freshness 审计（只读，2026-11-14）

## 文件
`tmp/sheaf/xif/paper/Mzk1P0FinalS3137DictionaryActual.lean`

## 时间戳与 official
- source mtime：**04:17:53**；
- olean mtime：**04:15:04**（早于 source）；
- watchdog 最近：**04:22:05 FAIL EXIT=1**；
- 因此当前源 **不是 official GREEN / 不可复现**，olean 是旧版残留。

## 当前 tail 错误
- `:88-90 failed to synthesize instance of type class`：
  `PaperS3137ReadingDictionary` 的 structure 参数顺序错误：
  `hM`/`hB` 定义在 `(T : SourceNativeInitialThetaData)` **之前**，
  但它们的类型引用 `qVFamTensorBlock T b`，T 尚未绑定；Lean autoImplicit 产生 typeclass/隐式变量错误。
- `:94/:99/:100 Function expected`：`PaperS3137ObjectLock`/`PaperS3137ReadingDictionary` unknown，是上述结构声明失败的连带。
- `:114/:132 Application type mismatch hM expected SourceNativeInitialThetaData`：调用方按错误 binder 顺序应用。

## 内容（源码级）
- `PaperS3137ObjectLock` structure 字段：
  * `B : Bad → Nat`，`B_pos`；
  * `weight_relation : d_b = B b * localCompletionDegree T.arithmetic (nativeBadToKPlace b)`；
  * `unitMass_eq : actualUnitMassL I place = (s1915UnitMass T).toReal`；
  * `theta_sign : thetaNormReadL I place = -thetaNormReadProduct T`。
- `PaperS3137ReadingDictionary` 字段：
  * `theta_product_eq : thetaNormReadProduct = s1915ClosedForm−1`；
  * `q_paper_eq`（定义展开）；
  * `coeff_eq_of_ratio`（S45 ratio=1 → c_norm=paperCoeff）。
- `paperS3137ReadingDictionary_of`：从 green `thetaNormReadProduct_eq_closedForm_sub_one` 等构造 (a)(b)(c)，lock 仍显式。
- `finalDictionaryCombined`：`S45SourceFields + RelativeFactorTowerData + ObjectLock → paper comparison ∧ RelativeFactorTowerData ∧ Nonempty Dictionary`。

## 需注意的语义问题
1. **binder 顺序 bug** 是当前 FAIL 根因，不是数学 gap；修法：structure 参数改为
   `(I) (place) (T) [Fintype] (hM) (hB) (lock)` 的顺序，让 hM/hB 在 T 之后。
2. **符号不一致**：
   - 本文件 `theta_sign : thetaNormReadL = -thetaNormReadProduct`；
   - 已 GREEN `Mzk1P0LNormComparisonConditionalActual` 的条件是
     `hlock : thetaNormReadL = thetaNormReadProduct`（正号）。
   两者只能有一个与当前 `thetaNormReadL`/`thetaNormReadProduct` 定义一致；需要核对符号，不能同时作为真前提。
3. `finalDictionaryCombined` 仍使用 `paperNormalizedComparison_of_sourceFields`（来自 BadPlacePaperNormalizedComparison），属于 paper-normalized model comparison，不是 native/tensor 实际路线；作为 P0/P1 条件 consumer 可以，但不能当 #1 实际收口。

## 结论
- **不 fresh**：source 04:17:53 vs olean 04:15:04，当前 FAIL 04:22:05；
- 主要失败是 binder 顺序（T 在 hM/hB 之后才绑定）；
- 另有 theta_sign 符号与 LNormComparisonConditional 的正号条件不一致，需核对；
- 在修复并 official 前，不能把 `finalDictionaryCombined` 当可用字典。

未改源。
