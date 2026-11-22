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

## 13. 更正（2026-11-14）：FinalS3137Dictionary 已 GREEN，旧 GAP rows stale

### 当前 official
- `Mzk1P0FinalS3137DictionaryActual`：source 04:25:11，olean 04:29:54，**DONE EXIT=0 04:29:55**；
- `Mzk1P0FinalS3137DictionaryAxiomProbeActual`：source 04:33:10，olean 04:36:24，**DONE EXIT=0 04:36:25**；
  `#print axioms` 对 `paperS3137ReadingDictionary_of`/`finalDictionaryCombined` 均为 `[propext, Classical.choice, Quot.sound]`（无 sorryAx）。

### 已修复的 binder 顺序
`PaperS3137ReadingDictionary` 现为：
`(I) (place) (T) [Fintype] (hM) (hB) (lock)`；
`PaperS3137ObjectLock` 也把 T/Fintype 放在前置参数，结构已可编。

### 仍需注意
1. **theta_sign 符号**：
   - Dictionary 的 lock 字段：`thetaNormReadL I place = -thetaNormReadProduct T`；
   - `Mzk1P0LNormComparisonConditionalActual` 的 hlock 是 **正号** `thetaNormReadL = thetaNormReadProduct`；
   - 两者不能同时作为同一对象的真前提；需核对定义符号。Dictionary 只把这个等式作为 **lock 字段**（未证明），所以不产生矛盾，但语义上两个 consumer 不一致。
2. **paper comparison 来源**：`finalDictionaryCombined` 的 `paperNormalizedThetaSum ≤ paperNormalizedQPilotSum` 来自 `paperNormalizedComparison_of_sourceFields`（paper-normalized model comparison），不是 native/tensor 实际收口。

### stale 状态行（未改源，仅记录）
- `Mzk1P0FinalS3137ConditionalActual.lean:92`：
  `("PaperS3137ReadingDictionary", "not defined (EXPLICIT GAP; no True)", "EXPLICIT GAP")` — **已过期**，Dictionary 现已定义并 GREEN；
- `Mzk1P1PaperSumsToS3137BridgeActual.lean:118`：
  `("PaperS3137ReadingDictionary", "EXPLICIT GAP (not defined; True placeholder deleted...)", "EXPLICIT GAP")` — **已过期**。

### 结论
- FinalS3137Dictionary/Probe 已 fresh GREEN；
- 两个旧 rows 仍写 GAP/not defined，是 stale documentation，需由 owner 更新；
- theta_sign 正负号与 LNormComparisonConditional 不一致，仍需核对；
- 未改源。

## 14. row 更新后复核（2026-11-14）

### fresh GREEN
- `Mzk1P0FinalS3137DictionaryActual`：source 04:39:04，olean 04:44:24，**DONE 04:44:25**；
- `Mzk1P1PaperSumsToS3137BridgeActual`：source 04:39:04，olean 04:44:23，**DONE 04:44:24**；
  rows 已更新为 `CONSTRUCTED in Mzk1P0FinalS3137DictionaryActual (...; no True)`。

### stale / red
- `Mzk1P0FinalS3137DictionaryAxiomProbeActual`：source/olean 仍是 **04:33:10 / 04:36:24**，早于 Dictionary 新 olean 04:44:24；
  probe 本身 GREEN，但 **不是对当前 Dictionary 的 fresh probe**；需 retouch 后再报 axioms。
- `Mzk1P0FinalS3137ConditionalActual`：source 04:39:04，最近 **FAIL 04:44:24**；
  * 日志有 `Mzk1P1NormalizedSourceConditionalActual.olean does not exist`（旧 batch 瞬时缺失；该 olean 03:15 已存在）；
  * 真实源 bug：`finalBridgeConditionRows` 现有 **10** 行，但 `finalBridgeConditionRows_length : ... = 9`，`rfl` 失败（type mismatch）；
  * rows 内容已更新为 `PaperS3137ReadingDictionary CONSTRUCTED (...)`，但 length 定理未同步。

### 结论
- Dictionary 与 Bridge 已 fresh GREEN；
- AxiomProbe 需 retouch 才能对当前 Dictionary 报 fresh axioms；
- Conditional 仍 red，根因是 rows length 9 vs 实际 10（须改 10 或删一行）；
- 未改源。

## 15. 最终 fresh 复核（2026-11-14）

### all GREEN
- `Mzk1P0FinalS3137DictionaryActual`：src 04:53:07，olean 04:57:23，**DONE 04:57:24**；
- `Mzk1P0FinalS3137ConditionalActual`：src 04:53:15，olean 04:57:23，**DONE 04:57:23**；
- `Mzk1P0FinalS3137DictionaryAxiomProbeActual`：src 04:53:15，olean 04:57:18，**DONE 04:57:19**；
- `Mzk1P1PaperSumsToS3137BridgeActual`：src 04:39:04，olean 04:44:23，**DONE 04:44:24**。

### freshness caveat
- Probe olean **04:57:18** 早于 Dictionary 最终 olean **04:57:23**；
  即 probe 可能在 Dictionary 最后一次重编前完成，属“依赖后变”；
  内容/名字未变时 axioms 预计相同，但严格 freshness 需 retouch probe 再跑一次。

### 结论
- Dictionary/Conditional/Bridge 均 fresh GREEN；
- Probe GREEN 但对最终 Dictionary 的依赖顺序不够 fresh，建议 retouch；
- 未改源。

## 16. 最终 fresh 复核 2（2026-11-14）

- Probe 已 retouch：src 05:02:06，olean 05:04:50，**DONE 05:04:50**；
  olean 晚于 Dictionary 04:57:23，**fresh**；
- `#print axioms` fresh：
  * `paperS3137ReadingDictionary_of` → `[propext, Classical.choice, Quot.sound]`；
  * `finalDictionaryCombined` → `[propext, Classical.choice, Quot.sound]`；
- Dictionary 04:57:23、Conditional 04:57:23、Bridge 04:44:23 均仍 fresh GREEN。

### 结论
全部 final freshness 满足；无 source changes。

## 17. LS3137/donor freshness（2026-11-14）

### LS3137
- `Mzk1S3137LReadoutActual`：src 11-13 15:00:38，olean 11-13 15:01:51，**DONE 15:01:52**；
  fresh GREEN（旧但未改）。
- `Mzk1P0LS3137LFinalActual`：src 05:43:49，**FAIL 05:47:13，无 olean**；
  tail errors：
  * `:14 Invalid argument name I for function`（`qPilotLogVolumeReadingL` 的隐式 I/C3L binder 顺序）；
  * `:17 typeclass instance problem is stuck`（`C3L.q.q` 的 place/QCandidate 实例）；
  * `:20 Unknown identifier C3L` + whnf timeout；
  * `:19 unknown qReading_final` 是上述失败连带。
- `Mzk1P0LReadoutFinalActual`：src 02:01:27，olean 02:04:07，**DONE 02:04:08**；fresh GREEN。
- `Mzk1P0LNormReadoutActual`：src 01:54:11，olean 01:57:31，**DONE 01:57:32**；fresh GREEN。
- `Mzk1P0LPaperInstanceActual`：src 11-13 15:24:41，olean 11-13 15:27:26；fresh GREEN。

### donor
- 见 §13：BaseScalar fresh GREEN 05:22；spectral FAIL 05:32；Final 无 olean。

### 结论
- LS3137 readout 旧文件 fresh GREEN；
- LS3137 Final 仍 red，是隐式 binder/instance 问题，不是新定理；
- L readout/normcomparison fresh GREEN；
- 未改源。
