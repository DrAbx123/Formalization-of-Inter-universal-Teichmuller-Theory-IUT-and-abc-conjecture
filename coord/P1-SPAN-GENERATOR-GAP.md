
# P1: SpanGeneratorValuation gap 记录（2026-11-14）

目标：`SpanGeneratorValuationLemma`（`Mzk1Ob33B5CountUnconditionalAttemptActual:41`）：
`∀ I v d, localValuation v d.generator = -countExponent v I`。

## 已可用的 Mathlib/项目供体
1. `IsDedekindDomain.HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity`（AdicValuation:190）；
2. `FractionalIdeal.count_coe`（Factorization:535）；
3. `FractionalIdeal.count_well_defined`（Factorization:329）+ `count` 定义（:309）；
4. 本项目已 green：`localPrincipalGenerator_proved`（无假设 generator，LFI official）、
   `countExponent_self_maxIdeal` / `localValuation_uniformizer` /
   `countValuationBridge_maxIdeal_of_generator` / `r21Bridge_maxIdeal_of_generator`（maxideal 供体）、
   `ideal_map_pow_general`、`count_mul_ideal`（乘性）、`countExponent_pow`。

## 本轮新增（条件定理）
`Mzk1P1SpanGeneratorValuationMaxIdealActual`：
- `maxIdealGeneratorData`（显式 uniformizer + span 识别构造 generator data）；
- **`spanGeneratorValuation_maxIdeal_of_span`**：max ideal 的 SpanGeneratorValuation（条件于
  `localizedLine (p) v = span{π}` 且 `Valued.v π = ofAdd(-1)`）；
- **`countValuationBridge_maxIdeal_of_span`**：同上 ⇒ CountValuationBridge。

## 剩余精确缺口
把 `localizedLine (p) v = span{π}` 真正证出来，等价于：
- **桥 1**：`Ideal.map (O_K→O_v) p = completionIdeal`（进行中）；
- **桥 2**：`localizedLine (I) v = span O_v (image of ideal extension)`。
桥 1+2 绿后，max-ideal SpanGeneratorValuation 即无条件；general I 通过 factorisation + 乘性
（`IdealMapPowerStatement`）推广。

## 结论
`SpanGeneratorValuationLemma` 目前保留为 **exact named input**（不冒充）；其 max-ideal 情形已降为
`hspan`（= 桥 1+2），不是新的不可证内容缺口。

## 桥 1 PROVED（2026-11-14 18:54:55Z）

- **`Mzk1P1IdealMapCompletionIdealActual.idealMapMaximalBridge_proved` — DONE 18:54:55Z（106s）**：
  `Ideal.map (O_K -> O_v) (underlyingPrime v).asIdeal = completionIdealOf v`。
  证明链：`intValuation_exists_uniformizer` → `intValuation_lt_one_iff_mem` →
  `valued_algebraMap_completionIntegers` + `valuation_of_algebraMap` →
  `maximalIdeal_eq_span_uniformizer` → 双向包含
  （正向 `Ideal.map_le_iff_le_comap`+`mem_completionIdeal_iff`+`algebraMap_completionIntegers`；
  反向 `Ideal.mem_map_of_mem`）。

### 桥 1 绿后剩余
- **桥 2**：`localizedLine (I) v = span O_v (image of Ideal.map)`（现可直接尝试
  `FractionalIdeal.extended` 的 `coe_extended_eq_span` / `localizedFractionalIdeal_coe_eq` 组合；
  `P1LocalizedIsPrincipalNoGap`/`LocalizedFractionalIdealFix` 只提供 `IsPrincipal`，不含该 span 恒等）；
  一旦桥 2 绿：max-ideal `localizedLine p = span{π}` = 桥 1 + FLT `maximalIdeal_eq_span_uniformizer`；
- 然后 `Mzk1P1SpanGeneratorValuationMaxIdealActual` 的条件定理转无条件（max-ideal CountValuationBridge/R21Bridge）；
- `IdealMapPower`（prime-power + 乘性）→ general I；B5Index 重接。
