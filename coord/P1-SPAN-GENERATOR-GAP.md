
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
