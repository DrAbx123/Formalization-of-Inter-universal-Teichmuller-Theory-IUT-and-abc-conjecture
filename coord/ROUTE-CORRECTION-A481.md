# A481 路线纠正：放弃 model/value-realized carrier，改原文对象

## 为什么这条路不对（仓库自身审计已证明）
- `LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/SourceHullInterfaceDischarge.lean`：
  - F2（已证）：在 value-monoid realization 且 pointwise degree-faithful 下，paper-shaped 输入（hull ⊆ λ·unit-region）**不可满足**，且 `sourceHullVolume = ⊤`（`sourceHullVolume_not_lt_top_of_degreeFaithful`）；
  - F1 只是 ℝ-范数空间的 consistency model（`haarContractionInterface`），不是 IUT 的 `IQ(S±; n,◦D^vdash)` 载体；
  - 结论原文：`Nothing here is claimed about the actual IQ(...) carrier`，discharge 仍 open。
- `IQCarrierHaarData.lean`：interface 存在 ⇔ hull log-degree 有界；在 degree-faithful 下不存在。
→ 因此“在某模型/抽象接口上填两个 gap 字段”不是证明，那些不等式原文对象未构造时按用户指示是不可判定的。

## 改正后的路线（A481）
1) 先构造 literal IQ 载体：有限素位上的 log-shell 受限乘积 + 单位区域 O + Haar 归一化 scaling λ（Hodge theater/prime-strips/Frobenioid/log-shell 对象）。
2) 在其上构造 θ-pilot 像 `n,◦U_{vQ}` 与 hull。
3) 用 `1,◦U_{j,vQ}` 的紧性 + log-volume 定义证明 Cor 3.12 的 hull 有限性。
4) 把 IUT IV 两个比较不等式在 literal 载体上化成具体计算并证明。
5) 最后才重接 `Cor312ToABCBridgeInterface`（carrier = literal IQ 载体），不得再用 realLineHullData/model。

## 已处置
- `Mzk1StandardComparisonConstructionActual`（realLineHullData 模型路线）标 SUPERSEDED，不作为解。
- 8 个 owner 已按 A481 重新分工（literal carrier / θ-pilot 像 / compactness / 重接桥 / IUT IV 计算 / 审计）。