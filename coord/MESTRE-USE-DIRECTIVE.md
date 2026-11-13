# Mestre–Oesterlé 输入的使用指令（2026-11-14 用户口径）

用户明确：**如果当前路线用得上 `MestreOesterleBound` 这个输入，就用；最后再形式化它的精确陈述。不要出现“能用但不用”**；只有确认实在用不上才另说（并写清精确原因）。

## 当前事实（Lead 已核）
- `MestreOesterleBound` 只出现在旧 §12.2/素导子骨架（`Mzk1PrimeConductorRouteActual`、`Mzk1DExactLowerActual`、`Mzk1L7ProofActual`、`Mzk1ThetaDataLegalityActual`、`Mzk1TargetReductionActual`、`Mzk1P3*`），不在 signed Cor312/`Paper312Statement` 的 import closure。
- 旧骨架里它作为显式 `hMO` 条件出现；形式为 `logq ≤ 6·logd + C`（normalized；原文精确陈述待逐字核验，见 `E7-SOURCE-AUDIT.md`）。
- abc 侧仍需 `Cor312ToABCBridgeInterface`（审计：等价于 abc 本身），不是 MO 能替代的。

## 待做（owner: mainline，abc 支援）
1. 对当前活动缺口逐项判定 MO 可否消费：`thetaR13Defect=0`/`defect≥0`、`NativeComparison`、`R21Bridge`、`IdealLocalizedCount`、`residue-one`、det-Haar 最后两步、`P2ArchLogSourceIdentification`、`R37R13`、blockEquiv/unitMass。
2. 判定标准：缺口或其子引理是否能写成 MO 形状（`log q ≤ 6 log d + C`、素导子 `e_p ≤ 5`、`D_exact` 下界等）的推论；若 YES，写小文件显式 `hMO` 接线（class-B 输入，不伪造证明）。
3. 若 NO，写精确非适用性说明（对象/量纲/归一化不匹配，或仅对旧骨架可用）。
4. 最后阶段：把 MO 的精确陈述（1989 论文定理编号/假设/例外）逐字核验后替换当前 normalized Prop（待原文）。

## 更正：genuine Mestre–Oesterlé 定理 vs 代码中的归一化替代

- **genuine MO（Zbl 0693.14004，zbMATH 评论已 fetch）**：
  - Thm 1：E/Q 半稳定 Weil 曲线，`|Δ|=m` 次幂 ⇒ `m≤5` 且 E 有 Q-有理 m-除点；
  - Thm 2：导子为素数 p ⇒（明确例外外）`Δ=±p`。
- 代码 `Mzk1PrimeConductorABCActual:32`/`Mzk1PrimeConductorRouteActual:54` 的 `MestreOesterleBound`（`logq≤6logd+C`、`e≤5∧(p>37→e≤2)`）是 **normalized surrogate**，不是原文陈述；最终形式化 MO 时替换为 Thm 1/2 并重新推导。
- 这不影响当前判定结论（当前活动缺口均非 MO 形状）；但 **不得把 surrogate 声称成原文定理**。`Mzk1MestreUseWiringActual` 的 rows/文档需按此更正。
