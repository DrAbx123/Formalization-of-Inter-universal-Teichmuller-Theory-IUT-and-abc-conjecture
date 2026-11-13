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
