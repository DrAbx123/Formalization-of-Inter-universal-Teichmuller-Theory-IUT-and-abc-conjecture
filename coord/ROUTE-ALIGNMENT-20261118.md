# R0-R7 路线对齐审计（2026-11-18）

权威路线：`coord/P7-G1-P6-P8-CLOSURE-ROUTE-20261116.md`（不修改）。本文件只登记当前 Lean 工作与路线出口的差异与纠正动作。

## 总表

| 包 | 路线出口（摘要） | 当前 Lean 实际物 | 对齐判定 | 动作/owner |
|---|---|---|---|---|
| R0 | R0.1 c_P=v_P(q_P)/e_P^abs；R0.2 全纤维；R0.3 hBar=logHeight1/[L:Q]、D=log|disc|/[L:Q] | R0.1 `Mzk1ULR0RealDictionaryActual`（当前 cP:=order，未除 e_abs）；R0.2 `Mzk1ULR0FullFiberActual` DONE 16:14:13（Qb 用 v_P=orderAtFPlace）；R0.3 `Mzk1ULR0BarDiscActual`/`BarAdapterActual` 在编（hBar/D 口径正确） | R0.1 偏离路线；R0.2/R0.3 对齐 | david 立即把 R0.1 改回路线 c_P=v_P/e_abs；sophie co-sign |
| R1 | q-root 格 J_b->Theta、sum_b w_b nu(J_b)=-M、-M<=nu(Theta)（R1.1）；根参数主格不取整 | `Mzk1URRootMassOnePlaceActual`（rootNu/log_rootHaar_prime_pow 在编）；`Mzk1URRootValueGroupProbeActual`（值群分解 probe）；sophie R1-P5 文档给出 qP5/thetaP5 与共同容器比较 | 对齐（进行中）；c_P 权重必须用新口径 | kurt：root 质量用 c_P=v/e_abs；P5=`-M<=ksThetaHullLogRoot_lam` |
| R2 | 实际 procession 对象与 R1 同一 Theta 的源映射；hlogdK/hsQ 实际数据；nu(Theta)<=H=sum w avg V | `Mzk1ULR2HsQSupportActual` DONE 16:21:39（actual support primorial）；`Mzk1ULR2HlogdKTowerActual` 在编；packet `Mzk1URPacketActualInstanceActual` b-参数化+scoped 4M 在编 | 部分对齐：hsQ/hlogdK 对齐；procession 源映射与 nu(Theta)<=H 尚未交付，当前 packet 结论仅为 `ksThetaHullLog<=urPacketV_K` 中间式 | kurt：按路线 §4.2 第 3-5 步补 procession 源映射和 nu(Theta)<=H；david 供权重 |
| R3 | 逐 lambda 合格源（实际 E[3]/E[5]/E[l] 坐标，含 y 与加法公式枚举）；compositum/degree；R3.2 Q_all-Q_used；选 l | `Mzk1G1F2ThetaTorsionFiveActual` DONE 16:21:34（仅 Psi_5 的 x 根集）；`ThetaDivisionPolynomials/TorsionCoords/Compositum/CompositumDegree/IndexTables/BadTate` 在编 | 部分偏离：`fiveTorsionX` 只登记 division-polynomial 根，路线 §5.2(2) 要求 y 坐标+加法公式证明枚举=实际 torsion；R3.2 尚早 | grace：补 y/曲线方程与 torsion 枚举证明（或走实际乘法核）；其余按 R3a/R3b |
| R4 | 一般受保护点 noncritical map（三路线取一，出口 psi 满足 R4.1）；§6.4 有理函数递归 | emmy 路线 A：`Mzk1G1R4ProtectedActual` layer1+structures，字段名修中；`Mzk1G1F2H1VanishingDataActual` 按 sophie H1 doc；henry `Mzk1G1R44RationalRecursionActual`（`M2AnalyticTargetRat`）START | 对齐（进行中） | emmy/henry：保持路线 A + 有理映射递归；H1VanishingData 不得 sorry |
| R5 | SeparationInput 实际实例（base different=0 用 differentIdeal_self_eq_top 填，不可删 base）；phi_L:Y_n(L)->P1(L) 与 rho 距离；有限不交边界族->K_V | `GKRhoDistance/RhoZero/RhoSmul` DONE；`GKRhoP1` 在编；`Mzk1G1FractionRingFinrankActual` 修 hc；`BaseDifferentTransport` 暂保留 `(prerequisite: base_different_top)` | 部分偏离：路线 §7.1(3) 要求证 base different=0，不是留 prerequisite；rho/phi_L 对齐进行中 | alan：把 base_different_top 从 prerequisite 变回证明（differentIdeal_self_eq_top + 整数环识别）；henry：rhoP1/phi_L |
| R6 | 同一数域/多截面：h_E 有限齐次生成元、base divisor=E_i、lambda_{E_i,v}、h_E<=kappa h_omega；R6.1-R6.3 | `Mzk1HTF4R6GeneratorsActual` DONE 16:16:38（R6GeneratorData/R6PlaceData/sum_lambda）；`Mzk1HTF4R6Actual` DONE 15:58:47 | 对齐（数据层）；3 个 crosswalk 未闭：completion-to-degree m_i、scheme baseDiv、per-place metric（sophie R6 doc 已标 OPEN citation） | andrew：按 R6 paper doc 收 crosswalks；R6.1/h_omega 待 R4/R5 |
| R7 | 实际 Fermat lift L=Q(x,y)：[L:Q]<=n^2、三类素数、D(L)<=log rad(abc)+C_n；同一实际点填 P8 | andrew 已重派 F7；`Mzk1F7LiftActual` DONE 14:22:04；F8/P8 consumer 既有 | 对齐（进行中）；hPi/pi(y)=a/c 的 F8 高度字典未接 | andrew：F7 三类素数+D(L) 界；之后 P8 同 L/y 装配 |

## R0 的必须纠正（路线 §2.1 / §10 第一批）

路线原文要求：

- `c_P = v_P(q_P) / e_P^abs`（R0.1）；`v_P(pi_P)=1`、`|x|_P=p^{-v_P(x)/e_P^abs}`；
- `qVFamNormalizedCoefficient` 的实际定义是 `-log_p||q||`，不按名字等于整数阶；不能把 c=order 当默认规则；
- 按 (R0.1) 用 spectral norm 时绝对 ramification 已进入 c_P；再除 e(P/b) 可能重复除法；
- 本批交付“一个实际坏位的 c=ord/e、root 格质量、full-fiber 权重图”。

我们此前的 R0.1 裁决（cP:=order，无 /e）与路线不一致，必须改为：

1. `order_c := ((qVFamily T b).order : R) = v_P(q_P)`（raw integer order；`QVFamTensorCoefficient`/`QVFamNormalizedCoefficientActual` 是这个 raw 量，名字有误导）；
2. `e_abs := e_P^abs`（qVFamily 所在位的绝对分歧指数；用已有 ramificationIdx/completion 供体）；
3. paper/路线 `c_P := order_c / e_abs`（不是 raw order）；
4. spectral 量（`QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient`）：`spectral = c_P - log(qVFamNormRatio)/log p_b`（S121 形式）；当 `qVFamNormRatio=1` 时 spectral=c_P（逐 b），不是 spectral=raw order；
5. 不得再除 e(P/b)（e_abs 已在 c_P 中；double counting）；
6. R0.2 full-fiber 保持用 raw v_P：`(1/[F:Q])sum_P f_P v_P(q_P) = f_b v_b/[Fmod:Q] = ([Fmod_b:Q_p]/[Fmod:Q])*c_P`；Qb 的 orderAtFPlace（=v_P）不改，M_paper_v2 不改；
7. legacy `actualQPilotMagnitudeClassical` 用 spectral：`actualQTermSpectral = actualQTermPaper - gamma_b*(log ratio/log p_b)*log p_b`（david 已写 `Mzk1ULR0ActualQCorrectionActual`，保留）。

## 其余 dev/风险

- R2：§4.1 packet 的 `urActualB T` 改给定 b 已做；§4.2 第 3/5 步源映射+nu(Theta)<=H 未交付，不能只用 `urPacketV_K` 名称对接。CTheta 下界用 §4.5（-1<=CThetaPaper），不要填 S2953 等式。
- R3：§5.2(2) torsion 枚举必须含 y 且用加法公式；§5.2(3) compositum 需实际 Galois 作用/degree；仅 adjoin root set 只到 root field，不能称 torsionCoords 已闭。
- R5：§7.1(3) base different=0 是必证项；prerequisite 只是临时缺口，不能当闭环。
- R6：§8.4 的 3 个 crosswalk 与 §8.6 h_omega 统一界是 R6 剩余；数据层 DONE 不等于 (R6.3) 已闭。
- R7：§9.2 hPi 高度字典与 P8 同一 y 装配未起；F7 完成前不能填 P8。

## 结论

- 主线没有切换：R0->R1/R2->R3/R4/R5->R6->R7->P8 方向与路线一致；F 侧旧 P5/hull 仍只作 donor。
- 最紧急的唯一口径偏离是 R0.1：立即把 c_P 改回 `v_P/e_P^abs`（路线 §2.1/§10），并让 R1 的 root 质量/权重用该口径；R0.2 保持 raw v_P。
- R3 的 torsion y/枚举与 R5 的 base different 是两个“看起来完成但实际未闭”的点，必须在报告中区分 data-layer / closed。
