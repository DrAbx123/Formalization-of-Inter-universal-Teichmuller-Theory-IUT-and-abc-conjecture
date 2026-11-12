# P3-MINIMAL-DELIVERABLE — P3 最小交付现状（HANDOFF §8.2 P3）

时间：2026-11-13 05:37。依据：HANDOFF §8.2 P3（“对一个具有原文量词的输入类给出明确、可代入的界；写明其他输入仍缺什么”）。

## 1. 已交付的“输入类 + 界”

输入类：**素导子（prime conductor）椭圆曲线数据**（carrier: Mzk1PrimeConductorRouteActual.PrimeConductorCurve，显式 p、e=ord_p(Δ_min)）。

定理（Mzk1PrimeConductorUnconditionalActual，watchdog DONE 21:32:45Z）：
- nativeDExact_L7_of_conditions：给定
  - GAP-PC-WEIGHT：∀ 坏位 b，nativeBadLocalWeight b = 1（局部完备次数 1）；
  - GAP-PC-LOGSUM：log C.p ≤ Σ_b baseQLogMagnitude；
  - arch ≥ 0；
  ⇒ DExactLowerTarget C l (nativeDExact T arch)（实际 D_exact = Σ w_b·|log q_b| + arch）。
- primeConductor_ssIneqExplicit_of_actual：对外部参数 MestreOesterleBound（显式 Prop，已发表定理，不是 axiom）与上述两个内容缺口，得到
  SSIneqExplicit (sL l) (e·log p) l ((l+5)/4 · nativeDExact)。
- 辅助：nativeBadLocalWeight_eq_one_of_localCompletionDegree_one（degree=1 ⇒ weight=1）。

配套（已 green 的支撑链）：
- Mzk1DExactActual：L7⇒L6 接口；
- Mzk1TargetReductionActual：M≥0 ⟺ L6ReducedInequality（条件于对象字典 hbridge）；
- Mzk1P3DictionaryActual（DICT-A）：boxSlack、T(l) 分母字典 l6_iff_scaled、targetM⟺paperBox（条件 DICT-B/C）；
- Mzk1S3050ConstantSourceActual / Mzk1StepVReductionActual / Mzk1StepVExtraNonnegActual / Mzk1StepVProcessionActual / Mzk1StepVAlignmentActual / Mzk1StepVVolumeActual / Mzk1StepVScalingDataActual：StepV 链与局部 2l=c_root 换算、per-label region、volume identity 归约。

## 2. 仍缺什么（按可证性排序）

1. **GAP-PC-WEIGHT**：实际 localCompletionDegree T.arithmetic (nativeBadToKPlace T b) = 1。素导子 + l ∤ e_p 的 tame 情形：K=F(E[l])，p 处 tame 且 l∤e_p ⇒ K_w/F_v 不分歧 ⇒ degree 1。需要局部域分歧/次数计算（FinitePlaceExtension/CompletionDegree 现有对象可查）。**这是最有希望闭合的一条。**
2. **GAP-PC-LOGSUM**：log p ≤ Σ_b baseQLogMagnitude 的实际识别（q_b 的指数/范数与 p 的关系；素导子情形 q 与 p 的 local 参数）。
3. **GAP-PC-THETA-LEGALITY**：素导子 Θ-data 合法性（l∤e_p、ρ̄ 满射等外部/半外部条件，ThetaDataLegality 结构已有字段）。
4. **对象字典（DICT-B/C）**：paper 对象 (D,Q,S,T) ↔ 算术量（log disc、q 系数、s^Q、T(l)D_exact）以及 box 上界 ⟷ L6 下界的方向一致性（反向 UNKNOWN）。
5. **StepVQRootSourceGap**：qroot^{label²} 的 actual generators + norm 等式（StepV volume identity 无条件化的最后源对象）。

## 3. 验收口径

- 该素导子类是“具有原文量词的输入类”的一个真实子类；定理只依赖外部已发表定理参数 + 两个显式内容缺口，无 sorry/axiom，无目标假设。
- 不得把它报告为“3.12 已证”或 ABC 进展；它是 P3 的局部最小交付示例，其余输入类/全称命题仍缺上述内容。
- 下一步：GAP-PC-WEIGHT（mainline）→ GAP-PC-LOGSUM；DICT-B/C（mainline/abc）；StepVQRootSourceGap（qpilot）。
