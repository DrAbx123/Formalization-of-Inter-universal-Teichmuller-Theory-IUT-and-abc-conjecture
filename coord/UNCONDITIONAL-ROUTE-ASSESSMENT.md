# 无条件路线评估：IUT 能否不建 [GenEll]/[Mzk1] 而无条件？

**结论：不能。** 已发表的 IUT 证明链把无条件性建立在 [GenEll] 之上（IUT IV §2 原文：'we combine Theorem 1.10 with the theory of [GenEll] to give a proof of the ABC Conjecture'），而 [GenEll] Thm 2.1 的 (ii)⇒(i) 又依赖 [Mzk1] Thm 2.5/Cor 3.2（非临界 Belyi 映射存在性）。

## 1. IUT IV §2 实际引用的 [GenEll] 内容（corpus 行号）
- GenEll Def 1.2(ii)/Def 1.5(iii)(iv)/Example 1.3(i)(ii)/Prop 1.4(i)(iii)(iv)（IUT IV 2357-2417, 2528, 2637, 2664, 2773）
- GenEll Prop 3.4（Faltings heights, 2415/2555/2630/3233）
- GenEll Lemma 3.1(iii)/3.5/3.6/3.7（2624-2671, 3233-3234, 3365）
- GenEll Theorem 3.8（2672, 3192）
- GenEll Theorem 2.1（3078-3134；IUT IV 3133 明确：'by the equivalence of [GenEll] Theorem 2.1, it suffices to verify (ii)'）
- GenEll Cor 4.4（3168, 3192）
- GenEll Lemma 4.1 / Remark 4.1.1 = 经典 PNT（IUT IV 2357-2358）

## 2. 为什么不能跳过
- IUT IV Theorem 1.10（及其前置 Cor 3.12）只对 general position / compactly bounded 情形给出高度不等式；把任意 ABC 三元组化到该情形正是 [GenEll]（Thm 2.1 + §3/§4）。
- 若跳过 [GenEll]：只能 (a) 直接证我们 paper-route 的无条件 (b)/(c)（这比论文所证的 general-position 定理更强，等于绕开 GenEll；目前没有路线/依据），或 (b) 用抽象 gate 的 cardP（= ABC-strength 假设，非无条件）。
- [GenEll] 本身是**已发表证明**（无 GRH 假设；Lemma 4.1 只依赖 PNT），不是猜想；形式化它是'形式化已证数学'。

## 3. 依赖顺序与工程量（Mathlib 缺口已核实）
### Phase 1（近期可完成，已在做）
- GenEll §1：Def 1.2/1.5、Ex 1.3、Prop 1.4/1.6/1.7（abc/mainline）；
- GenEll Thm 2.1：(i)⇒(ii) 已证；(ii)⇒(i) 归约链条件于单一 Mzk1 存在性输入（mainline）；
- [Mzk1]：Lemma 2.1/2.2/2.3/2.4 完整证明（stage4；P¹ 层，Mathlib 多项式/复分析可证）；Thm 2.5 陈述 + 归约，唯一深块 = GeometricCore（RR/Serre 对偶/线丛/上同调）；
- GenEll Lemma 4.1/4.2（PNT：Mathlib 已有 primeNumberTheorem）+ 初等分析；
- P3 集成：IUT IV §2 = 'Thm 1.10 + GenEll ⇒ ABC' 显式条件定理（stepxi）；
- [AbsTopIII] 需要的具体部分（hull/stage4，见另一计划）。
### Phase 2（大工程，需自建 AG/数论基础设施；Mathlib 缺口）
- Mathlib 缺：Serre duality（0 文件）、Riemann-Roch（0）、line bundles/coherent cohomology（0）、elliptic curves/Faltings heights（0）、Galois representations/Chebotarev（0）。
- Mzk1 GeometricCore：smooth proper curves + line bundles + RR + Serre duality + basepoint-free linear systems；
- GenEll §3：SL2 群论 lemmas 3.1/3.2（初等可证）；Prop 3.4（Faltings height 比较，需 heights/moduli）；Lemmas 3.5/3.6/3.7；Theorem 3.8（full SL2 Galois actions，Serre 型深定理，需 l-进 Galois 表示）；
- GenEll Cor 4.3/4.4（依赖 Thm 3.8 + Lemma 4.1）。
### Phase 3
- 无条件 IUT ⇒ ABC：IUT 侧 (b)/(c) + Cor 3.12 定量分裂 + GenEll 全套 + Phase 2 深输入全部消除。

## 4. 当前可交付的最强诚实陈述
- **条件式**：ABC ⇐ [IUT Thm 1.10（general position/compactly bounded 不等式）] + [GenEll Thm 2.1 + Prop 3.4 + Lemma 3.5 + Thm 3.8 + Cor 4.4 + PNT]；
- 每消除一个命名输入（GenEll Thm 2.1 的 Mzk1 输入、§3/§4 的深定理），条件就少一层；最终无条件需要 Phase 2 全部完成。

## 5. 决策
- 用户指示'那就建'：按 Phase 1 → Phase 2 推进；Phase 1 已派（GenEll/Mzk1/AbsTopIII/IUT IV §2 集成）；Phase 2 的 AG/数论基础设施按依赖拆成可验证批次（先 Mzk1 GeometricCore 的 AG 层：curves/line bundles/RR；再 GenEll §3 的群论+moduli 层）。
- 不做中间 reopen；registry frozen 14041；只在论文级定理（GenEll Thm 2.1 归约链完成、Mzk1 Thm 2.5 条件化、IUT IV §2 集成等）更新一次。
