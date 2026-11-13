# P7 十 GAP 逐个击破计划（2026-11-13 R29 之后）

来源：coord/P7-GATE-REVIEW.md §13（Mzk1P7GapRegisterActual.gapRegister）。
用户指示：10 个 gap 是把一个大 gap 分解成 10 个，逐个击破。
状态：全部未 unconditional discharge；GAP-P7-CONTRACT 为 CONDITIONAL/INTERFACE。

## 编号 / 缺口 / 主攻 lane / 下一步（可执行）

| # | code | 当前状态 | owner | 下一步（具体） |
|---|---|---|---|---|
| 1 | GAP-P7-GENERAL-CMP | OPEN；已精确化为 `comparison ⇔ ‖q‖ ≤ haarScale·∏_b μ_b(ball_b)`（abc C3S1902 链 green，CONDITIONAL on transport data） | abc | 攻乘积下界：θ-value 范数下界（rootNormedThetaValueInL 的 j=±1 指数）或 haarScale 显式值；再证 `1 ≤ haarScale·∏` 的条件分支（ConditionOne 已 green） |
| 2 | GAP-P7-IQ-LITERAL | OPEN；Mathlib restricted product 已 rfl 识别（IQ skeleton = Πʳ）；FLT RestrictedProduct/Equiv 正在修 :620 | qpilot | FLT Equiv/TopologicalSpace/FiniteAdeleRing 链：等 olean 后做 `IQRestrictedProductCarrier ↔ FiniteAdeleRing` 的 Equiv/instance，或写精确缺口（哪些字段未 realization） |
| 3 | GAP-P7-OB33-SRC | OPEN；det(x)M finite determinant 恒等式 green，source arithmetic-degree = normalized log-volume 识别未证 | shehdd | 查 OB33 接口（Mzk1Ob33*）与 source identity 定义；给出 identification 的显式 named input + 条件等价，或找实际构造；更新 P7 §13 |
| 4 | GAP-P7-MULTIRADIAL | OPEN；(xi-e)/(xi-f) multiradial production 缺失 | stepxi | 全树搜索 xi-e/xi-f multiradial 生产（IUT II/III、S 系列、n8）；若存在可 port 则建 carrier；若不存在写精确缺失定义（production 的输入/输出型别） |
| 5 | GAP-P7-THETA-V | OPEN；S3137 raw Haar green，paper normalized V 未识别（GAP-P6-C17-THETA-S3137 四层差） | hull | 逐层拆四层差：先 `thetaPilotHullLogVolumeReal`（raw）与 `normalizedLog`（paper V）的 scale/offset 字典（RawNormalizedDictionary 已有条件版）；一层一个定理 |
| 6 | GAP-P7-THETA-D | OPEN；C3-vs-D 字典未构造 | hull | 用实际 C3=S2717C3…D 与 D 数据构造 C3D dictionary 的 key map（C3D rows/index/field/place-tuple 已有）；先写条件字典（显式 named field），再试消去 |
| 7 | GAP-P7-THETA-DEG | OPEN/PARTIAL；S3137 p-scaling block factor 非正已证；[C3 block:Q_p] vs local degree 识别未证 | stage4 | 用 `Mzk1S3137ThetaBlockFactorNonposActual` + 局部 degree（localCompletionDegree/FINITE）写 block:Q_p 与 local degree 的识别条件；先条件版 |
| 8 | GAP-P7-CONTRACT | CONDITIONAL/INTERFACE；reconciliation 12 rows/7 missing；S3137 assembly 以 comparison 为 hypothesis | mainline | AgreeFLT green 后：把 7 missing rows 与 10 GAP codes 逐行映射（GapLedger），产出 conditional contract（hypotheses 显式列出）；这是 P7 最终条件装配 |
| 9 | GAP-P7-HULL-UB | OPEN；但 hull 已有 actual main-term 界 `normalizedLog_hull ≤ (1/4)l(log disc+log cond)`，C0=0 | hull | 关键：把 `Mzk1MainTermActualBoundActual.normalizedLog_hull_le_actualMainTerm` 与 P7 的 V 经 paper normalization 字典对接；若字典条件化成立，则 HULL-UB 可降为 CONDITIONAL（甚至关闭） |
| 10 | GAP-NORM-ARCH-C-K | OPEN；explicit K/[K:Q] arch normalization 未闭 | lattice | 查 Mzk1NormArch* 系列（CAbc/CHArc/ArchDegree）已有内容；构造显式 C_K 并证 `NORM-ARCH-C-K` 条件版；与 abc 的 arch factor 输出对接 |

## 纪律
- 每项只允许：定理化（green）、条件接口（显式 named input，CONDITIONAL）、精确缺口文档（OPEN + 障碍说明）。
- 禁止：改对象/加 axiom/sorry/toy carrier；不得把条件接口写成 unconditional。
- 报告格式：gap code + 文件/定理 + watchdog DONE/olean + 状态变化（OPEN→CONDITIONAL→DISCHARGED）。
- 文档同步：P7-GATE-REVIEW §13 表、GapLedger、R29-STATUS。

## 优先级
1. GAP-P7-HULL-UB（#9，可能已有足够材料关闭）
2. GAP-P7-CONTRACT（#8，等 AgreeFLT）
3. GAP-P7-GENERAL-CMP（#1，C3S1902 链已就绪）
4. GAP-P7-THETA-V/D/DEG（#5/6/7，hull/stage4）
5. GAP-P7-IQ-LITERAL（#2，等 FLT Equiv）
6. GAP-P7-MULTIRADIAL（#4，可能真缺）
7. GAP-NORM-ARCH-C-K（#10）
