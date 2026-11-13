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
| 4 | GAP-P7-MULTIRADIAL | PARTIAL；finite Q(i)-at-5 production green；general CarrierAlgorithmContract 无条件 green；RouteNormalForm named input；实际 production 缺失 | stepxi | 已完成：carrier 包 `Mzk1P7MultiradialCarrierActual`（finite model）、`Mzk1P7MultiradialGeneralBridgeActual`（general conditional）、精确缺口 `coord/P7-MULTIRADIAL-GAP.md`；下一步仅 actual n,oR_LGP/production 源 |
| 5 | GAP-P7-THETA-V | **PARTIAL**（四层：L1 raw green `Mzk1ThetaVLayerRawActual`、L2 normalized green `Mzk1ThetaVLayerNormalizedActual`、L3 scale/offset CONDITIONAL `Mzk1ThetaVLayerScaleOffsetActual`、L4 OPEN；`Mzk1ThetaVFourLayersActual` DONE 11:19:54Z） | hull | 剩 L3 的 scale/offset 实际来源与 L4；一层一个定理 |
| 6 | GAP-P7-THETA-D | **PARTIAL**（实际 C3D key map 已构造：`Mzk1C3DKeyMapActual`，`actualDonorC3 := S2717C3 R … D`，indexEquiv/dPlaceIndex/dPlaces/dTuple 全取实际 C3 字段） | hull | 剩 D 侧对齐：把 D 数据接到该 key map 形成双向字典；先条件字典再消去 |
| 7 | GAP-P7-THETA-DEG | **OPEN/PARTIAL**（文件 `Mzk1P7ThetaDegActual` 已写，等 `Mzk1C3BlockMeasureActual` olean 后编；含 localCompletionDegree=finrank、c3TensorBlockDimension=∏、block nonpos+local degree 分解） | stage4 | 等依赖 olean 后重编 → 更新 P7 §13 为 CONDITIONAL/PARTIAL |
| 8 | GAP-P7-CONTRACT | **CONDITIONAL ASSEMBLY**（`Mzk1P7ContractMapActual` DONE 11:18:55Z，olean=True；AgreeFLT DONE 11:13:10Z） | mainline | 已完成：`recon12ToGap`/`missing7ToGap`/`gapCodesCovered`/`contract_fields_not_linked`/`p7_conditional_contract`；文档 `coord/P7-CONTRACT-MAP.md`。后续：等其它 GAP 关闭后把条件装配升级为 DISCHARGED |
| 9 | GAP-P7-HULL-UB | **CONDITIONAL**；normalizedLog→paperBox actual green（`Mzk1HullUBPaperBoxActual`，C0=0）；paper V 差 RawNormalizedDictionary scale/offset | hull | 已完成实际 normalizedLog 侧 + 条件字典（`Mzk1HullUBDictionaryActual`）；下一步只拆 scale/offset 的实际来源（若 scale=1/offset=0 可升级 DISCHARGED） |
| 10 | GAP-NORM-ARCH-C-K | **CONDITIONAL/PARTIAL**；`Mzk1NormArchCKActual.lean`（DONE 11:13:09Z）显式 C_K 已证 | lattice | 已构造 `archCK=1/[K:Q]`、`archCKToric=1/(2[K:Q])`，general-K `hArc/hNon/hToricArc` 因子形式 green；剩余 abc arch factor 输出对接（GAP） |

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
