# AUDIT-IV-LIT-QSTABILITY — iv/lit 读法分歧与 q-不稳定性审计

日期：2026-11-12（A1029）。**Status: MODEL/NUMERIC 审计记录，不是定理，不改目标。**

本文件记录 A1027–1028 的读法判定、qOrder 原始整数结论、偏差候选与待审计项；不改生产 Lean，不编译，不声称 ABC/SSIneq 已证。

## 1. A1027–1028 结论：iv 不稳定 / lit 稳定

### 1.1 两个读法的精确定义

- **iv 读法**：`concreteVariantData` 的 `rhsData := D.rhsData`，`thetaPilot := thetaPilotOn _ (ivLabels _)`；`ivLabels i = {distinguished n i} = {j}`（单 label；IUT IV Thm 1.10 Steps (iv)-(v)）。源：`Iut/Concrete/ThetaRegion.lean:315-316`, `:333-336`, `:354-362`；`Iut/Cor312/Statement.lean:89-91`。
- **lit 读法**：`rhsDataLit := rhsDataOn (litLabels _)`，`litLabels i = Set.univ = S_{j+1}`（全 label union，含 (Ind1) 置换；IUT III Cor 3.12 literal）。源：`ThetaRegion.lean:338-341`, `:364-370`；`Iut/Concrete/Literal.lean`。
- `concreteVariantData = iv`；`concreteVariantDataLit = lit`；lana 的 `Cor312VariantHolds` 与 ABC 桥 `Iut.MainTheorem` 用 **iv**；lit 独立定义。

### 1.2 A1027 最小模型（MODEL，不是定理）

模型：e=1, shell=O, n=1, qroot ord = m/(2ℓ), A=m logp/(2ℓ), sF=(1/nC)Σj²；单坏位 I_n 族（p=7, ℓ=5, n=1..50）。

| reading | `ind2` | `gap` | variant 条件 | 稳定性 |
|---|---|---|---|---|
| **iv** | 0 | 0 | `V ≥ (sF−1)A` | **不稳定**：V q-无关，RHS 线性无界；I_n 的 qOrder=n 使大 n 失效 |
| **lit** | +j²A | `sF·A` | `V ≥ −A` | **稳定**：若 `V≥0, A≥0` 则 trivially 成立 |

数值（`coord/TATE-IN-FAMILY-VARIANTS.md`，qOrder=n 方案 a）：

- `H_tame=2(1−1/10)log7=3.502638`，`arch=0.28527176`，`T(m)=0.2918865·m`；
- iv：`M(n)` 在 n=20 首次翻负 `M=−2.050`，首个 **admissible 负值 n=21**（`M=−1.369`；admissible 条件 ℓ∤n），n=50 `M=−10.806`；
- lit：`gap=sF·A`，variant ⇔ `V≥−A`；在 `V≥0` 下成立，**大 n 稳定**。
- `V≥0` 的 green 依据（GAP-VNONNEG）尚未验证：需要 packet 体积非负、finite tame `Σ(1−1/e)logp≥0`、arch/logShellRadius≥0 的端口；本模型只作数值。

### 1.3 读法判定的直接后果

- lana 的 `concreteVariantData` 是 **iv**；paper IUT III Cor 3.12 的字面（literal）是 **lit**；IUT IV Steps (iv)-(v) 用 **iv**；ABC 桥用 **iv**。
- 若 A1027 模型忠实，**lana 的 iv 目标对任意 I_n 大数据为假**（与 IUT 定理矛盾）⇒ 形式化/paper 偏差确实存在；不能把模型当定理，也不能擅自把目标改成 lit。

## 2. qOrder 是原始整数，无约化

A1026（`coord/QORDER-NORMALIZATION.md`）源码级结论：

- `qOrder` 是 Tate 参数 q 的**归一化整数阶** `orderNat`（相对 uniformizer，uniformizer 无关）；`qOrder_eq_orderNat` / `qOrder_pos` / `coprime_qOrder`；
- **无 mod 2ℓ/ℓ、无约化代表元、无固定区间**；`q_order_coprime` 是对原始整数阶与 ℓ 互素；
- 半稳定 I_n：`qOrder=n`（可任意大）；admissible 仅 ℓ∤n；
- 因此 I_n 大 n 警报成立：`A=qOrder·logp/(2ℓ)` **线性无界**；不能用「qOrder 取模」救活（无源支持）；
- 若 paper variant 隐含 q 的高度界，应在形式化陈述中显式写 `VariantBoundedQ`，否则是偏差。

## 3. 偏差候选（待审计，不是结论）

1. **θ-pilot 的 q 指数**：iv 用单 label `j²`，literal hull 由 `min_l ord_p(q_{v_l})` 控制；实际 Ind1 平均可能给 `j²·m_i/qOrder` 型有效系数（`QORDER-SIGN`/`THETA-LABELS-PAPER`）；需核对 `scaleEltAt` 与 `thetaComponent` 是否真的只取 distinguished label，还是被 Ind1 平均。
2. **A 的归一化 2ℓ**：`qroot` 是 Tate 参数的 `2ℓ`-th root；`ordp_qroot=qOrder/(2ℓ·ramIdx)`；`absLogQ=logQ/(2ℓ)`；若 A 或 qOrder 在某一环多用/少用 2ℓ，会导致 T 的线性项错位；需逐项对 `LeftHandSide.lean:81-93`、`ThetaLocalConstruct/Data.lean:327-330` 审计。
3. **V 是否含 q 项**：`SSINEQ-ANATOMY.md` 当前读法给 `V=logVol(hull(vcI))` **不含 qOrder**；但 iv 不稳定正来自 V q-无关、T 线性；若 paper 的 `log-vol(hull(Θ))` 实际含 q 的项（或 lit 的 min 项），则 `V` 公式不完整，需要重展开。
4. **iv 的 Ind1 平均**：若 iv 实际不是单 label 而是对 Ind1 置换取平均/最小，则有效 `ind2` 不是 0，RHS 可能获得 q-正项；需核对 `ivLabels` 定义与 `thetaComponent` 的并集语义（`indAut` vs label permutation）。
5. **lit 的 gap 恒等式**：本模型用 `gapLit=sF·A`；这是 MODEL 推导，未在 Lean 中证明；`cor312Literal_of_variant` 只是 iv ⇒ lit 的方向，不提供 lit 的 gap 值。
6. **目标选择**：lana `Cor312VariantHolds`（iv）与 `Cor312LiteralHolds`（lit）不等价；ABC 桥只消费 iv；改 lit 需要新的 `lit ⇒ ABC` 桥或重新论证 paper 的 iv 归约。

## 4. 待审计项（按优先级）

| 优先级 | 审计项 | 责任 lane | 判据/产出 |
|---|---|---|---|
| P0 | lana `Iut.MainTheorem` 的 `Cor312VariantHolds` 是**定理还是假设**；ABC 桥是否只是条件消费 | mainline/stepxi | 源码 `MainTheorem.lean:13`/`classicalABC_of_variant` 签名；确认无 variant 证明 |
| P0 | paper 语义：IUT III Cor 3.12 是 lit、IUT IV Steps 是 iv；我们的目标应取哪一个 | lead + shehdd | 读原文/源码 `ThetaRegion:58-74`；给出目标决策 |
| P1 | `V` 是否真的 q-无关；`SSINEQ-ANATOMY` 的公式与 iv 不稳定是否矛盾 | hull | `VcI.lean`/`SSINEQ-ANATOMY` 逐项；给出 V 的 q 依赖审计 |
| P1 | A/`qOrder`/`qroot` 的 2ℓ 归一化是否一致 | qpilot/hull | 对 `LeftHandSide`、`Data.lean:327-330`、`Gap.lean:747` 的指数逐项 |
| P2 | `ind2Term` 的 iv/lit 值（0 vs +j²A）是否只是模型；lana 的 Ind2 值是 Open | hull/stage4 | 对 `DECOMP-PAIRING`/`IND2-*` 与 `Gap.lean` 的定义 |
| P2 | `GAP-VNONNEG`（V≥0）与 lit gap 恒等式是否可 green | hull | `logShellRadius≥0`/packet 体积非负的 green 端口 |
| P3 | 偏差候选 1–4 的数值复算（只用 MODEL/NUMERIC） | qpilot/lattice | 新 CSV/表；不升格为定理 |

## 5. 状态、owner 与下一步

**状态**：MODEL/NUMERIC 审计记录；不是 Lean 定理；不改变 `SSIneq`/`Cor312VariantHolds` 目标；不声称 ABC 进展。

**下一步（可执行）**：

1. mainline/stepxi 核 `MainTheorem.lean` 的 variant 是 assumption 还是 theorem；若只是 assumption，FINAL-STATUS 的“条件装配”口径保持。
2. lead/shehdd 决定目标语义：维持 lana iv（则必须解释 A1027 模型为何不忠实），或改 lit（需新 `lit ⇒ ABC` 桥/重新论证 paper 归约），或加显式 `VariantBoundedQ` 假设（需登记 class-B）；**不得擅自改目标**。
3. hull 审计 `V` 的 q 依赖与 2ℓ 归一化；qpilot 审计 `A/ind2` 的 2ℓ；产出逐项表。
4. stage4 审计本文件与相关 `IND2-*`/`VARIANT-*` 记录；确认没有“MODEL 说成定理”。
5. lattice 保持 FINAL-STATUS/ROUTES/AUDIT_LEDGER 指针；等 owner 决策后更新。

**指针**：`coord/VARIANT-READING-DECISION.md`、`coord/THETA-LABELS-PAPER.md`、`coord/QORDER-NORMALIZATION.md`、`coord/TATE-IN-FAMILY-VARIANTS.md`、`coord/TATE-IN-FAMILY.md`、`coord/SSINEQ-ANATOMY.md`、`coord/IND2-REVIEW.md`、`coord/IND2-CLOSURE.md`。
