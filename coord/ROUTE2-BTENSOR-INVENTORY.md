# ROUTE2-BTENSOR-INVENTORY — 路线二 B-Tensor 盘点（HANDOFF §5.5/§5.6）

| field | value |
|---|---|
| Status | INVENTORY + IMPLEMENTATION（盘点 2026-11-13；新文件 `tmp/sheaf/xif/paper/Mzk1TensorDualCorrectionActual.lean` 已编译 EXIT=0，olean=600896B，trio axioms） |
| 任务 | task-76 / R29-abc：B6 `R ⊆ O_E ⇒ O_E# ⊆ R#`；B7 `#(O_E/R)=#(R#/O_E#)`；张量积对偶比较；整闭包指数损失 → 对偶侧有限商 |
| 结论 | B6 已有**generic green 定理**（`integralTraceDualLattice_antitone`）；张量/积的 dual 已有 green 分解（`traceDualLattice_pi`）；B7 的**基数计算工具**已有 green（`natCard_quotient_span_padicInt_pow` 等），但“指数损失 = 对偶商”的 **SNF 对偶恒等**未证（GAP-DUAL-SNF）；不同理想的 rank-one 情形有 green 定理（FinitePlaceHolomorphicDifferentBase，但该文件当前 olean=False）。 |

## 1. 文件与关键定理（file:line，olean 状态）

### 1.1 `LeanFormal/IUT/Foundations/LocalFields/IntegralTraceDualTensorInclusion.lean`（1057 行，**olean=True/green**）

| 定理/定义 | 行 | 内容 |
|---|---|---|
| `matrix_charpoly_root_isRoot_of_aeval_eq_zero` | :107 | 矩阵特征多项式根 |
| `algebra_trace_isIntegral` | :155 | trace 整性 |
| `piTensorProduct_trace_tprod` | :169 | 张量积的 trace 乘法公式 |
| `padicIntegralTraceDualLattice_basisIntegralLattice_eq_basisIntegralLattice` | :209 | 基格对偶 |
| `arithmeticTupleValuationIntegerRegion` | :278 | 实际 tensor 整数区域 |
| `arithmeticTupleValuationIntegerLattice_eq_span` | :287 | 整数格 = span |
| `arithmeticTupleValuationIntegerQpBasis` | :293 | Qp 基 |
| `arithmeticTupleValuationIntegerDualQpBasis` | :346 | 对偶基 |
| `arithmeticTupleValuationIntegerLattice_eq_basisIntegralLattice` | :352 | 整数格 = 基格 |
| `isIntegral_arithmeticTupleValuationIntegerSubalgebra` | :484 | 整性 |
| `arithmeticTupleValuationIntegerNormalization_le_traceDual` | :540 | **normalization ⊆ traceDual**（B6 方向之一） |
| `integersIsIntegralClosure` | :623 | 整数环是整闭包实例 |
| `localDifferentIdeal` / `localDifferentGenerator` | :643 / :652 | 局部不同理想/生成元 |
| `localDifferentOrder` / `localDifferentPaperOrder` | :693 / :701 | 不同指数 |
| `localDifferentGenerator_mul_mem_integralTraceDual` | :768 | different·dual ⊆ integral |
| `arithmeticTensorDifferentGenerator` | :807 | tensor different 生成元 |
| `arithmeticTensorDifferentGenerator_mul_mem_traceDual` | :964 | tensor different × traceDual ⊆ lattice |
| `arithmeticTensorDifferentGeneratorMulSubmodule` | :1013 | different 乘子子模 |
| `arithmeticTensorPaperDifferentScale` | :1036 | paper different scale |

**覆盖**：actual tensor 整数格 / 对偶基 / different 生成元 / trace-dual 包含（B6 的 tensor 实例化素材）；**未覆盖**：B7 的商基数等式（不同文件）。

### 1.2 `LeanFormal/IUT/Foundations/LocalFields/IntegralTraceDualLattice.lean`（450 行，**green**）

| 定理/定义 | 行 | 内容 |
|---|---|---|
| `integralTraceDualLattice B L` | :50 | 一般整对偶 |
| `mem_integralTraceDualLattice_iff` | :56 | 成员刻画 |
| **`integralTraceDualLattice_antitone`** | **:75** | **B6 的 generic 形式：L₁⊆L₂ ⇒ L₂#⊆L₁#** |
| `le_flip_integralTraceDualLattice` | :82 | 翻转 pairing 对偶 |
| `integralTraceDualLattice_span_basis` | :94 | 基格对偶 = 对偶基 span |
| `padicIntegralTraceDualLattice` | :108 | ℤp 特化 |
| `mem_padicIntegralTraceDualLattice_iff` | :112 | 成员 |
| `padicIntegralTraceDualLattice_span_basis` | :118 | 基格 |
| `integralTraceDualLattice_traceForm_eq_traceDual` | :394 | **整对偶 = Mathlib `Submodule.traceDual`（复用它可接 Mathlib）** |
| `mem_traceDual_iff_traceForm_mem` | :403 | traceForm 成员 |
| `mul_le_traceDual_one_of_le_traceDual` | :411 | 乘法对偶 |
| `coeSubmodule_differentIdeal_eq_inv_traceDual` | :431 | **different = (traceDual 1)^{-1}** |
| `differentIdeal_le_iff_traceForm_le_one` | :438 | different 判据 |

### 1.3 `LeanFormal/IUT/Foundations/LocalFields/DifferentTraceProduct.lean`（238 行，**green**）

| 定理/定义 | 行 | 内容 |
|---|---|---|
| `trace_pi` | :26 | 积的 trace = 分量 trace 和 |
| `traceDualLattice R K B A` | :49 | 实际整数像的 trace dual（乘积也定义） |
| `traceMultiplierIdeal` | :53 | 乘子理想 |
| `mem_traceMultiplierIdeal` | :67 | 成员 |
| `dualSubmodule_pi` | :81 | **积的对偶 = 分量对偶的积** |
| `integralImage_pi` | :142 | 整数像 = 分量积 |
| **`traceDualLattice_pi`** | **:151** | **张量/积对偶分解（§5.6 入口）** |
| `mem_traceMultiplierIdeal_pi` | :158 | 乘子理想分量化 |
| `traceMultiplierIdeal_eq_differentIdeal` | :192 | **乘子理想 = different ideal** |
| `mem_traceMultiplierIdeal_pi_iff_mem_differentIdeal` | :230 | 分量不同理想 |

### 1.4 `LeanFormal/IUT/Foundations/LocalFields/PadicLatticeIndexFormula.lean`（250 行，**green**）

| 定理/定义 | 行 | 内容 |
|---|---|---|
| `natCard_quotient_eq_prod_span_of_smithNormalForm` | :37 | SNF 商基数 |
| `exists_smithNormalForm_and_natCard_quotient_eq_prod_span` | :95 | SNF 存在 |
| `padicIntQuotientEquivZMod` | :123 | `ℤp/p^n ≅ ZMod(p^n)` |
| **`natCard_quotient_span_padicInt_pow`** | **:130** | **`#(ℤp/p^n)=p^n`（B7 rank-one 可计算）** |
| `natCard_quotient_span_padicInt_eq_pow_valuation` | :144 | `#(ℤp/(a))=p^{v(a)}` |
| `natCard_quotient_eq_prod_pow_valuation_of_rankEq` | :193 | 一般格指数公式 |
| `natCard_quotient_eq_prod_pow_valuation_of_finiteFree` | :222 | finite free 版（被 FinitePlaceHolomorphicIntegerIndex:258 使用） |

### 1.5 `LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceHolomorphicDifferentBase.lean`（117 行，**olean=False/红**）

| 定理 | 行 | 内容 |
|---|---|---|
| `traceDual_one_le_one_self` | :39 | traceDual 1 ⊇ 1（rank-one） |
| `differentIdeal_self_eq_top` | :56 | different(ℤp,ℤp)=⊤ |
| `differentIdeal_padicInt_self_eq_top` | :69 | 同上 |
| `cardQuot_differentIdeal_padicInt_self_eq_one` | :74 | `#(ℤp/different)=1` |
| `prod_cardQuot_differentIdeal_padicInt_self_eq_one` | :80 | 积 |
| `arithmeticTupleIntegerTensorHolomorphicIndex_eq_one_of_differentInterface_rankOne` | :97 | rank-one index=1 |
**注**：该文件当前 olean=False（红），盘点可用、**不要 import 依赖**；若需其结论可在新文件重新证明或等修复。

### 1.6 `LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceStepVAssembly.lean`（864 行，green）

与 B-Tensor 相关的 green 结论：`arithmeticTupleValuationIntegerLattice_mul_holomorphicLattice` :48（整数格乘 holomorphic 格）、`arithmeticTupleLocalDifferent_ne_zero` :576、`arithmeticTupleTprod_localDifferent_mul_mem` :585、`arithmeticTuple_stepV_normalizedLogVolume_le_paperBound` :602、`arithmeticTupleHolomorphicHull` :752、`arithmeticTuple_stepV_hull_normalizedLogVolume_le_paperBound` :814。
**覆盖**：different 与 log-volume/Step V 的绿色接口；**未覆盖**：B6/B7 的泛函代数证明本身。

## 2. (B6)/(B7) 覆盖对照

| 论断 | 已有 green | 缺口 |
|---|---|---|
| (B6) `R ⊆ O_E ⇒ O_E# ⊆ R#` | **generic** `integralTraceDualLattice_antitone`（IntegralTraceDualLattice:75）；trace 形式 = Mathlib `Submodule.traceDual` 的单调性（可由 `mem_traceDual` 直接证） | 无本质缺口；只需在新文件写 trace-form wrapper |
| (B7) `#(O_E/R)=#(R#/O_E#)` | 商基数工具（PadicLatticeIndexFormula:130/144/222）；SNF 商基数（:37/107）；different 判据（:431/438） | **GAP-DUAL-SNF**：对偶基的 SNF 系数 = 原 SNF 系数的逆（`#(O/R) = ∏ p^{v(a_i)}`，`#(R#/O#) = ∏ p^{v(a_i^{-1})}`）未形式化；Mathlib `Submodule.traceDual` 无 cardinal 公式 |
| 整闭包指数损失 → 对偶侧有限商 | `arithmeticTupleValuationIntegerNormalization_le_traceDual`（TensorInclusion:540）；`localDifferentGenerator_mul_mem_integralTraceDual` :768 | 需要把“R ⊆ O_E 的指数”与“different/对偶商”在同一对象上对齐（GAP-INDEX-DUAL） |
| 张量积对偶比较 | `traceDualLattice_pi`（DifferentTraceProduct:151）、`dualSubmodule_pi` :81、`piTensorProduct_trace_tprod`（TensorInclusion:169） | 不能把 `O_E#` 直接替换为因子对偶的张量积（HANDOFF §5.5 明言）——R 与 O_E 的差仍在 |
| 不同理想实际入口 | `localDifferentIdeal`/`localDifferentGenerator`（TensorInclusion:643/652）；`coeSubmodule_differentIdeal_eq_inv_traceDual`（IntegralTraceDualLattice:431） | 与 B7 商基数的对接（GAP-DIFFERENT-INDEX） |

## 3. 本任务 Lean 文件（Mzk1TensorDualCorrectionActual，已实现并编译）

1. **B6 generic** ✅：`b6_integralTraceDual_subset`（复用 `integralTraceDualLattice_antitone`）；`b6_traceDual_subset`（由 `Submodule.mem_traceDual` 证）。
2. **B7 充分条件** ✅：`TraceDualQuotientEquiv`（两个有限商的显式等价）+ `b7_card_eq_of_equiv`（`Nat.card_congr`，真证）。
3. **B7 可计算实例** ✅：`b7_rank_one_padicInt_card`（`#(ℤp/p^n)=p^n`）、`b7_rank_one_padicInt_card_valuation`（`#(ℤp/(a))=p^{v(a)}`）re-export。
4. **B8** ✅：`b8_dual_span_le_iInf`（dual of span ⊆ iInf duals，真证）。
5. **明确 GAP**：GAP-DUAL-SNF（对偶 SNF 系数逆关系；`TraceDualQuotientEquiv` 是显式数据）；GAP-INDEX-DUAL（R/O_E 指数 ↔ different 商）；不得把 `R=O_E` 当默认。
6. **编译证据**：`lake env lean -R . -o .lake/build/lib/lean/tmp/sheaf/xif/paper/Mzk1TensorDualCorrectionActual.olean tmp/sheaf/xif/paper/Mzk1TensorDualCorrectionActual.lean` → `EXIT=0`；olean 600896 B；`#print axioms` 五个定理均为 `[propext, Classical.choice, Quot.sound]`。

## 4. 结论

1. B6 是**现成 green**（generic antitone + trace-form 直接 wrapper）；
2. 张量积对偶分解 green（`traceDualLattice_pi`），但 HANDOFF 警告的 `O_E#` vs 因子张量积差别仍需保留；
3. B7 的可计算工具 green（`p^n` 商基数），但“指数损失 = 对偶有限商”的完整等式缺 **GAP-DUAL-SNF**；
4. `FinitePlaceHolomorphicDifferentBase` 当前红，不作为依赖；其 rank-one 结论可在新文件外独立引用（待其转 green）。
---

## 5. R29b 更新（task-82：B7 实质化进展）

| field | value |
|---|---|
| Status | B7 **部分实质化**：配对映射的下降与核已真证；完整基数等式仍缺 GAP-PERFECT-DUAL（有限 abelian 对偶 `#Hom(A, Qp/Zp)=#A` 未形式化） |
| Build | `lake env lean -R . -o .lake/build/lib/lean/tmp/sheaf/xif/paper/Mzk1TensorDualCorrectionActual.olean tmp/sheaf/xif/paper/Mzk1TensorDualCorrectionActual.lean` → **EXIT=0**；olean 649048 B；`#print axioms` 全部 `[propext, Classical.choice, Quot.sound]` |

新增真证定理（`tmp/sheaf/xif/paper/Mzk1TensorDualCorrectionActual.lean`）：
```
b7_pairing_integrality  : x ∈ I#, y - z ∈ I ⇒ B x y - B x z ∈ ℤp         （:105 附近）
b7_pairing_kernel       : (∀ y∈J, B x y ∈ ℤp) ↔ x ∈ J#                  （:115 附近）
```
含义：实际 trace pairing 在 `I# × (J/I) → ℚp/ℤp` 上良定义（下降），且核 = `J#`；
这给出 `I#/J# ↪ Hom(J/I, ℚp/ℤp)` 的**实际来源**（不再是显式等价数据）。

仍缺的桥：
```
GAP-PERFECT-DUAL：上述下降映射的满射性（完美配对）——需对任意 φ : J/I → ℚp/ℤp 找 x∈I#
GAP-FINITE-DUAL：有限 abelian 群对偶 `#Hom(A, ℚp/ℤp) = #A`（A=J/I）——Mathlib 无现成结果
GAP-DUAL-SNF：Gram/SNF 路线（IntegralTraceDualLattice:300 的 det 公式 + dual Gram = inverse）
  亦可给 B7，但需要 det 的对偶恒等式（未形式化）
```

### 5.1 `FinitePlaceHolomorphicDifferentBase.lean` red 证据
```
lake env lean ... FinitePlaceHolomorphicDifferentBase.lean → EXIT=1
L62:6 error: synthesized type class instance not definitionally equal: Algebra.id (FractionRing A) vs
        FractionRing.liftAlgebra A (FractionRing A)  （@traceDual ... 自扩张）
L64:2 error: Type mismatch  traceDual_one_le_one_self has type ... Algebra.id ...
        but expected ... FractionRing.liftAlgebra ...
⇒ 需要统一 FractionRing 自代数的 Algebra 实例（或改写 differentIdeal_self_eq_top 不使用该引理）；
  当前不 import；rank-one 结论 :39/:74/:97 已由错误阻断。
```
---

## 6. R29h：Gram/坐标行列式路线盘点 + task-82 收尾（2026-11-13）

| 步骤 | 已有覆盖（file:line） | 缺口 |
|---|---|---|
| 1. Haar 缩放 `μ0(Λ)=|det B|_p`（坐标模型） | `FinitePadicHaarScaling.lean:25 measure_prime_smul_finiteDimensional`（标量 p）、`:54 log_measure...`；`PadicFiniteCoordinateHaarScaling.lean:30 measure_prime_smul_padicIntegerCoordinateLattice`、`:85 measure_prime_smul_finiteCoordinates`、`:67 distribHaarChar_prime_finiteCoordinates` | **一般 B ∈ GL_d(Q_p)** 的 det 缩放未证；仅有标量 p（及 p^k 的迭代可补）；**Step 1 未完成** |
| 2. 对偶基格 `Λ# = (S^{-1}B^{-T})·Z_p^d`（B2） | `IntegralTraceDualLattice.lean:94 integralTraceDualLattice_span_basis`、`:118 padicIntegralTraceDualLattice_span_basis`；Gram 矩阵 `:270 traceDualGramMatrix`、`:300 natCard_traceDual_quotient_eq_pow_valuation_gram_det` | 需要把 Gram 矩阵写成 `S` 并证明 dual Gram = S⁻¹；`span` 形式已有，矩阵包装未做 |
| 3. `μ0(Λ)·μ0(Λ#)=|det S|_p^{-1}`（B4/B5 前身） | 依赖 1、2；无现成 | **未证**；曾尝试写标量 `p^k` 的迭代版（在 `Mzk1TensorDualCorrectionActual.lean` 加 section），因 `Set` smul/`HAdd` binder 问题未过编译，已**回退删除**（文件恢复为已交付的 B6/B7-部分/B8 版本） |
| 4. 相对形式 `(μ(Λ)/μ(O))·(μ(Λ#)/μ(O#))=1` | `CompactOpenAddSubgroupIndex.lean:23 intersectionInLeft`、`:25 intersectionIndex`、`:46 measure_eq_index_mul_intersection`；`PadicLatticeIndexFormula.lean:130/144/222` 商基数 | 需 1-3；**未证** |

**task-82 收尾状态**：B6（generic + trace-form）、B7 的配对下降/核（`b7_pairing_integrality`/`b7_pairing_kernel`）、B8、B7 的显式商等价接口与 rank-one 商基数已交付；**完整 B7（Gram/SNF 基数等式）与 Gram 路线 Step 1/3/4 仍未证**，已作为 GAP-DUAL-SNF/GAP-INDEX-DUAL 记录。按 Lead 指示 task-82 关闭（交付=盘点+已证部分+精确缺口），后续可继续 Gram 路线。

**统一编译约定**：本文件及 `Mzk1TensorDualCorrectionActual.lean` 不再由本人编译；以 `dag/watchdog/watchdog.log` 的 START/DONE/FAIL 为准（该文件历史 log 中的 FAIL 属中间破坏版本，已回退修复内容）。