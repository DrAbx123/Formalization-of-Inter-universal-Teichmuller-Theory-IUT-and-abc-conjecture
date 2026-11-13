# P3-MINIMAL-ACCEPTANCE — §9.6 最小真实验收例（qVFam 块）

日期：2026-11-13；R29j/task-90；Status：**PARTIAL / actual-node + GAPs**。
纪律：不改题、不新增假设、不 toy/PUnit/True carrier、不手工编译；新文件待 Lead 加入 watchdog 启动列表。

## 0. 结论先行

- 已定义实际格 `LambdaG = F(c_root)·O_hol` 在真实 `qVFamTensorBlock T b` 上（不是抽象 finite 模型），并证 `LambdaG ⊆ paperRootThetaImageNZ`（j=1 非零标签像）⇒ `LambdaG ⊆ closure(paperRootThetaImageNZ)`。
- 已给出 normalized log-volume 公式 `-(∑ c_i) log p` 的 Lean 定理，但它**条件于** `ArithmeticTuplePureFractionalScalingData ... (paperRootCoefficientFamily)`；该 actual scaling data 仍未构造（现有 qVFam normalized data 是 `rootHalfCoefficient`，不是 paper coefficient family）。
- 精确 μ 比值可写成 `p^{r}`，`r = -d * ∑_i c_i`，`d = finrankℚp(qVFamTensorBlock T b)`，`c_i = paperRootCoefficientFamily T b i`；这是 normalized log 公式的指数形式。
- **迹对偶同一相对体积：GAP**。现有 B4/B5 只覆盖 scalar `p^k•O`（task-75），不覆盖一般 fractional `c_root`；缺 actual trace pairing/Gram、B2 矩阵与 general-Haar 缩放/交格上界。
- 按 lead 更新：qVFam 块上 `paperRootThetaImageNZ = F(c_root)·O_hol` 是公共标量族，相对 index 不随 m 增长；增益只能来自 Ind2/gap。本验收例**不是目标增益**，只登记实际有限生成下界与可计算的相对体积。

## 1. 对象与文件

| 对象 | 定义/来源 | 状态 |
|---|---|---|
| 块 `qVFamTensorBlock T b` | `QVFamTensorCoefficientActual.lean` | actual 有限维 Qp 载体（one-factor `Unit` 索引） |
| 参照 `O_i` | `arithmeticTupleCanonicalUnitReference (qVFamTensorPlaces T b) qVFamTensorTuple` | actual compact/open canonical unit reference |
| `paperRootThetaImageNZ` | `S793PaperLeastLambdaOHullActual.lean:79-80`（j≠0 union） | actual 定义；当前不是 `Mzk1PaperFaithfulHullActual`（该文件 FAIL，无 olean） |
| `Λ_G` | 本文件 `Mzk1MinimalAcceptanceActual.lean:56`；`F(c_root)·O_hol` | actual submodule；有限生成由 fractional lattice 的 pure-tensor 生成元给出（`ArithmeticTuplePureFractionalScalingData` 的 `localGenerator`） |
| `paperFaithfulThetaHullNZ` | 本文件 `:84` = `closure paperRootThetaImageNZ` | 局部诚实 hull；**不是** import `Mzk1PaperFaithfulHullActual` |

## 2. §9.6 清单逐项

| §9.6 项 | 本节点状态 | file:line / GAP |
|---|---|---|
| (1) 来源作用矩阵 G(T,i) | **GAP** | 未构造 `G`；`LambdaG` 是 `F(c_root)·O_hol`，其生成元来自 fractional scaling data；显式 G 矩阵/来源作用仍未给 |
| (1) 迹矩阵 S(T,i) | **GAP** | qVFam block 的实际 trace pairing/Gram 未构造；`B` 仍是任意 nondegenerate bilinear，不是 paper trace |
| (2) `Λ_G ⊆ H_Θ` | **PROVED（实际 containment）** | `Mzk1MinimalAcceptanceActual.lean:70` `LambdaG_subset_paperRootThetaImageNZ`；`:87` `LambdaG_subset_paperFaithfulThetaHullNZ`（本地 closure hull） |
| (3) `μ(Λ_G)/μ(O_i)=p^{r(T,i)}` | **CONDITIONAL** | `:94` `LambdaG_normalizedLogVolume`；条件 `data : ArithmeticTuplePureFractionalScalingData ... paperRootCoefficientFamily` 未构造；公式 `r = -d * ∑ c_i` |
| (4) 对偶侧同一相对体积 | **GAP** | task-75 scalar B4/B5 only; general `c_root` + trace dual 未证；缺 B2 矩阵/general-Haar 缩放/交格上界 |
| (5) file:line / build | **DONE** | 新文件 `tmp/sheaf/xif/paper/Mzk1MinimalAcceptanceActual.lean`（5,858B）；watchdog **DONE EXIT=0 @20:44:49Z（102s）**，olean 136,128B @04:44:48 fresh |

## 3. 已证明的 Lean 节点（名称+file:line；build 待 watchdog）

| 定理/定义 | file:line | 内容 |
|---|---|---|
| `LambdaG` | `Mzk1MinimalAcceptanceActual.lean:56` | `F(c_root)·O_hol` actual submodule |
| `LambdaG_eq_paperLambdaORegion` | `:63` | 展开为 S793 `paperLambdaORegion` |
| `LambdaG_subset_paperRootThetaImageNZ` | `:68` | 取 j=1 非零标签像，Λ_G⊆paper image |
| `paperFaithfulThetaHullNZ` | `:82` | 本地 `closure(paperRootThetaImageNZ)` |
| `LambdaG_subset_paperFaithfulThetaHullNZ` | `:85` | Λ_G⊆hull |
| `LambdaG_normalizedLogVolume` | `:94` | 条件于 actual data 的 `-(∑ c_i) log p` |

**build 状态**：watchdog `START 20:43:07.828Z` → **DONE EXIT=0 20:44:49.380Z（102s）**；olean 136,128B @04:44:48 local，fresh。未手工编译。

## 4. 精确 μ 比值

令 `d = Module.finrank ℚ_[qVFamTensorP T b] (qVFamTensorBlock T b)`，`c_i = paperRootCoefficientFamily T b i`。`arithmeticTupleNormalizedLogVolume` 定义为 `(1/d)(log μS - log μO_i)`；由 `LambdaG_normalizedLogVolume` 得
```text
log (μ(Λ_G)/μ(O_i)) = -d * (∑ i, c_i) * log p
μ(Λ_G)/μ(O_i) = p^{r(T,i)},   r(T,i) = -d * ∑ i c_i.
```
这是精确表达式（不是数值近似）；**但条件 `data` 尚未构造**，所以不宣称 unconditional。

## 5. 迹对偶侧：缺哪条桥

1. **actual trace pairing**：qVFam block 的 `Tr_{E/Q_p}`（或 `qVFam` 有限 étale 代数的 trace）没有作为该 block 的实际 bilinear form 构造；task-75 的 `B` 是任意 nondegenerate form。
2. **B2 矩阵**：`S^{-1}B^{-T}` 的显式 Gram/矩阵公式在 task-75 盘点为 GAP；这里需要 qVFam 实际 `S`/生成矩阵 `G`。
3. **general c_root 的 Haar 缩放**：task-75 B4/B5 只覆盖 `L=p^k•O` scalar；`c_root=m/(2l)` 的 fractional lattice 不是 `p^k` scalar，需 general determinant-Haar/Smith 公式。
4. **交格上界/B8**：`X_G = {x : G^T S x ∈ Z_p^r}` 与 `Λ_G#` 的同一性/体积上界未构造；B8 亦 GAP。
5. **同一相对体积**：上述桥补齐前，不能声称对偶侧给出相同 `p^r`；只能报告 scalar B4/B5 工具已闭合。

## 5a. 对偶侧首版（task-102，new file 待 watchdog）

新文件：`tmp/sheaf/xif/paper/Mzk1DualIntersectionActual.lean`（3,960B）；watchdog **DONE EXIT=0 @20:52:22Z（62s）**，olean 99,568B @04:52:21 fresh。

| 节点 | file:line | 状态 |
|---|---|---|
| `qVFamTraceForm` | `Mzk1DualIntersectionActual.lean:47` | actual `Algebra.traceForm` on `qVFamTensorBlock` |
| `qVFamTraceBasis` | `:57` | actual `arithmeticTupleValuationIntegerQpBasis`（multiFactorQpBasis） |
| `qVFamTraceGram` | `:64` | actual Gram `S`（entries = trace pairing） |
| `qVFamTraceGram_apply` | `:71` | rfl 等式，未用抽象整数 |
| `XG` | `:80` | actual `padicIntegralTraceDualLattice` of `LambdaG` |
| `XG_eq_traceDual` | `:84` | 定义性双对偶对象（rfl） |

**仍缺**：
1. `XG = {x | G^T S x ∈ Z_p^r}` 的矩阵交格等式未证；`G` 作为 `LambdaG` 的显式生成矩阵也未给。
2. `μ(Λ_G)/μ(O_i)` 与 `μ(X_G)/μ(O_i#)` 同一相对体积未证；一般 `c_root` 的 B4/B5 缺 general-Haar/Smith 桥（task-75 scalar p^k 仅工具）。
3. `O_i#` 的基准与 `qVFamTraceGram` 的整性/非退化补全未证；`qVFamTraceGram` 现在只是 trace pairing 矩阵，不是 dual 矩阵 `G^T S`。

**build**：watchdog `START 20:51:20.615Z` → **DONE EXIT=0 20:52:22.682Z（62s）**；olean 99,568B @04:52:21 local，fresh。未手编。

## 5b. 一般满格 (B4)/(B5) 首版（task-104，new file 待 watchdog）

新文件：`tmp/sheaf/xif/paper/Mzk1GeneralDualVolumeActual.lean`（3,856B）；watchdog **DONE EXIT=0 @20:59:03Z（28s）**，olean 139,064B @04:59:03 fresh。

已写条件核心：`RelativeHaarScaling`（:30，相对缩放条件）；`relativeHaarVolume_product_of_scaling`（:37，由 `μL=cμO`、`μL#=c⁻¹μO#` 推出乘积恒等式）；`relativeLogVolume_neg_of_product`（:53，正性/有限性下推出 B5 log 形式）。

**精确 GAP（task-104 未完成部分）**：
1. `GAP-DET-HAAR`：一般 `B ∈ GL_d(Q_p)` 的 `μ(B•Z_p^d)=|det B|_p·μ(Z_p^d)` 未证；需 SNF `B=V·diag(p^{e_i})·W`、`GL_d(Z_p)` 保持格/Haar、`measure_prime_smul_finiteDimensional` 组合。
2. `GAP-DUAL-TRANSPOSE`：`(B O)# = B^{-T}O#` 的实际 trace pairing 关系未证。
3. `GAP-QVFAM`：推广到 qVFamTensorBlock（multiFactorQpBasis/dualBasis/pi 分解）未证。

**build**：watchdog `START 20:58:35.583Z` → **DONE EXIT=0 20:59:03.565Z（28s）**；olean 139,064B @04:59:03 local，fresh。未手编。`Mzk1TraceDualVolumeActual` 的 scalar p^k B4/B5 亦 green（task-75）。

### 5b.1 SNF 路线当前阻塞（2026-11-13 05:xx）

- **矩阵 SNF 不可得**：仓库/Mathlib 的 `Submodule.smithNormalForm` 是“子模相对于基”的 SNF，不是任意 `B ∈ GL_d(Q_p)` 的 `B=V·diag(p^{e_i})·W` 矩阵分解；没有直接定理可调用。
- **`GL_d(Z_p)` 保 Haar/格**：需实际证明 `V,W ∈ GL_d(Z_p)` 给出 `V '' Z_p^d = Z_p^d` 及 Haar 不变；仓库没有现成打包定理。
- **对角缩放**：现有 `measure_prime_smul_finiteDimensional` 只支持整体 `p` 幂，不支持逐坐标 `p^{e_i}` 的乘积；需额外 product-Haar 公式。
- **`(BΛ)#=B^{-T}Λ#`**：需 trace pairing 的 adjoint/transpose；当前 `Mzk1DualIntersectionActual` 只有 `Algebra.traceForm` 与 Gram，无一般 B 的 dual transport。
- 结论：一般 `B4/B5` 不是一处小补，需新增 SNF/矩阵分解与 product-Haar 两块基础；当前只交付条件核心（`relativeHaarVolume_product_of_scaling` / `relativeLogVolume_neg_of_product`），不冒充一般版本。

## 5b.2 受限矩阵 Haar 基础（task-109，new file 待 watchdog）

新文件：`tmp/sheaf/xif/paper/Mzk1MatrixHaarBaseActual.lean`（5,023B）；watchdog **DONE EXIT=0 @21:46:58Z（39s）**，olean 204,384B @05:46:58 fresh。

| 项 | 状态 | 说明 |
|---|---|---|
| 坐标格 `Z_p^d` | actual | `coordLattice := padicIntegerCoordinateLattice` |
| GL_d(Z_p) 矩阵作用 | actual | `glMatrix`/`glAct`（矩阵扩展到 Q_p） |
| `glAct_mem_coordLattice` | **DONE** | :49，积分矩阵 V '' Z_p^d ⊆ Z_p^d 逐坐标证明 |
| `glAct_image_eq_of_mul_eq_one` | **DONE** | :81；显式逆 W、`V*W=1` ⇒ `V''Z_p^d=Z_p^d` |
| Haar 不变 μ(V''S)=μ(S) | **GAP** | 需 Haar 唯一性 + lattice mass 归一化；未构造 |
| `diagAct`/`diagAct_image_coordLattice` | **DONE** | :93/:96；逐坐标 p^{e_i} 像 = 坐标缩放格 |
| 对角坐标缩放乘积公式 | **GAP** | 逐坐标 p^{e_i} 的 product-Haar 未证 |
| 受限 det 公式 | **GAP** | 需 SNF/矩阵分解 + 上述 Haar 不变；doc §5b.1 |

**build**：watchdog START 21:46:19Z → DONE EXIT=0 21:46:58Z（39s）；olean 204,384B fresh。未手编。

### 5b.3 Haar 不变当前精确条件（task-109）

已被证明的格部分：`glAct_image_eq_of_mul_eq_one`（显式逆 `W`，`V*W=1`）给出 `V '' Z_p^d = Z_p^d`。

要得到 `μ(V '' S)=μ(S)`，还需以下条件/步骤（未完成，标 GAP）：
1. **连续线性等价**：把 `glAct V` 打包成 `ContinuousLinearEquiv`（需 `V,W` 双向逆且有限维 Q_p 连续性）；当前只有矩阵/`mulVec` 作用。
2. **Haar 传输**：定义 `ν = μ.map (glAct V)`，证明 `[IsAddHaarMeasure ν]`；需 `Measurable`/连续与加法同胚。
3. **归一化**：用 `measure_isAddInvariant_eq_smul_of_isCompact_closure` 得 `ν = c • μ`（c=`addHaarScalarFactor ν μ`）；在 `coordLattice` 上 `ν O = μ O`（用 1）⇒ c=1。
4. **全 sets 推广**：uniqueness 直接给 compact closure 集；全集需内正则/regular 扩展。

**精确条件版**：若暂时不构造 `ContinuousLinearEquiv`，可把 `hν : IsAddHaarMeasure (μ.map (glAct V))`、`hmeas`、`c=1` 作为显式条件；等价地 `μ(V''Z_p^d)=μ(Z_p^d)` 是 c=1 的归一化条件。本文件**不**把该条件写成无条件定理。

### 5b.4 对角 quotient cardinal（task-109，green）

新文件：`tmp/sheaf/xif/paper/Mzk1DiagonalIndexActual.lean`（2,367B）；watchdog **DONE EXIT=0 @22:15:01Z（32s）**，olean 67,144B @06:15:01 fresh。

- `diagLatticeSubmodule e := ∏ i, (p^{e_i}) ⊂ d→Z_p`；
- **`natCard_quotient_diagLatticeSubmodule`**：`Nat.card ((d→Z_p) ⧸ ∏ p^{e_i}) = ∏ i, p^{e_i}`，用 `Submodule.quotientPi` + `natCard_quotient_span_padicInt_pow` + `Nat.card_pi`。

**仍缺（μ scaling）**：
1. 把 `diagLatticeSubmodule` 经 `integerProductEmbedding` 映到 `d→Q_p` 的紧开子群 `L'`；
2. 证 `L' ⊆ Z_p^d` 且 `Z_p^d ∩ L' = L'`；
3. 证 `#(Z_p^d/L') = ∏ p^{e_i}`（需把 `(d→Z_p)/diagLatticeSubmodule` 与 `Z_p^d/L'` 的商等价写出来）；
4. 用 `CompactOpenAddSubgroup.measure_eq_index_mul_intersection` 得 `μ(Z_p^d)=#(Z_p^d/L')·μ(L')`。

当前只完成 3 的 cardinal 端；4 的 measure 端、受限 det 仍 GAP。

### 5b.5 坐标置换不变性（task-109，green）

新文件：`tmp/sheaf/xif/paper/Mzk1PermutationHaarActual.lean`（2,543B）；watchdog **DONE EXIT=0 @22:22:53Z（23s）**，olean 75,208B @06:22:53 fresh。

- `permAct σ x i = x (σ i)`（:31）；
- `permAct_image_coordLattice`（:39）：实际置换 `P_σ` 保 `Z_p^d`；
- **`measure_pi_perm_coordLattice`**（:53）：product-Haar mass `μ(P_σ''Z_p^d)=μ(Z_p^d)`，由像集相等直接得。

这是 `GL_d(Z_p)` Haar 不变性的**置换子群情形**；一般矩阵 `V ∈ GL_d(Z_p)` 的 Haar 不变仍 GAP。

### 5b.6 批处理小文件（task-109，均 watchdog green）

| file | size | watchdog | olean | 内容/边界 |
|---|---|---|---|---|
| `Mzk1GLActBundlingActual.lean` | 971B | DONE 22:37:07Z（40s） | 35,912B | `glLinear` Q_p-linear 打包；连续等价 GAP |
| `Mzk1DiagonalProductScalingConditionActual.lean` | 925B | DONE 22:41:21Z（36s） | 30,880B | 对角 quotient cardinal re-export；measure scaling GAP |
| `Mzk1RestrictedDetConditionalActual.lean` | 1,304B | DONE 22:31:13Z（51s） | 35,000B | restricted det 条件乘积（task-104 green core）；SNF/det-Haar GAP |
| `Mzk1DiagonalPermutationActual.lean` | 1,147B | DONE 22:37:00Z（41s） | 35,008B | `diagPermAct = permAct ∘ diagAct`；measure invariance GAP |
| `Mzk1GLHaarConditionalActual.lean` | 1,559B | DONE 22:49:05Z（36s） | 31,016B | `GLHaarInvarianceCondition` 精确条件；c=1/Haar uniqueness GAP |

**说明**：GLHaarConditional 原尝试直接调用 additive Haar uniqueness，但该 olean 上下文里 `addHaarScalarFactor` / `measure_isAddInvariant_eq_smul_of_isCompact_closure` 无法解析；已降为精确条件定义，不冒充无条件 GL 不变。置换子群 `Mzk1PermutationHaarActual` 仍独立 green。

### 5b.7 c=1 Haar scalar 归一化（task-109，green 条件步）

新文件：`tmp/sheaf/xif/paper/Mzk1HaarScalarOneActual.lean`（5,064B）；watchdog **DONE EXIT=0 @23:17:30Z（52s）**，olean 156,696B @07:17:30 fresh。

- `addHaarScalarFactor_eq_one_of_lattice`（:22）：
  `L : (d→Q_p) ≃L[Q_p] (d→Q_p)`，μ additive Haar，`coordLattice` 开、`0<μO<⊤`；
  若 `(μ.map L) O = μ O`（`hνO`），则 `addHaarScalarFactor (μ.map L) μ = 1`。
- 使用 `ContinuousLinearEquiv.isAddHaarMeasure_map` + `Measure.measure_isAddHaarMeasure_eq_smul_of_isOpen`（命名空间 `MeasureTheory.Measure`）。
- `map_coordLattice_eq_of_image_eq`（:48）：由 image 等号 + `Measure.map_apply` 得 `(μ.map L) O = μ O`。
- `addHaarScalarFactor_eq_one_of_image`（:72）：直接由 image 等号得 c=1。
- **`map_eq_of_image_eq`（:87）**：在 `[Measure.OuterRegular μ]` 与 `[Measure.OuterRegular (μ.map L)]` 下，由开集相等经 `Measure.OuterRegular.ext_isOpen` 得 `μ.map L = μ`（全可测集）。

**仍 GAP**：实际 Haar 的 `OuterRegular` 实例（一般局部紧/第二可数来源）；矩阵 `glAct` 到 `ContinuousLinearEquiv` 打包。B4 compact-open 层已足。

### 5b.8 canonical Haar OuterRegular + 无假设全 sets 不变（task-109，green）

新文件：
- `Mzk1CanonicalHaarRegularActual.lean`（1,263B；DONE **23:33:34Z（27s）**；olean 29,080B）：`canonical_addHaarMeasure_outerRegular`（`Regular.toOuterRegular`，需 `[LocallyCompactSpace]`）。
- `Mzk1CanonicalHaarInvarianceActual.lean`（2,153B；DONE **23:35:48Z（46s）**；olean 50,480B）：`canonical_map_eq_of_image_eq`。
  - 对 canonical `addHaarMeasure K₀`，`L''coordLattice=coordLattice` ⇒ `(addHaarMeasure K₀).map L = addHaarMeasure K₀`；
  - 不再需要 `[OuterRegular μ]` 假设；像测度外正则由 `Measure.OuterRegular.map L.toHomeomorph` 提供。

**已补**：`Mzk1CanonicalHaarCoordLatticeActual.lean`（3,550B；DONE **23:56:51Z（29s）**；olean 135,136B）——`coordinateCompacts`（carrier=coordLattice，Pi topology）；`coordinateCompacts_mass`（`addHaarMeasure_self=1`）；`canonical_map_eq_of_image_eq_full`（:48，canonical `addHaarMeasure` 无 OuterRegular、无 hOpos/hOfin 假设的 map_eq）。

**剩余**：真实 `glAct` 打包 ContinuousLinearEquiv、对角 measure scaling、一般 SNF det。

### 5b.9 GL_d(Z_p) 打包 + canonical B4 无条件 GL 不变（task-109，green）

新文件：
- `Mzk1GLActContinuousActual.lean`（1,432B；DONE **23:59:59Z（30s）**）：`glContinuousLinearEquiv : GL_d(Z_p) → ((d→Q_p) ≃L[Q_p] (d→Q_p))`，用 `Matrix.GeneralLinearGroup.map (algebraMap Z_p Q_p)` + `toLin` + `toContinuousLinearEquiv`。
- `Mzk1GLActContinuousActionActual.lean`（2,310B；DONE **00:09:13Z（46s）**；olean 71,640B）：
  - `glContinuousLinearEquiv_apply`（:15）rfl；
  - `glContinuous_image_coordLattice`（:20）：V 的打包作用保 `Z_p^d`；
  - **`glContinuous_canonical_haar_invariant`（:31）**：对 canonical `addHaarMeasure coordinateCompacts`，任意 `V ∈ GL_d(Z_p)` 满足 `(addHaarMeasure).map (glContinuousLinearEquiv V) = addHaarMeasure`。

这是 B4 的 **GL_d(Z_p) 无条件不变性**（canonical Haar）；剩对角 scaling 与一般 SNF det。

### 5b.10 canonical 对角 volume ratio（task-109，green 条件 wrapper）

新文件：`tmp/sheaf/xif/paper/Mzk1CanonicalDiagScalingActual.lean`（2,668B；watchdog **DONE 00:18:06Z（55s）**；olean 69,728B）。

- `canonical_diag_volume_ratio`（:16）：把 `Mzk1DiagVolumeProvedActual.diagonal_volume_ratio_actual` 特化到 canonical `addHaarMeasure coordinateCompacts`；
  得 `μ(coordDual f)/μ(coordSmall) = (∏ p^{f_i})⁻¹`。
- 目前 compact/open/正有限测仍为显式条件；无条件化（从 `coordinateCompacts` 的紧开性 + `IsOpenPosMeasure`）是剩余小 GAP。

**SNF**：`Mzk1GeneralSNFVolumeActual` 已有 quotient cardinal，Haar volume bridge 仍 GAP（stage4 协作）。

### 5b.11 coordSmall = coordLattice 桥（task-109，green）

新文件：`tmp/sheaf/xif/paper/Mzk1CoordSmallBridgeActual.lean`（1,660B；watchdog **DONE 00:31:39Z（30s）**；olean 112,376B）。

- `span_one_eq_one`（:13）：`Z_p ∙ 1 = 1`；
- **`coordSmall_eq_coordLattice`（:28）**：`(coordSmall : Set (d→Q_p)) = coordLattice`。

这是对角 scaling 无条件化的桥①；桥②（coordDual = diagEquiv '' coordLattice）与桥③（紧开/正有限）仍 GAP。

**SNF**：stage4 `Mzk1GeneralSNFVolume2Actual` 当前 watchdog FAIL/无 olean，不能 import；`Mzk1CanonicalSNFDetActual.lean` 仅作 GAP 记录，未冒充。

## 5c. task-109 最终 acceptance（2026-11-13）

### Green（watchdog 证据，不手编）
| 文件 | 状态 | 内容 |
|---|---|---|
| `Mzk1MatrixHaarBaseActual.lean` | DONE | 积分矩阵格作用、`glAct_image_eq`、`diagAct` 像 |
| `Mzk1DiagonalIndexActual.lean` | DONE | `Nat.card ((d→Z_p)/∏p^{e_i})=∏p^{e_i}` |
| `Mzk1PermutationHaarActual.lean` | DONE | 坐标置换保 `Z_p^d` 与 product-Haar mass |
| `Mzk1HaarScalarOneActual.lean` | DONE | c=1 条件、image 等号 ⇒ c=1、全 sets（条件 OuterRegular） |
| `Mzk1CanonicalHaarRegularActual.lean` | DONE | canonical `addHaarMeasure` 的 `OuterRegular` |
| `Mzk1CanonicalHaarInvarianceActual.lean` | DONE | canonical 无 OuterRegular 假设的 map_eq（条件 hOpos/hOfin） |
| `Mzk1CanonicalHaarCoordLatticeActual.lean` | DONE | `coordinateCompacts`、mass=1、**canonical full map_eq**（B4 全 sets） |
| `Mzk1GLActContinuousActual.lean` | DONE | `GL_d(Z_p) → ContinuousLinearEquiv` |
| `Mzk1GLActContinuousActionActual.lean` | DONE | action=rfl、image 等号、**GL 无条件 canonical Haar 不变** |
| `Mzk1GLActBundlingActual.lean` | DONE | glLinear 打包 |
| `Mzk1RestrictedDetConditionalActual.lean` | DONE | restricted det 条件乘积 |
| `Mzk1CanonicalDiagScalingActual.lean` | DONE | canonical diag volume ratio（条件紧开/正有限） |
| `Mzk1CoordSmallBridgeActual.lean` | DONE | `coordSmall = coordLattice` |

### 精确 GAP
1. **bridge② `diagEquivCLM`**：`p^{f_i}` 对角 `ContinuousLinearEquiv` 的 `left_inv/right_inv` 结构归约未过；`diagEquivCLM '' coordLattice = coordDual f` 未证。
2. **bridge③**：`coordDual f` 紧开/正有限测未从 `coordinateCompacts` 消去；故 `canonical_diag_volume_ratio_unconditional` 未完成。
3. **一般 SNF det**：stage4 `Mzk1GeneralSNFVolume2Actual` 当前 FAIL/无 olean，不能 import；`Mzk1CanonicalSNFDetActual.lean` 仅为 GAP 记录。
4. B4 的 GL 部分与 canonical full sets 已无条件 green；剩余是 diagonal/SNF 部分。

### 结论
task-109 的 **B4 Haar 不变性主链**（canonical full sets + GL_d(Z_p) 无条件）已完成并 gate green；diagonal 与 SNF 为明确 GAP，未用 axiom/sorry 冒充。

## 6. 其他 GAP / 前提

- `Mzk1PaperFaithfulHullActual`：watchdog FAIL EXIT=1（2026-11-12T20:19:39Z；无 olean）；当前 source 8,188B/4:21:32 local。不能 import；本文件用 `paperFaithfulThetaHullNZ := closure paperRootThetaImageNZ`，并明确不是该文件的定理。
- coefficient data：现有 `qVFamNormalizedPureFractionalScalingData` 的系数是 `rootHalfCoefficient`；`paperRootCoefficientFamily` 的 data 需 `QVFamNormalizedNormCompatibility`/e=1 或单独构造；见 `S3131PaperQFormulaE1Actual.lean:69`、`S826CNormOrderRamificationActual.lean:52`。
- 本节点**不**给目标增益；公共标量族相对 index 不随 m 增长（HANDOFF §5.5/§8.2 P2 停止条件）。

## 7. 指针

- HANDOFF：`D:/iut-audit-20261113/COR312-THREE-ROUTES-HANDOFF-20261113.md` §8.2 P3、§9.3、§9.6。
- 已有：`S793PaperLeastLambdaOHullActual.lean`、`S1004QVFamFiniteLinearizationActual.lean`、`S1008S1004HullFiniteActual.lean`、`S3131PaperQFormulaE1Actual.lean`、`FinitePlaceNormalizedUnitScalingLogVolume.lean`。
- 新：`tmp/sheaf/xif/paper/Mzk1MinimalAcceptanceActual.lean`；task-75 tool inventory：`coord/ROUTE2-TOOL-INVENTORY.md`。
