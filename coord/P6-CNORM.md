# P6-CNORM — C-Norm (C13)-(C16) 盘点、工具与缺口（R29h / task-88）

| field | value |
|---|---|
| Status | **task-88 completed**：**(C15)(C16)(C13 尽力) 已 green**（watchdog DONE EXIT=0，2026-11-12T20:24:28Z，37s；olean 140480 B）；global product formula / restriction of scalars 记为 GAP；与 (C17)-(C20) 接口见 §4 |
| 编译 | **watchdog DONE EXIT=0**：`dag/watchdog/watchdog.log` L204037 `2026-11-12T20:24:28.161Z DONE EXIT=0 ... (37s)`；olean `tmp/sheaf/xif/paper/Mzk1NormDeterminantToolsActual.olean` 140480 B；按统一约定本人不自行编译 |
| 纪律 | 无 sorry/axiom、无 PUnit/True carrier；不新增假设换 green |

## 1. Mathlib 已有覆盖（file:line）

| 内容 | 位置 | 说明 |
|---|---|---|
| `Algebra.norm` 定义（det of left multiplication） | `Mathlib/RingTheory/Norm/Defs.lean:59-62`（`noncomputable def norm : S →* R := LinearMap.det.comp (lmul R S).toRingHom.toMonoidHom`） | (C15) 的定义源 |
| `Algebra.norm_apply` | `Norm/Defs.lean:64`：`Algebra.norm R x = LinearMap.det (lmul R S x)` | **(C15) 精确形式**，rfl |
| `Algebra.norm_eq_matrix_det` | `Norm/Defs.lean:82-84`：`norm R s = Matrix.det (Algebra.leftMulMatrix b s)` | (C15) 矩阵形式（选基） |
| `Algebra.norm_algebraMap_of_basis` | `Norm/Defs.lean:87-91`：`norm R (algebraMap R S x) = x ^ Fintype.card ι` | 基版本 |
| `Algebra.norm_algebraMap` | `Norm/Defs.lean:99-101`：`norm R (algebraMap R S x) = x ^ finrank R S` | **(C16) 核心**（norm of scalars） |
| `Algebra.norm_natCast` | `Norm/Defs.lean:104-105` | norm of Nat |
| norm 的乘法性/幂性 | `Algebra.norm : S →* R`（MonoidHom） | `map_mul`/`map_pow` ⇒ **范数函子性**（乘性部分） |
| 使用例 | `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean:399`（`simp_rw [Algebra.norm_eq_matrix_det ...]`） | 印证 API |
| norm 在数域整数环上的版本 | `Mathlib/NumberTheory/NumberField/Norm.lean:68 norm_algebraMap` | 数域/整环版本（非本任务主接口） |
| 相对范数/传递性 | `Mathlib/RingTheory/Norm/Transitivity.lean:220/247` | 相对扩张/传递性（部分） |
| **(C13) Galois 乘积** | `Mathlib/RingTheory/Norm/Transitivity.lean:272-273`：`theorem norm_eq_prod_automorphisms [IsGalois K L] (x) : algebraMap K L (norm K x) = ∏ σ : Gal(L/K), σ x` | **(C13) 定义/乘积形式直接复用** |

## 2. 仓库已有覆盖（file:line）

| 内容 | 位置 |
|---|---|
| `norm_algebraMap_pow_of_finrank_eq_relativeCompletionDegree` | `LeanFormal/IUT/ABCBridge/Geometry/RelativeCompletionFinrankReduction.lean:293` |
| `normalizedNorm_algebraMap` | `LeanFormal/IUT/Foundations/AlgebraicGeometry/BaseNormCompatibilityProof.lean:134` |
| `norm_algebraMap'`（p-adic）使用 | `LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceCompactHullScaling.lean:114`、`FinitePlaceStepVAssembly.lean:44` |
| `norm_completionMap_pow` / `norm_algebraMap_pow` | `LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceCompletionNormTransport.lean:27` |
| det × log-volume 簿记（packet/Wedgedet） | `LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/HullDeterminantLogVolumeReduction.lean:123/153/173/220/249/302` | `HullDeterminantLogVolumeFrozenSpec`、`matrixLogDet`、`packetLogVolume_eq_matrixLogDet`、`packetLogVolume_tensorPower` |
| WeightedNormalization（模块） | `LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/WeightedNormalization.lean`（Project.lean:335 import） | 未逐条盘点（本任务只读内容搜索） |
| `HaarLogVolume`/gobal det 归一化 | `LeanFormal/IUT/Foundations/Volumes/HaarLogVolume.lean:51-71` | log-volume 工具 |

## 3. 本任务 Lean 文件（`tmp/sheaf/xif/paper/Mzk1NormDeterminantToolsActual.lean`，watchdog 编译）

```lean
-- (C13) Galois 乘积（re-export Mathlib Transitivity:272）
theorem norm_galois_product [IsGalois K L] (α : L) :
    algebraMap K L (Algebra.norm K α) = ∏ σ : Gal(L/K), σ α

theorem norm_mul (α β : L) : Algebra.norm K (α * β) = Algebra.norm K α * Algebra.norm K β
theorem norm_pow (α : L) (n : ℕ) : Algebra.norm K (α ^ n) = (Algebra.norm K α) ^ n

-- (C15) linear form：det of lmul = norm（re-export Mathlib norm_apply）
theorem norm_eq_det_lmul (α : L) :
    Algebra.norm K α = LinearMap.det (Algebra.lmul K L α)

-- (C15) matrix form（re-export Mathlib norm_eq_matrix_det）
theorem norm_eq_matrix_det (b : Basis ι K L) (α : L) :
    Algebra.norm K α = (Algebra.leftMulMatrix b α).det

-- (C16)：α^r = algebraMap K L q，r>0，q≠0 ⇒ r·log||N α|| = [L:K]·log||q||
theorem norm_pow_log_relation
    [NormedField K] [Field L] [Algebra K L] [Module.Free K L] [Module.Finite K L]
    (r : ℕ) (hr : 0 < r) (α : L) (q : K)
    (hα : α ^ r = algebraMap K L q) (hq : q ≠ 0) :
    (r : ℝ) * Real.log ‖Algebra.norm K α‖ =
      (Module.finrank K L : ℝ) * Real.log ‖q‖
```
证明思路：`congrArg (Algebra.norm K) hα` ⇒ `(N α)^r = q^finrank`（用 `Algebra.norm_algebraMap` 与 `map_pow`）；取 `‖·‖` 用 `norm_pow`；取 `Real.log` 用 `Real.log_pow`。

## 4. 与 (C17)-(C20) 的接口：可复用 vs 需新对象

| 接口 | 内容 | 可复用（file:line） | 需要的新对象/缺口 | 状态 |
|---|---|---|---|---|
| **(C17)** `det_K(m_α)` 的算术解释 | 范数 = 乘法的行列式 | `Mzk1NormDeterminantToolsActual.norm_eq_det_lmul`（Lean，green）；Mathlib `Norm/Defs.lean:64` | **无**（det 定义即 norm） | **green** |
| **(C18)** 范数函子性 | 乘法/幂、相对范数、restriction of scalars | `norm_mul`、`norm_pow`（本文件 green，来自 `Algebra.norm` 的 MonoidHom 结构）；Mathlib `Norm/Transitivity.lean:202 Algebra.norm_norm`（相对范数传递性，一般环） | 本项目 **relative completion / restriction of scalars 的实例化**（把 `norm_norm` 对齐到 `InitialThetaData`/`SourcePilotRegionData` 的实际扩张）；无现成对象 | **部分 green**（乘性/幂 + 一般传递性）；实例化 = GAP-NORM-TRANS |
| **(C19)** `α^r=q` 的 log 线性化 | `r·log|N(α)|_K = [L:K]·log|q|_K` | `norm_pow_log_relation`（本文件 green，真证；用 `norm_algebraMap`/`map_pow`/`norm_pow`/`Real.log_pow`） | **无**（抽象层）；若要把 `‖·‖_K` 换成 paper 的 normalized absolute value，需 arch/normalization 对象（与 §5 product formula 同源） | **green**（抽象）；paper 归一化 = GAP-NORM-ARCH |
| **(C20)** 全局 product formula / Arakelov degree | `∏_v |·|_v = 1`，度=log-volume 归一 | 局部工具：`HullDeterminantLogVolumeReduction.lean:123/173/220/249/302`（det × log-volume 簿记）；`HaarLogVolume.lean:51-71`（log-volume）；`CardHullRealHaarDilationDocking.lean`（Haar 伸缩） | **新对象**：全局位集/乘积公式（含 arch 归一化）、Arakelov degree 与 determinant metric 的接口；paper 的 `|·|_v` 归一化（`(1/(2ℓ))` 等） | **GAP-PRODUCT-FORMULA**（最大缺口） |
| **(C13)** Galois 范数 | `algebraMap(N α)=∏_{σ∈Gal} σ α` | `norm_galois_product`（本文件 green，re-export Mathlib `Norm/Transitivity.lean:272`）；`norm_mul`/`norm_pow` | Galois 作用下不变性 `N(σ α)=N(α)` 的显式证明（可由乘积重排得到，未写）；与 (C18) 相对范数在 Galois 情形的接口 | **基本 green**；不变性 = GAP-C13-INV |

结论：
1. **(C17)、(C19) 可直接复用本 green 文件**；
2. **(C18) 复用 `Algebra.norm` 的 MonoidHom 性与 Mathlib `norm_norm`**，但需把一般定理实例化到项目的 relative completion（新对象：项目扩张/完成映射的 norm 兼容引理）；
3. **(C20) 是唯一需要真正新对象的大缺口**：product formula + Arakelov degree 接口；局部簿记（HullDeterminantLogVolume/HaarLogVolume）已存在但未接 product formula；
4. **(C13) 乘积形式已 green**，Galois 不变性留一个小引理（GAP-C13-INV）。
## 5. 缺口（file:line）

```
GAP-C13（已基本闭合）：Galois 乘积形式由 Mathlib `norm_eq_prod_automorphisms` 提供，本文件 re-export；
         仍缺：Galois 作用下的不变性 `N(σ α)=N(α)` 的显式证明（可由乘积形式+重排得到，未写）。
GAP-NORM-TRANS：相对范数传递性/restriction of scalars 的完整函子性：
         Mathlib/RingTheory/Norm/Transitivity.lean 有部分（Transitivity:220/247），未覆盖本项目 relative completion 情形。
GAP-PRODUCT-FORMULA：全局 product formula（含 arch 归一化）未形式化；
         与 Arakelov degree / determinant metric 的接口在 HullDeterminantLogVolumeReduction（簿记）+ HaarLogVolume（工具），
         但 product formula 本身缺。
GAP-C17-C20：C17/C19 已接；C18 仅乘性部分；C20 缺。
```

## 6. 结论

1. (C15) 完全由 Mathlib `Algebra.norm_apply`/`norm_eq_matrix_det` 覆盖，本文件 re-export；
2. (C16) 本文件给出真证 `norm_pow_log_relation`（依赖 `norm_algebraMap`/`map_pow`/`norm_pow`/`Real.log_pow`）；
3. (C13)、相对范数传递性、全局 product formula 记为 GAP；与 (C17)-(C20) 的接口见 §4；
4. 按统一约定：不自行编译；`Mzk1NormDeterminantToolsActual.lean` 已在 watchdog 启动列表，DONE/FAIL 以 watchdog.log 为准；
5. 若 watchdog FAIL，请回传 per-file log 首错，我只改文件、不再自行 lake/lean。
## 7. 下一步（等 Lead 定 P5/P6）

1. 若 P6 继续：优先 (C20) 的 **product formula 对象**（全局位集、归一化 arch 因子）——它同时解锁 (C19) 的 paper 归一化版本与 §4 的 GAP-NORM-ARCH；
2. (C18) 实例化：在 `RelativeCompletionFinrankReduction.lean:293` 与 `FinitePlaceCompletionNormTransport.lean:27` 之间建立 relative norm 的 `norm_norm` 实例（新对象=项目扩张/完成映射的 `IsScalarTower` 链）；
3. (C13) 不变性：`Gal` 作用重排 `∏ σ` 的小引理，可放进本文件或后续 C-Norm 扩展。