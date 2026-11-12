# MODEL-FIX — FinalL 载体问题与两个模型修正方案 (A1127)

| field | value |
|---|---|
| Status | ANALYSIS + MIGRATION PLAN (no Lean, no compile) |
| 确认 | **FinalL = AlgebraicClosure**（`RootExtension := AlgebraicClosure (CommonPrimeCompletion ...)`），`FinalLValuedCarrier = TensorProduct ℚ_p qVFamTensorBlock FinalL` —— **非有限维、无 canonical Haar**；S971/S979/S981 的 `D.measure` 是**额外假设的测度**（无构造），链是条件性的。 |
| 方案 | **(A) 在 `qVFamTensorBlock`（有限维 ℚ_p）上做全部体积，L 只作标量扩张** —— **已有部分实现**（S1004/S996/S976/S995）；**(B) 换成有限扩张 E/ℚ_p** —— 需新建域与所有根/Ind 数据，成本高。 |
| 建议 | 采用 **(A)**；S971/S979/S981 保留为 L-载体 audit，不用于测度论 log-volume；迁移清单见 §4。 |

## 1. 确认：FinalL 是代数闭包（非有限维）

```lean
-- PaperC3ThetaRootActual.lean:34-36
-- The algebraic-closure Kummer extension at each source place.
abbrev RootExtension (v : V) : Type u := AlgebraicClosure (CommonPrimeCompletion (G.place v))

-- PaperFinalLValuedTensorCarrierActual.lean:42-46
abbrev FinalL (T) (b) : Type := RootExtension (G := finalLGeometry T b) PUnit.unit
abbrev FinalLValuedCarrier (T) (b) : Type :=
  TensorProduct ℚ_[qVFamTensorP T b] (qVFamTensorBlock T b) (FinalL T b)

-- 48-50: qVFamToLValued x := tmul x 1
```
后果：
```
✗ `FinalLValuedCarrier` 是 ℚ_p-向量空间但不是有限维（AlgebraicClosure 无限维）；
✗ 没有 canonical 的局部紧拓扑/Haar（`AlgebraicClosure` 无局部紧结构；S956 的
  `FinalLTensorLogVolumeData` 只能**假设**一个 Measure + 拓扑 + 局部紧实例）；
✗ 因此 S971/S979/S981 的 `D.measure` 无构造，`FinalLTensorLogVolumeRequired` 无 inhabitant；
✗ 它们的 log-volume 不是 paper 的 canonical Haar log-volume。
```

## 2. 方案 (A)：在 `qVFamTensorBlock`（有限维 ℚ_p）上做体积 —— 已部分实现

`S1004QVFamFiniteLinearizationActual`（green）正是方案 A：
```lean
-- S1004:6-11 文件头：full FinalL-valued carrier is not finite-dimensional ⇒ rebuild on qVFamTensorBlock
noncomputable def s1004E : qVFamTensorBlock T b ≃ₗ[ℚ_[qVFamTensorP T b]] (Fin d → ℚ_p)   -- S996 linearization
noncomputable def s1004QPilotImage : Set (FiniteLogShellCarrier p d) := s1004E '' qPilotPaperRegion
noncomputable def s1004Hull : Set (FiniteLogShellCarrier p d) := s1004E '' paperRootThetaImageNZ
theorem s1004Containment : s1004QPilotImage ⊆ s1004Hull := Set.image_mono qPilotPaperRegion_subset_thetaImageNZ
noncomputable def s1004H := finiteLogShellHaarData (p) (d)        -- S976: finite-dim canonical Haar
theorem finiteNormalizedLog_mono_qvfam (hSU) (hpos) (hfin) :
  log (measure S).toReal ≤ log (measure U).toReal
theorem s1004PerB (hpos) (hfin) :
  log (measure s1004QPilotImage).toReal ≤ log (measure s1004Hull).toReal
```
⇒ **有限维载体、canonical Haar、containment、per-b log 不等式均已存在（green）**。
全局加权版本在 `S995FiniteCarrierCor312ConclusionActual`（S1004 imports it）。

## 3. 方案 (B)：有限扩张 E/ℚ_p 替代 AlgebraicClosure

```
把 RootExtension 换成有限扩张 E ⊇ ℚ_p（含所需的 2ℓ-th 根、Ind 作用的根），
则 E 有限维 ⇒ canonical Haar、局部紧、可做体积；
但需要：
(B1) 构造 E 并证明全部 qroot/theta roots 在 E 中（Kummer 扩张的显式次数界）；
(B2) Ind1/2/3 作用在 E-向量空间上可定义（可能依赖 E 的选择）；
(B3) 重新验证所有 log-volume 归一化（E 的 Haar 归一化）。
⇒ 数学上可行但成本高；且 paper 的 Ind 作用本来在代数闭包上，有限 E 可能不足。
```
建议：**用 (A)**，L 只作标量扩张（若需要 L-valued 标量，用 `⊗ L` 但不取测度）。

## 4. S971/S979/S981 迁到方案 (A) 的改动清单

| 现定义（L-carrier） | 方案 A 替换 | 备注 |
|---|---|---|
| `FinalLValuedCarrier T b` | `qVFamTensorBlock T b`（或其有限模型 `FiniteLogShellCarrier p d`） | S1004 `s1004E` |
| `qVFamToLValued` | `s1004E`（线性化）或 `id`/`FiniteLogShellCarrier` 嵌入 | 不再需要 tensor with L |
| `tensorThetaRegionImage` | `s1004E '' paperRootThetaImageNZ` | S1004 `s1004Hull` |
| `tensorThetaRegionIndUnion` | **删除**（Ind 点像在 A 中由 paper region image 已覆盖）或有限 Ind 像 | 需确认 Ind 作用在 A 中可忽略/由 paper region 包含 |
| `tensorRegionHull := closure (...)` | `s1004Hull`（不取闭包）或有限维闭包 | 有限维 ℚ_p 中闭包 = 闭集；S1004 不需要 |
| `tensorNormalizedLogVolume` | `Real.log ((s1004H).measure S).toReal`（unitRegion 归一化在 A 中可省，差常数） | S962 的 unitRegion 归一化取消 |
| `qPilotTensorLog` | `Real.log ((s1004H).measure s1004QPilotImage).toReal` | S1004 `s1004PerB` |
| `tensorRegionHullLog` | `Real.log ((s1004H).measure s1004Hull).toReal` | S1004 `s1004PerB` |
| `FinalLTensorLogVolumeData` | `FiniteLogShellHaarData`（S976）/ S1004 的 `s1004H` | 不再假设测度 |
| S979 `qPilotTensorLog_le_tensorRegionHullLog` | `s1004PerB`（已证） | 直接替换 |
| S981 `tensorRegionHull_measure_lt_top_of_subset` | 有限维 Haar 的 `measure_lt_top`（S976 提供） | 更简单 |

**需要改的引理**：
```
- 所有用到 `D.measure` 的地方 → `(s1004H).measure`；
- 所有 `qVFamToLValued` 的 image 等式 → `s1004E` 的 image；
- closure/hull 的包含引理（S971:61）→ `s1004Containment`（image_mono）；
- 全局加权：用 S995 的有限载体结论，替换 S919 的 global weighted inequality（若其依赖 L 载体）。
```

## 5. 对我们的 target 的影响

```
(A) 下：
  A = paperQAbsLog l logQ（不变，标量）；
  R = -log ((s1004H).measure s1004Hull).toReal  （有限维 canonical Haar，无 L 载体）；
  containment 链 s1004QPilotImage ⊆ s1004Hull 已 green；
  per-b 不等式 s1004PerB 已 green；
  仍需 GAP-NORM2：A = paperQAbsLog vs 有限 Haar 归一化（q 侧 measure 与 logQ/(2l) 的识别）。
(B) 下需要全部重建。
```

## 6. Lean 签名草案（方案 A 的 target 形态）

```lean
-- 以 S1004 数据为参数（T, b, s1004H 等已定义）
def AFam (T b) : Real := paperQAbsLog l (logQ)                 -- 仍是标量
def RFam (T b) : Real :=
  - Real.log ((s1004H (l := l) T b).measure (s1004Hull (l := l) T b)).toReal

theorem RFam_le_AFam_of_norm (hpos : 0 < (s1004H T b).measure (s1004QPilotImage T b))
    (hfin : (s1004H T b).measure (s1004Hull T b) < ⊤)
    (hA : AFam T b = - Real.log ((s1004H T b).measure (s1004QPilotImage T b)).toReal) :
    RFam T b ≤ AFam T b := by
  -- s1004PerB + hA
  sorry -- 目标陈述草案（待实现；s1004PerB 提供 log μq ≤ log μhull）
```

## 7. 结论

1. **FinalL = AlgebraicClosure 确认**：非有限维、无 canonical Haar；S971/S979/S981 的条件测度链不是 paper 的 log-volume；
2. **方案 (A) 已在 S1004 部分实现**：有限维 `qVFamTensorBlock`/`FiniteLogShellCarrier`、`finiteLogShellHaarData`、`s1004Containment`、`s1004PerB`（green）；
3. **方案 (B)**（有限扩张 E/ℚ_p）数学可行但成本高、且可能不足 paper 的 Ind 作用；
4. **迁移清单**见 §4：核心是把 FinalLValuedCarrier 换成 qVFamTensorBlock/有限模型，删 Ind union/closure，用 S1004/S976 的 measure 与引理；
5. 对我们的 target：R 改为有限维 Haar 的 log，containment/per-b 已 green；**唯一剩余 GAP-NORM2**（A 与有限 Haar 归一化的识别）；
6. 建议后续：在 S1004 基础上写 A 版本的 `A/R` 装配，不再使用 FinalL 载体测度。