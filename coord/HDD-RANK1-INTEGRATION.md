# HDD-RANK1-INTEGRATION — rank>1 HDD 资产能否补 Step (xi-d) (A1054)

| field | value |
|---|---|
| Status | PARTIAL (三文件均 olean=True；资产=det⊗M 体积簿记/Haar 缩放，非 determinant 几何比较；需 4 类桥接) |
| 源 | `S1476HDDRankActual`（olean=True）、`S1418HDDConsumerActual`（olean=True）、`S1422HDDDetActual`（olean=True） |

## 1. 关键定义/定理（精确陈述）

### S1476HDDRankActual（rank>1 vector bundle/localization）
```
abbrev S1476GlobalSections (r) := Fin r → O_Q
structure S1476RankArithmeticVectorBundle (r) where
  total : Type; [AddCommGroup]; [Module O_Q]
  localization : ∀ v, total →ₗ[O_Q] (Fin r → O_v)
  rank : finrank O_Q total = r
structure S1476ArithmeticVectorBundleLocalization (r) where
  lattice : ∀ v, Submodule O_v (Fin r → Completion v)
  integral / free / finite / finrank = r / full (span = ⊤)
noncomputable def s1476ActualLocalization (r) : S1476ArithmeticVectorBundleLocalization r
noncomputable def S1476ArithmeticVectorBundleLocalization.toS1215 (D) (I) : S1215HDDLocalLattice I
noncomputable def s1476S1215HDDLocalLattice (I) := (s1476ActualLocalization 2).toS1215 I
theorem s1476S1215HDDLocalLattice_rank_gt_one (I) :
    1 < (s1476S1215HDDLocalLattice I).rank
```
**性质**：rank>1 的算术向量丛与每位的整局部格（free/full/finrank），**无 log-volume/det 比较**。

### S1418HDDConsumerActual（det tensor power）
```
noncomputable def S1418GlobalLattice (D) (o) := D.dependentHull o
theorem s1418GlobalLattice_eq_hull : S1418GlobalLattice D o = LocalFieldProductHull.hull (D.image o)
theorem s1418Image_subset_globalLattice : D.image o ⊆ S1418GlobalLattice D o
theorem s1418GlobalLattice_mono : D ≤ D' → S1418GlobalLattice D ≤ S1418GlobalLattice D'
theorem s1418DetTensorPower_globalLattice :
    D.detData.logVolume (D.detData.detTensorPower (S1418GlobalLattice D o))
      = (D.detData.tensorPowerExponent : ENNReal) * D.detData.logVolume (S1418GlobalLattice D o)
theorem s1418DetTensorPower_image（同上，对 D.image）
theorem s1418DetTensorPower_two：M*M*logVolume
theorem s1418ActualFrozenHullDetSpec : HullDeterminantLogVolumeFrozenSpec
```
**性质**：det⊗M 的 log-volume 缩放律（ENNReal 乘法）与 global hull 单调/包含；**无与 theta/q 缩放元的识别**。

### S1422HDDDetActual（DetTensorPowerLogVolumeBookkeeping）
```
noncomputable def hullLogVolume (μ) : Set ((i) → K i) → ENNReal := fun S => μ (hull S)
theorem hullLogVolume_apply : hullLogVolume μ S = μ (hull S)
theorem hull_smul_unit / smul_region / hull_smul（unit 缩放与 hull 交换）
noncomputable def detDataOfHull (μ) [IsAddHaar μ] [Regular μ] (G : Units) (M) (hM) (hchar :
    distribHaarChar G = M) : DetTensorPowerLogVolumeBookkeeping (Set ((i) → K i)) where
  logVolume := hullLogVolume μ
  tensorPowerExponent := M
  detTensorPower S := G • S
  logVolume_detTensorPower : μ (hull (G • S)) = M * μ (hull S)   -- by hull_smul_unit + hchar
noncomputable def dependentHullLogVolume (s) : dependentRegion s → ENNReal := fun S => dependentHaar s (hull S)
theorem dependentHullLogVolume_dependentHull : ... = dependentHaar s (dependentHull)
noncomputable def dependentDetDataOfChar（需 DependentProductScalingChar）
```
**性质**：det⊗M = “单位 G 的乘法膨胀”，log-volume 乘 M；ENNReal 世界；**无 Real/log 桥**。

## 2. 能否提供 Step (xi-d) 的 determinant 比较？

**不能直接提供**。Step (xi-d) 需要的是：
```
(i) det(localizations) 的 log-volume = rank * (某单位 log)（determinant 的 log-linear 公式）；
(ii) 该 det 单位与 theta 缩放 q^{j^2}（qroot）的**识别**；
(iii) 比较 theta hull 与 q-pilot 区域的 signed log-volume（Real 世界）；
(iv) 由包含/比较得到 -A <= -R。
```
三资产提供：
- S1476：rank、局部格、`toS1215`（rank>1 local lattice）——只覆盖 (i) 的**局部数据结构**；
- S1422：`detDataOfHull` 的缩放律 `μ(hull(G•S)) = M·μ(hull S)`（hchar 条件）——覆盖 (i) 的**体积簿记**；
- S1418：dependent hull 的 global lattice/单调/det⊗M 应用——覆盖 (ii) 的**数据侧引用**，但无 theta/q 元。
缺失：det 单位↔qroot 的识别、ENNReal→Real 的 log 归一化、theta hull 与 q-pilot 区域的对应。

## 3. 接到 `−A ≤ −R` 所需的识别（已有/缺）

| 识别 | 现有 | 状态 |
|---|---|---|
| rank>1 局部格 | `S1476.toS1215`、`s1476S1215HDDLocalLattice_rank_gt_one` | **已有** |
| det⊗M 缩放律 | `S1422.detDataOfHull`（`hchar` 条件）、`S1418DetTensorPower_*` | **已有**（ENNReal） |
| global hull 单调/包含 | `s1418GlobalLattice_mono`、`s1418Image_subset_globalLattice` | **已有** |
| ENNReal→Real log 桥 | `Mzk1SignedLogVolumeLemmasActual.signedLogVolume_ofReal`（部分） | **部分** |
| det 单位 ↔ qroot^{j²} 识别 | 无 | **缺（GAP-DET-QROOT）** |
| theta hull ↔ q-pilot 区域对应 | 无（lana 的 `lgp` 是 sF 平均，非 paper q-pilot） | **缺（GAP-REGION）** |
| signed 比较（Real 世界） | `Mzk1SignedLogVolumeCor312Actual.signed_cor312_inequality`（条件版） | **已有**（需 region 输入） |

## 4. 拼接方案（可先形式化的适配层）

```lean
-- 1. vol 从 HDD hull Haar 取 Real 版
def hullVolReal (μ : Measure Ω) (hfin : ∀ S, μ (hull S) ≠ ⊤) (S : Set Ω) : Real :=
  (μ (hull S)).toReal

-- 2. vol 单调（来自 hull 单调 + measure_mono）
theorem hullVolReal_mono ... : S ⊆ T → hullVolReal μ hfin S ≤ hullVolReal μ hfin T

-- 3. 复用 signed 桥：XiEContainment with vol := hullVolReal
theorem variant_from_HDD (D : XiEContainment Ω (hullVolReal μ hfin)) {A R}
    (hA : signedQ D = -A) (hR : signedTheta D = -R) : -A ≤ -R :=
  variant_of_signedContainment ...
```
（真实文件需把 `μ(hull S)` 的有限性作为显式假设；ENNReal→Real 用 `ENNReal.toReal`。）

## 5. 结论

1. 三资产均 green（olean=True），提供 rank>1 局部格、det⊗M 体积簿记、global hull 单调/包含；
2. **不能直接补 Step (xi-d)**：缺 det 单位↔qroot 识别（GAP-DET-QROOT）、theta hull↔q-pilot 区域对应（GAP-REGION）、ENNReal→Real log 桥（部分有）；
3. 可先写适配层：`hullVolReal`（ENNReal.toReal）+ 单调 + 复用 `XiEContainment`/`signed_cor312_inequality` ⇒ 条件版 `−A ≤ −R`；
4. 这些资产**足以支撑簿记侧**（det⊗M 缩放 M 倍），但几何比较仍需新形式化；建议作为 Step (xi-d) 的**簿记子层**登记，
   不声称已完成 determinant 比较；
5. 下一步（若继续）：GAP-DET-QROOT（det 单位 = q^{j²} 的识别）与 GAP-REGION（hull 对应），二者是真正的几何缺口。