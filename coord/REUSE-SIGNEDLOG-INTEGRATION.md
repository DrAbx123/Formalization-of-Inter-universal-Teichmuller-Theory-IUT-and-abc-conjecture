# REUSE-SIGNEDLOG-INTEGRATION — 复用 SignedLogVolumeCor312 栈 (A1051)

| field | value |
|---|---|
| Status | PARTIAL (复用判定完成；QRegionInclusion 已加 adapter 并标 superseded；未编译) |
| 源 | `tmp/sheaf/xif/paper/Mzk1SignedLogVolumeCor312Actual.lean`（olean=True）、`Mzk1SignedLogVolumeLemmasActual.lean`（olean=True） |

## 1. 精确陈述（逐定理）

### Mzk1SignedLogVolumeCor312Actual（olean True）
```
noncomputable def signedLogVolume (vol : Set α → Real) (S : Set α) : Real := Real.log (vol S)
theorem signedLogVolume_mono {vol} (hmono : ∀ {S T}, S ⊆ T → vol S ≤ vol T)
    {S T} (hST : S ⊆ T) (hpos : 0 < vol S) : signedLogVolume vol S ≤ signedLogVolume vol T
structure XiEContainment (α) (vol : Set α → Real) where
  qRegion hullRegion : Set α
  subset : qRegion ⊆ hullRegion
  q_pos : 0 < vol qRegion
noncomputable def signedQ (D) : Real := signedLogVolume vol D.qRegion
noncomputable def signedTheta (D) : Real := signedLogVolume vol D.hullRegion
theorem xi_f_signed_direction (hmono) (D) : signedQ D ≤ signedTheta D
theorem signed_cor312_inequality (hmono) (D) : signedQ D ≤ signedTheta D
theorem positive_magnitude_direction_obstruction {qVol hVol} (h : qVol ≤ hVol) : -hVol ≤ -qVol
```
### Mzk1SignedLogVolumeLemmasActual（olean True）
```
def signedLogVolume (measure : Set X → ENNReal) (S) : Real := Real.log ((measure S).toReal)
theorem signedLogVolume_nonpos (measure) (S) (hfin : measure S ≠ ⊤) (hle : measure S ≤ 1) :
    signedLogVolume measure S ≤ 0
theorem signedLogVolume_mono (measure) (hmono) {qRegion hull} (hsub : qRegion ⊆ hull)
    (hq_ne_top) (hh_ne_top) (hq_pos : 0 < (measure qRegion).toReal) :
    signedLogVolume measure qRegion ≤ signedLogVolume measure hull
theorem signedLogVolume_ofReal (S) {r} (hr : 0 ≤ r) :
    signedLogVolume (fun _ => ENNReal.ofReal r) S = Real.log r
```

## 2. `signed_cor312_inequality` 是否已是我们要的 Cor 3.12 条件版？

**是（条件版/算术桥）**，但需正确实例化 vol：
- 令 `vol qRegion := exp(-A)`（A=|log q|）、`vol hullRegion := exp(-R)`（R=|log Θ|）；
- 则 `signedQ = log vol qRegion = -A`、`signedTheta = log vol hullRegion = -R`；
- `signed_cor312_inequality hmono D : signedQ ≤ signedTheta` 即 **`-A ≤ -R`（variant 形式）**；
- 依赖（均为显式假设）：`hmono`（vol 对包含单调）、`D.subset : qRegion ⊆ hullRegion`、`D.q_pos`；
- 缺的仍只是**几何输入**：`qRegion ⊆ hullRegion` 与 `vol = exp(-·)` 的实际构造（paper Step (xi-d)）；
  `signed_cor312_inequality` 本身不做几何。

## 3. 与 QRegionInclusion 的对接（复用、去重）

我们新文件 `Mzk1QRegionInclusionActual` 的 `RegionLogVol`/`haarLogVolume_mono_of_subset`
与 `signedLogVolume`/`signedLogVolume_mono` **重复**；处理：
- **保留** `Mzk1QRegionInclusionActual` 文件（不删），header 标 `SUPERSEDED-PARTIAL`：
  抽象 `RegionLogVol` 被 `Mzk1SignedLogVolumeCor312Actual` 取代；
- 新增 **adapter**（同文件内），直接 import 并复用：
```
structure SignedQRegionData (α) (vol : Set α → Real) where
  hmono : ∀ {S T}, S ⊆ T → vol S ≤ vol T
  qRegion hullRegion : Set α
  subset : qRegion ⊆ hullRegion
  q_pos : 0 < vol qRegion
noncomputable def signedCor312Data (D) : XiEContainment α vol := { ... }
theorem cor312_signed_conditional (D) : signedQ ... ≤ signedTheta ...
theorem variant_signed_conditional (D) (hA : signedQ = -A) (hR : signedTheta = -R) : -A ≤ -R
```
- 旧的 `cor312_rankone_conditional`（logVol 版）保留但标 superseded；
- **方向措辞（A1052）**：`θ⊆q` 只是 variant 的**充分条件**（单向 `θ⊆q ⇒ μθ≤μq`）；`⇔` 不成立（反向需 null-set/可测性论证，未声称）。两种约定的 set 命名不同，勿混。
- 两条路线在 exp 映射下对应：旧 = `logVol=-log μ` + θ⊆q；新 = `signedLogVolume=log vol` + q⊆hull，
  vol=exp(-·) 时一致。

## 4. 结论

1. `signed_cor312_inequality` 已是**条件版 Cor 3.12 的算术桥**（复用价值高，olean green）；
2. 需要实例化 `vol=exp(-A/-R)` + `qRegion⊆hullRegion`（几何 GAP，Step (xi-d)）；
3. 新文件无需再定义 monotonicity/log-volume；`Mzk1QRegionInclusionActual` 的抽象部分标 superseded，
   通过 adapter 复用 signed 栈；
4. `Mzk1SignedLogVolumeLemmasActual` 的 ENNReal 版可用于 `XiEContainment` 的 `vol : Set → Real`
   若需要从 measure 提升（`signedLogVolume_ofReal`）。
## 5. A1053 语义钉死（与 hull 对齐）

`Mzk1SignedLogVolumeCor312Actual` 的字面语义：
- `signedLogVolume vol S = Real.log (vol S)`（**log μ**，不是 −log μ）；
- `XiEContainment{subset : qRegion ⊆ hullRegion, q_pos}`；
- `signed_cor312_inequality : signedQ ≤ signedTheta`，即 `log vol qRegion ≤ log vol hullRegion`。

**Paper-faithful 实例化**（vol = 实际 Haar 体积，q-pilot 区域体积 < 1）：
- 取 `signedQ = -A`、`signedTheta = -R`（即 A = −log vol(qRegion)，R = −log vol(hullRegion)）；
- 包含方向 = **`qRegion ⊆ hullRegion`（q-pilot 区域 ⊆ Θ-hull 区域）**；
- 结论 `signedQ ≤ signedTheta` 即 `-A ≤ -R` **就是 variant** ✓；
- 这解释了 hull 的观察：subset 字面是 q⊆hull，与 `theta⊆q` 相反——**因为体积归一化不同**：
  我们的抽象文件固定 `logVol := -log μ` 且 `logVol q = -A`，即 `μq = e^{A}`（倒数/大体积归一化），
  故其正确包含是 θ⊆q；paper-faithful Haar 体积是 `μq = e^{-A} < 1`，此时正确包含是 q⊆hull。
- **两者不可混用**；paper-faithful 拼接应走 signed stack + q⊆hull + A=−signedQ/R=−signedTheta。

## 6. 结论（A1053）

1. signed stack 可直接实例化为 variant：subset = q⊆hull，A=−signedQ，R=−signedTheta；
2. 我们 QRegion 抽象文件的 θ⊆q 只是**倒数归一化**下的等价表述，标 SUPERSEDED-PARTIAL（paper 集成用 signed 栈）；
3. adapter `variant_of_signedContainment` 已加（复用 `cor312_signed_conditional`）；
4. 仍需几何输入：q-pilot 区域 ⊆ Θ-hull 的**构造**（Step (xi-d)），与归一化选择无关。