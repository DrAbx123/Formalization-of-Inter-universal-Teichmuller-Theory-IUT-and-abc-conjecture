# NORMALIZATION AUDIT A495 — q/Θ readouts vs LANA quantities (mainline section)

只展开定义、不改定义。来源均为树内 Lean 源码（行号为当前文件）。

## ① `qThetaHullReadout`（mainline）

`tmp/sheaf/xif/paper/Mzk1QPilotR4Stage5AlignActual.lean:91`：
```lean
def qThetaHullReadout (b : Bad (nativePlaceSelection T)) : Real :=
  qPilotLogImage T b
```
`tmp/sheaf/xif/paper/Mzk1QPilotSHEDoubleImageActual.lean`（qPilotLogImage）：
```lean
noncomputable def qPilotLogImage (b : Bad (nativePlaceSelection T)) : Real :=
  localSignedLog (qVFamily T b)
```
`LeanFormal/IUT/IUTIII/Corollary312/ArithmeticQPilotLogVolume.lean:35` 与 `:25`：
```lean
noncomputable def localSignedLog (parameter : FinitePlaceQCandidate place) : Real :=
  Real.log ‖parameter.q‖
-- qNorm_pos : 0 < ‖q‖; qNorm_lt_one : ‖q‖ < 1 ⇒ localSignedLog < 0
```
**结论 ①**：`qThetaHullReadout T b = Real.log ‖(qVFamily T b).q‖ ∈ (-∞,0)`，是**单个 bad place b 的局部有符号 log**（不是全局和，无 1/(2ℓ) 因子）。

## ② `qThetaDetReadout`（mainline）

`Mzk1QPilotR4Stage5AlignActual.lean:95-96`：
```lean
def qThetaDetReadout (b) : Real := thetaPilotLogImage T b
def thetaPilotLogImage (b) : Real := qPilotLogImage T b / (2 * (l.value : Real))
```
**结论 ②**：`qThetaDetReadout = qThetaHullReadout / (2·l.value)`（正因子 `2·l.value = 2ℓ`，ℓ 为素数 l）。因 hull 读数为负，`hullReadout ≤ detReadout` 由`2ℓ>1`**自动成立**：
`hull = -A (A>0) ⇒ det = -A/(2ℓ) ≥ -A = hull`。
（文件 `Mzk1QPilotR4Stage5AlignActual.lean:70-101` 的 `qPilotLogImage_lt_thetaPilotLogImage` / `qThetaReadout_ordered` 正是这个方向。）

## ③ `qPilotLogImage` / `thetaPilotLogImage` 定义式

见 ①、②。等价地 `qPilotLogImage_exp : Real.exp (qPilotLogImage T b) = ‖(qVFamily T b).q‖`（SHE double image 文件）。
根关系（SHE 箭头）：`completionToRootExtension T qPilot b = (thetaPilotImage b)^(2·l.value)`，`Mzk1QPilotSHEDoubleImageActual.she_arrow_apply`。

## ④ LANA `(concreteVariantData D).qPilot` 字段（`tmp/sheaf/lana/iut/Iut/Cor312/LeftHandSide.lean`）

```lean
structure QPilotData (D : InitialThetaData.{u}) : Type u where
  badFinset : Finset (FinitePlace D.F)
  badFinset_spec : ↑badFinset = badPlacesOver D.F D.E D.VBad
  weight : FinitePlace D.F → ℝ          -- 期望 f_w/[F:ℚ]
  weight_pos : ∀ w ∈ badFinset, 0 < weight w

noncomputable def logQ : ℝ :=
  ∑ w ∈ Q.badFinset.attach,
    Q.weight w.1 * (D.qOrder w.1 (Q.mem_bad w.2) : ℝ) * Real.log (residueChar w.1)   -- :81

noncomputable def absLogQ : ℝ := Q.logQ / (2 * (D.ℓ : ℝ))                            -- :88
noncomputable def lhs : ℝ := -Q.absLogQ                                             -- :93
```
**结论 ④**：LANA `absLogQ` = **(全局加权和)/(2ℓ)**；`lhs = -absLogQ`。`weight` 是 bad place 的归一化算术度权；无 `inertDeg` 字段（该量以 `weight = f_w/[F:ℚ]` 的注释形式出现）。

## ⑤ LANA `rhsData.rhs`（`Iut/Cor312/RightHandSide.lean:96-107` + `Iut/Concrete/ThetaRegion.lean`）

```lean
noncomputable def thetaHull : ∀ i, R.container.AdmissibleRegion i := R.hull.hullFamily R.thetaPilot   -- :99
noncomputable def rhs : ℝ := R.vol.processionVol R.thetaHull                                        -- :107
```
`concreteVariantData D` 的实例（`ThetaRegion.lean:320-331`）：`thetaPilot := D.thetaPilotOn nC (ivLabels) …`；
`thetaPilotOn`（`ThetaRegion.lean:273-277`）capsule i 的 packet region = `productRegion (fun c => thetaComponentOn n i (S i) vQ c)`；
`thetaComponentOn` finite（`:170-175`）：
```lean
⋃ φ ∈ indAut, φ '' (⋃ l ∈ S, D.scaleEltAt n i p c l • shell)
```
`scaleEltAt`（`:126-132`）指数 = `(i.1 + 1) ^ 2`（即 capsule j=i+1 的 theta 值 `q_{v_l}^{j²}`）。
`processionVol` = 对 capsules 的 globalVol 平均（`LogVolumeData.processionVol`），`globalVol` = packetVol 的有限和。
**结论 ⑤**：`rhs = processionVol(hull θPilot)`；`sFactor(nC)` **不是** `rhs` 的定义字段，而是通过 LGP 律 `logVol(lgp S) = logVol(lgp O) + logVol S`、`logVol(lgp O) = -sFactor(nC)·absLogQ`（`IdentifiedCopies.lean:281,444`）与 `Wall.gap` 进入的。

## ⑥ `Wall.gap` / `Wall.sFactor`

`tmp/sheaf/lana/iut/Iut/WallEquiv/Gap.lean:505`：
```lean
def gap : ℝ := (concreteVariantData D).rhsData.rhs - logVol D (lgp D (hullOf D (vcI D)))
```
`Iut/Wall/Pilots.lean:55`：
```lean
noncomputable def sFactor (n : ℕ) : ℝ := (∑ j ∈ Finset.range n, ((j : ℝ) + 1) ^ 2) / n
```
`MultiContainer.lean:88`：
```lean
def SSIneq (D) : Prop := (sFactor (nC D) - 1) * D.qPilot.absLogQ ≤ logVol D (hullOf D (vcI D))
```
`Gap.lean`：`ss_iff_le_rhs_sub_gap : SSIneq ↔ -absLogQ ≤ rhs - gap`；`gap_nonneg`；`variant_of_ss_gap : SSIneq → Corollary312Variant`（反向不证）。

## 判定：`lhs ≤ rhs` 与 `hullReadout ≤ detReadout` 差什么？

设 `A := absLogQ > 0`（`absLogQ = logQ/(2ℓ)`，logQ 为 ④ 的全局加权和）。
* LANA Var：`lhs ≤ rhs` ⇔ `-A ≤ rhs`（rhs 见 ⑤，为**全局 procession 平均量**）。
* mainline 比较：`hullReadout = log‖q_V(b)‖ = -A_b`（**单个 place b 的局部量**），`detReadout = hullReadout/(2ℓ)`，故 `hullReadout ≤ detReadout` ⇔ `-A_b ≤ -A_b/(2ℓ)` ⇔ `A_b ≥ A_b/(2ℓ)`，对 `A_b>0` **恒真**（不含量值信息）。
* 二者之间差三重因子/结构：
  1. **局部 vs 全局**：`-A_b`（一个 bad place）vs `-A`（④ 的 weighted sum over bad places）；
  2. **2ℓ 归一化**：LANA 的 `A = logQ/(2ℓ)` 已经含 1/(2ℓ)；mainline det 再除一次 `2ℓ`：`det = (-A_b)/(2ℓ)`，即多一个 `1/(2ℓ)`；
  3. **sFactor**：⑤ 的 rhs 是 θ-pilot 的 procession 平均（j² 权重由 `scaleEltAt` 指数给出），与 LGP 律中的 `-sFactor(nC)·absLogQ` 相关；要把 `det` 对齐 `rhs` 需 `(-A_b)/(2ℓ) = rhs`，结合 LGP 律即需 `A_b/(2ℓ) = sFactor(nC)·A` 之类的归一化恒等式，一般情况下不成立（`sFactor(nC) ≥ 1`，`A_b` 只是 A 的单点分量）。
* **符号**：两边同为负、无符号翻转问题；差异是**归一化与局部/全局**，不是符号。

**结论（模型不匹配点，禁止当 rfl）**：
- `qThetaReadout_ordered` 是根关系 `θ^{2ℓ}=q` 的**平凡重标度**结论（`det = hull/(2ℓ)`, `2ℓ>1`），**不是 Var**；
- ① 的“定义级等式”跨两个模型（native `SourceNativeInitialThetaData` vs LANA `InitialThetaData`），非 defeq；
- ② 的对齐在 ① 下等价于 `rhs = lhs/(2ℓ)`（`Step3115AlignmentProofActual.det_alignment_iff_of_hull_alignment`），与 LANA 的 `sFactor` 归一化冲突（`sFactor(nC) ≠ 1/(2ℓ)`，nC≥1 时 s>1 而 1/(2ℓ)<1），故**不能**用当前 native 读法直接桥到 Var；正确做法是改用 LANA 规范化读法（`absLogQ = logQ/(2ℓ)`、θ-pilot 的 `j²` procession 平均），或把该归一化恒等式作为精确 named 输入（不得声称为已证）。

## 对现有文件的影响（审计结论）

- `coord`/代码中“`variant_of_step3115_readouts` 已证”仅在该对齐假设下成立；因 ② 归一化冲突，不能宣称已证 Var；
- 建议：mainline 的 step3115 rung 保留为 **结构/根关系** 结果，不再作为 Var 证明渠道；Var 走 LANA 自己的 `qPilot.lhs ≤ rhs`（即 `SSIneq`/`gap` 更弱形式）或在 LANA 归一化下重写读法。

## hull section (A495；A496 后记录，LANA 已停用，仅作归一化对照)

### 我们的 hull/det 读法逐字展开
- `hullReadout`（`tmp/sheaf/xif/paper/Mzk1HullDetStep3115Actual.lean:41`）：
  ```lean
  def hullReadout (x : HullDetState label) : Real := packetLogVolume x.packet
  ```
  展开链：`packetLogVolume packet = ∑ i, Real.log (packet.scale i)`（`Volume.lean:32`），
  `= Real.log (packetDet packet)`（`packetLogVolume_eq_log_det`），
  `= matrixLogDet (packetDiagonalMatrix packet)`（`packetLogVolume_eq_matrixLogDet`）。
- `detReadout`（同文件:45）：
  ```lean
  def detReadout (x : HullDetState label) : Real := - Real.log |x.q|
  ```
  `x.q > 0` 时 `= - Real.log x.q = Real.log x.q⁻¹`（`detReadout_eq_neg_log`/`detReadout_eq_log_inv`）。
- 比较：`hullReadout x ≤ detReadout x ↔ packetDet x.packet * x.q ≤ 1`（`hullReadout_le_detReadout_iff`）。

### 与 LANA 的两层定义对照（A491–A494 结论）
1. `hullReadout` 是**有限 packet 的 log-volume**（对 label 求和/行列式）；
   LANA `Wallet.logVol D U = (1/ℓ*) Σ_i Σᶠ_{vQ} packetVol_i,vQ`（`Cor312/LogVolume.lean:177,207-209`），
   是 procession 平均的全局量。二者只在 packet 层同构，容器/procession 层无定义等式。
2. `globalIQLogVolume`（我们的 literal IQ 载体）类型是 `ENNReal` 的 Haar log-volume
  （`S2723GlobalIQHullActual`/`S3129...`），与 LANA `rhsData.rhs : ℝ = vol.processionVol (...)`
   (`Cor312/RightHandSide.lean:98-107`) 不同域；接口层唯一現成桥是
  `iqHull_logVolume_hull_eq_ofReal : W.logVolume W.hull = ENNReal.ofReal (iqHullRealVolume W)`
  （`CertificateHullWiring.lean:99`）。因此 `globalIQLogVolume(hull) = rhs` **不是**可证的
  定义等式，只能在同一 carrier 上给出 `ENNReal.ofReal rhs` 形式的接口等式。
3. A492 的 LANA 等式（仅 LANA 内部成立，不能搬到我们的定义）：
   `logVol(lgp U) = logVol U + logVol(lgp O)`（`logVol_lgp`，`IdentifiedCopies.lean:280-282`），
   `logVol(lgp O) = - sFactor(nC) * D.qPilot.absLogQ`（`logVol_lgp_integral:441-445`）。
   我们的 hull/det 读法没有 `lgp` 作用，故无对应的 `correction`。
4. A494：`rhs = -thetaPilotLogImage` 在现有定义下**为假**：`-thetaPilotLogImage > 0`
   （因 `thetaPilotLogImage = qPilotLogImage/(2ℓ) < 0`），而 `rhs = -|log Θ|` 为负量级
   （`rhs_eq_logVol`，`Rss.lean:356`）。精确差异来源三层：
   - 符号/全局性：`rhs` 是 theta-pilot **hull 的 procession 平均**（`-|log Θ|`），
     `thetaPilotLogImage` 是单 bad place 的局部 signed `2ℓ` 次根 log；
   - `2ℓ`：我们 `thetaPilotLogImage = qPilotLogImage/(2ℓ)`（`l.value = ℓ`，与 LANA `absLogQ = logQ/(2ℓ)`
     的分母一致，但我们的逐 place 除，LANA 是先加权和再除）；
   - 权重/平均：LANA 对 bad places 乘 `f_w/[F:ℚ]` 权重（`LeftHandSide.lean:58-88`）并对 ℓ* capsule 平均；
     我们的 ① 是单 place 局部量、无 weight、无 ℓ*。
   LANA 的 `sFactor`（`(Σ j²)/ℓ*`，`Pilots.lean:52-55`）只进入 `lgp`/`Wall.SS`，不在我们的读法中定义。

### 可证的精确桥（在对应 b↔w 成立的前提下）
设 `weight_w = f_w/[F:ℚ]`、`qPilotLogImage_w = Real.log‖q_w‖`（我们的局部定义），则
`lhs = -D.qPilot.absLogQ = Σ_w weight_w · thetaPilotLogImage_w`
（加权平均的逐 place θ readout），不是单个 `hullReadout ≤ detReadout`；
而我们已验证的 `hullReadout ≤ detReadout` 是同一 place 的 `2ℓ` 缩放恒等式
（`hullReadout < 0`, `detReadout = hullReadout/(2ℓ) > hullReadout`），**不蕴含** Variant。


## A497 VOID 标记（qpilot）

下列声明依赖 `thetaPilotLogImage T b := qPilotLogImage T b / (2*l.value)`（定义式除以 2ℓ，
不是独立的 Θ 读法），按 Lead A497 全部标为 **VOID / 空转**，不得再作 Cor 3.12 证据：

- `Mzk1QPilotR4Stage5AlignActual.thetaPilotLogImage`（定义本身）；
- `twoL_mul_thetaPilotLogImage`、`thetaPilotLogImage_neg`、`qPilotLogImage_lt_thetaPilotLogImage`
  （后者只是 q<0、2ℓ>1 的算术）；
- `qThetaDetReadout`、`qThetaReadout_ordered`、`qThetaReadoutPackage`、`qThetaHDD`、
  `qThetaFourTriangleSynthesis`、`cor312Conclusion_of_qThetaFourTriangle`；
- `qThetaStepXIContract`（`targetSigned := thetaSigned`、`target_le_theta := rfl`）；
- `Mzk1QThetaHullDetAlignActual` 的 `qThetaPacket/qThetaState` 及其全部读法/`qThetaHullDetSynthesis`/
  `cor312Conclusion_qThetaHullDet`（依赖同一 VOID theta 定义）；
- `Mzk1QPilotSHEDoubleImageActual` 中 `thetaPilotImage` 本身是真实 root 扩展构造（保留），
  但其 `qThetaDetVolume`/`thetaPilotLogImage` 派生的比较按 VOID 处理。

替代方案（A498/A499）：独立 Θ-pilot 对象见 `tmp/sheaf/xif/paper/Mzk1ThetaPilotObjectActual.lean`
（qroot^(2ℓ)=q、thetaValue=qroot^{j²}、Ind1/2/3 possible images、s1902 hull），
纯问题对象已构造；3.12 比较需在对象完成后按 `Cor312ToABCBridgeInterface` 的 hcomp 两条
IUT IV 比较重新接线（named 真缺口，不能用 q≤target 充数）。
