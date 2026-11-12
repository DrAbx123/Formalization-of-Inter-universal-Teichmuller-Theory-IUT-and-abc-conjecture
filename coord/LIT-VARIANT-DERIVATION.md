# LIT-VARIANT-DERIVATION — lit 读法下 variant 的精确展开与化简 (A1029)

| field | value |
|---|---|
| Status | **DECISION: lit 读法下 rhs_lit = V（q-无关）、gap_lit = sF·A、variant_lit ⇔ −A ≤ V ⇔ V ≥ −A；因 V ≥ 0、A ≥ 0 该不等式**平凡真**（lit variant 无深层内容，与 `cor312Literal_of_variant` 的弱方向一致）** |
| 源 | ThetaRegion:236-241 (`ivLabels={distinguished}`, `litLabels=univ`), :251-269 (`thetaFinite`, `thetaFinite_eq`), :271-286 (`thetaPilotOn`), :315-341 (`thetaPilot/rhsData/rhsDataLit`), :333-370 (`rhsDataOn`, `concreteVariantDataLit`), ThetaRegion:168-175 (`thetaFiniteOn` union), IndAut:52-82 (`factorAut`/`image_smul_tensorLogShell`), VcI:734-744 (`logVol_hull_vcI_eq`), Gap:505/523-540 (`gap`, `gap_eq_rhs_add`, `variant_iff_le_rhs`), LeftHandSide:90-93 (`lhs=-absLogQ`) |

## 1. lit 的定义（源级）

- `ivLabels i = {distinguished i}`（ThetaRegion:236-237）；`litLabels i = Set.univ`（:239-241）；
- `thetaFiniteOn i S` = `∪_{φ∈indAut} φ '' (∪_{l∈S} scaleEltAt l • shell)`（:168-175）；
- `thetaPilotOn S` 的 region = product over c of `thetaComponentOn S`（:271-286）；
- `rhsDataLit := rhsDataOn (litLabels _)`（:338-341）；`concreteVariantDataLit.rhsData := D.rhsDataLit`（:364-370）；
- variant：`Corollary312Variant X := X.qPilot.lhs ≤ X.rhsData.rhs`（Statement:89-91），`lhs = −absLogQ`（LeftHandSide:93）。

## 2. lit 读法的精确展开（一般 e、多 place、权重、1/nC）

对每个 capsule i 与 tuple c（labels：factor k ∈ S_{j+1}，j=i+1）：
```
thetaComponent_lit(i,v,c) = ∪_{φ∈indAut} φ( ∪_{l∈univ} a_{i,l}(v) • shell(v) ),
a_{i,l} := qroot^{j^2} placed in factor l（ordp = j^2 * qOrder/(2l * ramIdx e_w)）. 
```
**逐 factor 的嵌套**：bad 位 q 收缩 ⇒ `ordp(a_{i,l}) > 0`，故 `a_{i,l} • shell ⊂ shell`
（shell 是 O-模/分数理想；乘 π^{正} 缩小）；
`leastHull` 逐 factor（product region 的 hull = 各 factor hull 之积）⇒ 在 factor k：
`union over l of (scaled factor k) = shell_k ∪ a_{i,k} shell_k = shell_k`（嵌套）；
indAut（lattice 自同构）保持 `tensorLogShell`（IndAut:52-56/`image_smul_tensorLogShell`），
故 φ 的并集仍在 shell 内且不改变 hull；
```
leastHull(thetaComponent_lit) = leastHull(shell)  (m-无关；无 q)
```
于是：
```
rhs_lit = processionVol(thetaHull_lit) = (1/nC) Σ_i Σ_{v} Σ_c packetWeight * componentVol(leastHull(shell))
        = logVol D (hullOf D (vcI D))  =: V        (由 Gap:901-906 proj_hull_vcI：vcIComp = shell)
gap_lit = rhs_lit + sF*A − V  (Gap:523-527 的同型) = sF*A
```
（`V = logVol(hull vcI)` 与 q 无关；`A = Σ_w weight_w*qOrder_w logp_w/(2l)`。）

## 3. lit variant 的化简与可证性

variant（Gap:531-540 形式，lit 数据）：
```
−A ≤ rhs_lit = V   ⇔   V ≥ −A   ⇔   V + A ≥ 0
```
因 `A ≥ 0`（qOrder>0, weight>0, logp>0），只需 `V ≥ 0` 即得 `V ≥ −A`。
`V ≥ 0` 来源：`logVol_hull_vcI_eq`（VcI:741）`V = (Σ_iΣ_v hullPacket_i(v))/nC`；
`hullPacket` 的 tame 展开 `Σ_c packetWeight componentVol(leastHull shell)`，其 finite 部分
`componentVol_leastHull_tensorLogShell_eq = Σ logShellRadius·logp`（VcI:603-605），
`logShellRadius ≥ 0`（log-shell 半径 = `-ordp` 最大元；需 green 引理）；arch 部分为 log-shell 正体积；
⇒ **V ≥ 0 是 GAP-VNONNEG（需要 `logShellRadius_nonneg` 与 arch/finite 正性端口）**。

若 `V ≥ 0` 得证，则 **lit variant 无条件可证且平凡**（`−A ≤ V` 仅用 A≥0, V≥0）。
这与 `cor312Literal_of_variant`（iv ⇒ lit）是弱方向一致：lit 内容极弱；
**真正的 IUT 内容是 iv**（scaled shell，非平凡），与本项目 ABC 桥所用（`MainTheorem` 用 iv）一致。

## 4. 证明所需局部引理清单

1. **NEST**：`a • shell ⊂ shell`（q 收缩，ordp(a)>0；shell 为 O-模/分数理想）；
   端口：`componentVol_prod_incl_smul_integral`、`scaleElt_eq_one`（good 位）、`ordp_qrootOf > 0`；
2. **HULL-PROD**：`leastHull(productRegion U) = productRegion (λc => leastHull (U c))`（逐 factor）；
   或直接用 `proj_hull_thetaPilot`（Gap:909-914）+ `leastHull_mono`/`leastHull_eq`；
3. **IND-AUT-SHELL**：`φ ∈ indAut ⇒ φ '' tensorLogShell = tensorLogShell`（IndAut:52-56，green）；
   以及 `φ(a•shell) ⊆ shell`（由 a•shell ⊂ shell 与 φ 保 shell）；
4. **HULL-LIT=VC**：`thetaHull_lit = hullOf(vcI)`（逐 component `leastHull(shell)`，Gap:901-906 `proj_hull_vcI`）；
5. **VNONNEG**：`V ≥ 0`（`logShellRadius_nonneg` + arch/finite 正性；GAP-VNONNEG）；
6. **GAP-LIT-ID**：`gap_lit = sF*A`（由 gap 定义 + `logVol_lgp`/`logVol_lgp_integral` 同型推导）。

## 5. Lean 陈述草案

```lean
/-- lit thetaHull is the vcI hull (q cancels in the union over all labels). -/
theorem thetaHull_lit_eq_hull_vcI (D : InitialThetaData) :
    (concreteVariantDataLit D).rhsData.thetaHull = hullOf D (vcI D) := by
  -- 逐 component: leastHull(shell) = proj_hull_vcI
  sorry -- GAP: HULL-LIT=VC (not yet proved)

/-- rhs_lit = V (q-independent). -/
theorem rhs_lit_eq_V (D : InitialThetaData) :
    (concreteVariantDataLit D).rhsData.rhs = logVol D (hullOf D (vcI D)) := by
  unfold RHSData.rhs
  rw [thetaHull_lit_eq_hull_vcI]

/-- lit gap = sF * A. -/
theorem gap_lit_eq_sF_mul_A (D : InitialThetaData) :
    gapLit D = sFactor (nC D) * D.qPilot.absLogQ := by
  -- from gap_eq_rhs_add 型 + rhs_lit_eq_V
  sorry -- GAP: GAP-LIT-ID

/-- lit variant is trivial: -A <= V. -/
theorem variant_lit_of_V_nonneg (D : InitialThetaData)
    (hV : 0 <= logVol D (hullOf D (vcI D))) :
    Corollary312Variant (concreteVariantDataLit D) := by
  rw [corollary312Variant_iff]
  have hA : 0 <= D.qPilot.absLogQ := by
    -- A = sum weight*qOrder*logp/(2l) >= 0
    sorry -- port: absLogQ_nonneg
  linarith [hV, hA]
```
（`sorry` 仅作为 GAP 占位标注，正式文件不允许；本任务不写生产 Lean。）

## 6. 结论

1. **lit 读法**：`rhs_lit = V`、`gap_lit = sF·A`、`variant_lit ⇔ V ≥ −A`；
2. 因 `A ≥ 0`，只需 `V ≥ 0` ⇒ **lit variant 平凡可证**（`−A ≤ V`），无 IUT 深层内容；
3. 与 `cor312Literal_of_variant` 弱方向一致；**ABC 的实质内容是 iv**（project 的 `concreteVariantData`
   与 lana `MainTheorem` 都用 iv）；
4. 若 owner 决定以 lit 为形式化目标，可直接证（GAP-VNONNEG + HULL-LIT=VC + GAP-LIT-ID 三个局部引理）；
   若以 iv 为目标，需 A1027/A1028 的稳定性问题（iv q-不稳定）另行处理；
5. 本任务不写生产 Lean；建议把 GAP-VNONNEG/HULL-LIT=VC/GAP-LIT-ID 登记为下一步的三个局部引理。