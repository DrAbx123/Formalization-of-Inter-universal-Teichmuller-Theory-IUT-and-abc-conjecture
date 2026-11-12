# CHAIN2-WIRING-SPEC — 链二 G 的真实接线规格（lana 根树源）

日期：2026-11-12；qpilot（A887；A890 行号修正）。**所有 lana 路径相对根 `Iut/` 树（`D:/lean/Iut/...`）。** **源读取的精确类型/字段规范**；用于给 abc 的 `GlobalConstraint` 与 `qPilotOrd` 接线。相关 lana 文件的部分 olean 仍在根闭包构建（当前根构建 9/164，其余在跑），本规格不宣称编译。

## 1. 五条源定理的精确输入/输出类型

### (a) `rlf_unique`（`Iut/LogLink/Thm311Rest.lean:473`）
```lean
-- 上下文：variable {V : Type} {bad : Finset V}
theorem rlf_unique (B B' : ValBPS V bad) (h : B.PF = B'.PF) :
    Nonempty (Unique (B.Iso B'))
```
- 输入：`B B' : ValBPS V bad`（字段见下）；`h : B.PF = B'.PF`，其中 `PF : Submodule ℝ (V →₀ ℝ)`。
- 输出：`Nonempty (Unique (B.Iso B'))`；`Iso` 字段 `toLinearEquiv : B.C ≃ₗ[ℝ] B'.C`、`map_localPilot : ∀ v, toLinearEquiv (B.localPilot v) = B'.localPilot v`。

`ValBPS`（`Iut/Wall/BPS.lean:175 structure ValBPS (V : Type) (bad : Finset V)`）：
- `C : Type`；`instAddCommGroup : AddCommGroup C`；`instModule : Module ℝ C`；`finrank_eq_one : Module.finrank ℝ C = 1`；`localPilot : V → C`；`localPilot_ne_zero : ∀ v, localPilot v ≠ 0`；`pilot_ne_zero : ∑ v ∈ bad, localPilot v ≠ 0`。
- `pilot B : B.C := ∑ v ∈ bad, B.localPilot v`；
- `sumMap B : (V →₀ ℝ) →ₗ[ℝ] B.C := Finsupp.linearCombination ℝ B.localPilot`；
- **`PF B : Submodule ℝ (V →₀ ℝ) := LinearMap.ker B.sumMap`**（`Iut/Wall/BPS.lean:210`）。
- `ValBPS.nonempty_iso_iff : Nonempty (Iso B B') ↔ B.PF = B'.PF`（`Iut/Wall/BPS.lean`，Lemma 4.1.7）。

### (b) `scaling_iff`（`Iut/ThetaLink/Link.lean:206`）
```lean
-- 上下文：variable (D : InitialThetaData.{0})
theorem scaling_iff (c : ℝ) (hc : 0 < c) :
    Nonempty ((GlobalRealified.scale c hc).obj (thetaPilotObj D) ≅ qPilotObj D) ↔
      c = (D.wallS)⁻¹
```
- 类型：`GlobalRealified K`（对象类型；`Iut/Frobenioid/Wall.lean` 内）；`scale (c : ℝ) (hc : 0<c) : GlobalRealified K ⥤ GlobalRealified K`（`Iut/Frobenioid/Wall.lean:72`）；
- `qPilotObj D : GlobalRealified D.Kt := ofBundle (qPilotBundle D)`（`Iut/Frobenioid/Wall.lean:128`）；
- `thetaPilotObj D : GlobalRealified D.Kt := ⟨pt, ((nC D : ℝ))⁻¹ • ∑ i : Fin (nC D), toDiv (thetaBundle D (i.1 + 1))⟩`（`:132`）；
- `D.wallS : ℝ`（`InitialThetaData` 字段；`D.wallS_ne_zero`）；
- 配套：`degreeNorm_qPilotObj : (qPilotObj D).degreeNorm = D.qPilot.absLogQ`；`degreeNorm_thetaPilotObj : (thetaPilotObj D).degreeNorm = D.wallS * D.qPilot.absLogQ`；`scale_thetaPilotObj`；`isEmpty_iso_thetaPilot_qPilot`（`Iut/WallEquiv/Basic.lean:190`）。

### (c) `PF_thetaVal`（`Iut/Wall/Pilots.lean:174`）——链二 PF 计算的核心
```lean
-- 上下文：variable {V : Type} (L : LocalDegrees V) (s : ℝ)
theorem PF_thetaVal (hs : s ≠ 0) : (thetaVal L hs).PF = (qVal L).PF
```
- `LocalDegrees V`（`Iut/Wall/Pilots.lean`）：字段 `bad : Finset V`、`deg : V → ℝ`、`deg_pos : ∀ v, 0 < deg v`、`bad_nonempty : bad.Nonempty`；
- `qVal L : ValBPS V L.bad`：`C = ℝ`、`localPilot = L.deg`、`pilot = ∑ v∈bad, deg v`（`qVal_pilot`）；
- `thetaVal L (s) (hs) : ValBPS V L.bad`：`C = (V →₀ ℝ) ⧸ LinearMap.ker (psi L s)`，`psi L s = s • Finsupp.linearCombination ℝ L.deg`，`localPilot v = Quotient.mk (single v 1)`；
- 结论：`thetaVal` 与 `qVal` 的 `PF` **相等**（同 `kernel`，因 `s ≠ 0`），故 `rlf_unique` 直接适用。
- 度数：`degTheta_pilot : degTheta L hs (thetaVal L hs).pilot = s * ∑ v∈bad, L.deg v`；
- 全局：`degreeNorm_qPilotObj_eq_pilot : (qPilotObj D).degreeNorm = (qVal D.bpsDegrees).pilot`。

### (d) `componentVol_image_algEquiv` / `IsLeastHull.componentVol_eq`（`Iut/Concrete/Ind1Invariance.lean:144,192`）
```lean
-- vQ : RationalPlace, c : ι → LocalTheory.Fiber k vQ（Fintype ι）
theorem componentVol_image_algEquiv
    (E : Tensor K vQ c ≃ₐ[baseField vQ] Tensor K vQ c') (S : Set (Tensor K vQ c)) :
    componentVol vQ c' (E '' S) = componentVol vQ c S

theorem IsLeastHull.componentVol_eq
    (E : Tensor K vQ c ≃ₐ[baseField vQ] Tensor K vQ c')
    {U : Set (Tensor K vQ c)} {a : Tensor K vQ c} (ha : IsLeastHull U a)
    {b : Tensor K vQ c'} (hb : IsLeastHull (E '' U) b) :
    componentVol vQ c' (b • integralAt vQ c') = componentVol vQ c (a • integralAt vQ c)
```
- `componentVol (S : Set (Tensor K vQ c)) : ℝ := Real.log ((haar vQ c S).toReal / (haar vQ c (integralAt vQ c)).toReal) / Module.finrank (baseField vQ) (Tensor K vQ c)`（`Iut/Concrete/LocalConstruct/Volume.lean:196`）；
- `IsLeastHull U a : Prop := IsUnit a ∧ U ⊆ a • integralAt vQ c ∧ ∀ b, IsUnit b → U ⊆ b • integralAt vQ c → a • integralAt vQ c ⊆ b • integralAt vQ c`（`Ind1Invariance.lean:161`）。

### (e) 乘积/标度律（`Iut/Concrete/LocalConstruct/ScaleVolume.lean:118`、`Prop14.lean:108`）
```lean
theorem componentVol_prod_incl_smul_integral (hc : ∀ j, IsOver K p (c j))
    (w : ι → FinitePlace K) (h : ∀ j, c j = Place.finite (w j))
    (y : ∀ j, completionAt K (w j)) (hy : ∀ j, y j ≠ 0) :
    componentVol (.finite p) c ((∏ j, incl p c j (w j) (h j) (y j)) • integral p c) =
      -(∑ j, ordp K (w j) (y j)) * Real.log p

theorem componentVol_prime_pow_smul_integral (hc : ∀ j, IsOver K p (c j)) (m : ℕ) :
    componentVol (.finite p) c (((p : ℕ) : Tensor K (.finite p) c) ^ m • integral p c) =
      -(m : ℝ) * Real.log p
```
- 归一化：`componentVol` 的分母 `Module.finrank (baseField vQ) (Tensor ...)`；`integral p c` 是 packet 的整结构；`ordp K w y` 是局部赋值。

## 2. 链二接线：`qPilotOrd` 与 `GlobalConstraint`（Lean 伪代码/签名）

```lean
-- (1) q-pilot 的序：由 lana Wall 的 q-pilot value-group BPS 提取
noncomputable def qPilotOrd {V : Type} (L : LocalDegrees V) : ℝ := (qVal L).pilot
theorem qPilotOrd_eq_sum {V} (L : LocalDegrees V) :
    qPilotOrd L = ∑ v ∈ L.bad, L.deg v := by
  simpa [qPilotOrd] using qVal_pilot L

-- (2) 与全局 Frobenioid 的 degree 对齐（degreeNorm_qPilotObj_eq_pilot）
theorem qPilotOrd_eq_degreeNorm {D : InitialThetaData.{0}} :
    qPilotOrd D.bpsDegrees = (qPilotObj D).degreeNorm := by
  rw [qPilotOrd, ← degreeNorm_qPilotObj_eq_pilot]

-- (3) Θ-side 的序：degTheta_pilot
theorem thetaPilotOrd_eq {V} (L : LocalDegrees V) (s : ℝ) (hs : s ≠ 0) :
    degTheta L hs (thetaVal L hs).pilot = s * qPilotOrd L := by
  rw [degTheta_pilot, qPilotOrd, qVal_pilot]

-- (4) 候选族 + 全局约束 G
structure Chain2CandidateFamily (V : Type) (L : LocalDegrees V) where
  cand : Type
  bps : cand → ValBPS V L.bad
  samePF : ∀ e, (bps e).PF = (qVal L).PF

structure GlobalConstraint (D : InitialThetaData.{0}) where
  V : Type
  L : LocalDegrees V
  -- q-pilot BPS 与 Θ-pilot 的精确标度（唯一 c = wallS⁻¹）
  wallS_pos : 0 < D.wallS
  theta_scale : Nonempty
    ((GlobalRealified.scale D.wallS⁻¹ (inv_pos.mpr wallS_pos)).obj (thetaPilotObj D)
      ≅ qPilotObj D)
  family : Chain2CandidateFamily V L
  -- 链二的位置：候选结构的 BPS 必须与 q-pilot 有相同 PF
  samePF : ∀ e, (family.bps e).PF = (qVal L).PF := family.samePF

-- (5) G 的两个输出（直接来自源定理）
theorem GlobalConstraint.candidate_unique {D} (G : GlobalConstraint D) (e : G.family.cand) :
    Nonempty (Unique ((G.family.bps e).Iso (qVal G.L))) := rlf_unique _ _ (G.family.samePF e)

theorem GlobalConstraint.scale_iff {D} (G : GlobalConstraint D) (c : ℝ) (hc : 0 < c) :
    Nonempty ((GlobalRealified.scale c hc).obj (thetaPilotObj D) ≅ qPilotObj D) ↔
      c = D.wallS⁻¹ := scaling_iff D c hc

theorem GlobalConstraint.not_iso {D} (G : GlobalConstraint D) :
    IsEmpty (thetaPilotObj D ≅ qPilotObj D) := isEmpty_iso_thetaPilot_qPilot D
```

**语义**：G 不是额外不等式，而是两件刚性数据：
1. **PF 相等 ⇒ 唯一同构**（`rlf_unique`）：候选结构的 BPS 一旦 PF 与 q-pilot 相同，结构选择被唯一同构消除（并集塌缩）；
2. **全局 realified 度只能按 `1/wallS` 标度**（`scaling_iff`）：Θ-pilot 对象与 q-pilot 对象在同一 GlobalRealified 内不同构（`isEmpty_iso_thetaPilot_qPilot`），只能在 `scale (wallS⁻¹)` 后等同。

## 3. PF 数据在 q-pilot 与候选族上的计算方式（需从 lana 实例提取的量）

### 3.1 q-pilot 侧
- `D.bpsDegrees : LocalDegrees V`（字段 `V`, `bad`, `deg`）；
- `qVal D.bpsDegrees : ValBPS V bad`，`C = ℝ`，`localPilot = deg`；
- `PF = ker (Finsupp.linearCombination ℝ deg : (V →₀ ℝ) →ₗ[ℝ] ℝ)`；
- `qPilotOrd = ∑ v ∈ bad, deg v`；`(qPilotObj D).degreeNorm = qPilotOrd`（`degreeNorm_qPilotObj_eq_pilot`）。

### 3.2 候选族侧
- 每个候选 `e` 给 `bps e : ValBPS V bad`：需提取其 `C`、`localPilot e : V → C`；
- `PF (bps e) = ker (sumMap (bps e))`；`samePF e : PF(bps e) = PF(qVal)` 作为 G 的输入（class-B）；
- 若候选 BPS 的 `C` 不是 ℝ（如张量空间），PF 仍是 `(V →₀ ℝ)` 的子空间，比较是线性代数：需给出 `PF` 的生成元/秩（或直接假设 `samePF`）。
- 由 `rlf_unique`：`samePF e` ⇒ `Nonempty (Unique ((bps e).Iso qVal))`；即候选的 local pilots 与 q-pilot 相差唯一线性同构。

### 3.3 Θ 侧
- `thetaVal L (D.wallS)`：`C = (V →₀ ℝ) ⧸ ker (psi L wallS)`，localPilot = `Quotient.mk (single v 1)`；
- `PF_thetaVal (D.wallS_ne_zero) : (thetaVal L wallS).PF = (qVal L).PF`；
- `degTheta_pilot`：`degTheta L hs (thetaVal L hs).pilot = wallS * qPilotOrd`；
- 这解释了为何 **BPS 层 PF 相等**而 **global realified 层不同构**：差异被 `scale wallS⁻¹` 吸收（`scaling_iff`）。

### 3.4 候选区域的 log-volume（componentVol 接线）
- 输入：`vQ : RationalPlace`、`c : ι → LocalTheory.Fiber k vQ`、候选区域 `U : Set (Tensor K vQ c)`、least hull 单位 `a`；
- `vol := componentVol vQ c (a • integralAt vQ c)`；
- 结构不变性：`IsLeastHull.componentVol_eq`（换 `c`/`E` 不变）；
- 初等选择：`componentVol_prod_incl_smul_integral` 给出 `= -(∑ ordp) * log p`（`R` 已被 `integral` 归一化吸收）；
- p-幂：`componentVol_prime_pow_smul_integral` 给出 `= -m * log p`。

### 3.5 需要从 lana 实例提取的量（清单）
1. `D : InitialThetaData` 的 `bpsDegrees : LocalDegrees V`（`V`, `bad`, `deg`）、`wallS`、`wallS_ne_zero`、`qPilot.absLogQ`、`nC`；
2. 候选族每个 `e` 的 `ValBPS V bad`（localPilot 值）；
3. PF 等式 `samePF e`（作为 G 输入；若需计算：`PF` 生成元/秩）；
4. `componentVol` 侧：`vQ`、`c`、`U`、`a`、`IsLeastHull U a` 见证；`ordp K w y`、`differentExponent`、`IsOver` 见证；
5. `GlobalRealified` 侧：`thetaPilotObj D`、`qPilotObj D`、`GlobalRealified.scale`、`wallS⁻¹`。

## 4. 源位置索引

| 内容 | 源 |
|---|---|
| `ValBPS`, `pilot`, `sumMap`, `PF`, `Iso`, `nonempty_iso_iff` | `Iut/Wall/BPS.lean:175,~200,210,…` |
| `rlf_unique`, `rlf_cocycle`, `RposOrbit`, `mem_rposOrbit_iff`, `rposOrbit_compat` | `Iut/LogLink/Thm311Rest.lean:473,479,487,491,506` |
| `scaling_iff` | `Iut/ThetaLink/Link.lean:206` |
| `thetaPilotObj`, `qPilotObj`, `scale`, `degreeNorm_*` | `Iut/Frobenioid/Wall.lean:72,128,132,~140,~150` |
| `PF_thetaVal`, `qVal`, `thetaVal`, `degTheta_pilot`, `LocalDegrees` | `Iut/Wall/Pilots.lean:106,144,174,~167,~80` |
| `componentVol`, `integralAt` | `Iut/Concrete/LocalConstruct/Volume.lean:196,…` |
| `IsLeastHull`, `componentVol_image_algEquiv`, `IsLeastHull.componentVol_eq` | `Iut/Concrete/Ind1Invariance.lean:161,144,192` |
| `componentVol_prod_incl_smul_integral` | `Iut/Concrete/LocalConstruct/ScaleVolume.lean:118` |
| `componentVol_prime_pow_smul_integral` | `Iut/Concrete/LocalConstruct/Prop14.lean:108` |
| `isEmpty_iso_thetaPilot_qPilot` | `Iut/WallEquiv/Basic.lean:190` |

**未核**：以上字段/签名按源文本读取；相关文件 olean 未全部产出（根构建进行中）；`GlobalConstraint`/`qPilotOrd` 为链二设计对象，非 lana 已有定义。