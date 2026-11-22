# B1/G-C 一般 T ψ：交接页（grace → andrew / emmy），2026-11-17 13:40 CST

## 1. G-C 一般 T ψ 的三件（全 DONE，三公理 `[propext, Classical.choice, Quot.sound]`）

### a) RR 数据层 — `Mzk1G1PsiGeneralRRDataActual`（DONE 05:17:05）
```lean
structure PsiGeneralRRData (n : Nat) (T : Finset ℚ) where
  u0 : R n
  u1 : Localization.Away (psiChartInfDenom n T)
  haffine : chart0ToOverlap n T ≫ chartMorphism0 u0 = chartInfPieceToOverlap n T ≫ chartMorphismInf u1
noncomputable def psiOfRRData (D : PsiGeneralRRData n T) : fermatCurveScheme n ⟶ projectiveLineGlued
theorem psiOfRRData_chart0_mem_p1Zero_iff (D) (p) : psiOfRRData n T D ((fermatChart0ToCurve n).base p) ∈ p1Zero ↔ D.u0 ∈ p.asIdeal
theorem psiOfRRData_chart0_image_subset (D) : (fermatChart0ToCurve n) '' {p | D.u0 ∈ p.asIdeal} ⊆ psiOfRRData n T D ⁻¹' p1Zero
```

### b) 全局零纤维 — `Mzk1G1B1GeneralPsiZeroFibreActual`（DONE 05:24:22）
```lean
theorem psiGeneral_chart0_mem_p1Zero_iff (u0) (u1) (haffine) (p) :
    psiGeneral n T u0 u1 haffine ((fermatChart0ToCurve n).base p) ∈ p1Zero ↔ u0 ∈ p.asIdeal
theorem psiGeneral_chart0_image_subset_p1Zero (u0) (u1) (haffine) : ... ⊆ psiGeneral n T u0 u1 haffine ⁻¹' p1Zero
theorem psiGeneral_preimage_p1Zero_eq (u0) (u1) (haffine) :
    (psiGeneral n T u0 u1 haffine) ⁻¹' p1Zero = (fermatChart0ToCurve n) '' {p : PrimeSpectrum (R n) | u0 ∈ p.asIdeal}
```
（`t`-chart 片无条件不贡献：`chartMorphismInf_not_mem_p1Zero`。）

### c) `ψ⁻¹(0) = D_T` — `Mzk1G1PsiGeneralZeroFibreDTActual`（DONE 05:26:49）
```lean
structure PsiGeneralRRDataWithDT extends PsiGeneralRRData n T where
  DT : Set (fermatCurveScheme n)
  hDT : (fermatChart0ToCurve n) '' {p | toPsiGeneralRRData.u0 ∈ p.asIdeal} = DT
theorem psiOfRRDataWithDT_preimage_p1Zero_eq (D) :
    (psiOfRRData n T D.toPsiGeneralRRData) ⁻¹' p1Zero = D.DT
```

## 2. B1 侧的 `Tr ⊆ DTFixed`（Tr 选取）
`Mzk1G1B1DTSubsetActual`（DONE 04:08:58）：
```lean
theorem chart0_point_mem_DTFixed_of_rational (S : Finset (PrimeSpectrum (R n))) (f : PrimeSpectrum (R n) → ℚ)
    (hf : ∀ q ∈ S, chartX n - algebraMap ℚ (R n) (f q) ∈ q.asIdeal) :
    ∀ p ∈ S, (fermatChart0ToCurve n).base p ∈ DTFixed n (S.image f)
theorem chart0_point_mem_DTFixed (p) (t) (hp : chartX n - algebraMap ℚ (R n) t ∈ p.asIdeal) :
    (fermatChart0ToCurve n).base p ∈ DTFixed n {t}
```
一般 T（q-piece 点/非有理 chart 坐标）不被任何有限有理 Tr 覆盖 → 属 route §4.1 的一般 T RR 义务。

## 3. 剩余义务（登记，不伪装闭合）
1. **一般 T 的 RR 存在性**：`PsiGeneralRRDataWithDT` 对任意 Galois-stable 有限几何点集 T（deg D_T ≥ deg K + 3）。donors：`AG_FLT_Def_AlgebraicCurve_CechSectionsOfDivisor`（`AlgebraicCurve.lSpaceOn`/`cechH0` 等）、`AG_FLT_RiemannRochPromotionActual`、`AG12CechRiemannRochActual`、`AG06bRRInterfaceActual`。
2. **0 处无分歧**：`ψ` 在 0 处 unramified —— 与 emmy 的 `hbridge`（chart-0 `smoothLocus ↔ derivative≠0`）同源；她的 `Mzk1G1B1HPolySmoothLocusActual` 出件后对接（B3 `dt/du` 也可复用）。

## 4. 与 emmy 的分工
- O3(ii)(b) `Branch(hPoly) ⊆ boundary`：emmy（`Mzk1G1B1HPolyBranchSchemeActual` 05:14:26 已归约到 `hpts` + O4 输入；O4 已无条件 DONE 05:26:19）。
- 等式版 `Branch(hPolyL) = p1Inv '' Branch(hPoly)`：emmy 另派 `Mzk1G1B1BranchIsoEqActual`（或降级显式 typeclass 参数版）；我的 `Mzk1G1B1HPolyBranchActual` 为 stub 指向她的 `HbObligations`/`PolyLoFP`。
- B3 `b3_omegaE_iso`：**可选/待消义务**（andrew 确认 F8/F1 只用 frameHeight 版；见 `coord/B3-OMEGAE-NECESSITY.md`）。
## 5. 追加（2026-11-17 13:41）：RR 数据的首个非空实例（DONE 05:39:05）
文件 `Mzk1G1PsiGeneralRRInstanceActual`（三公理）：
```lean
noncomputable def psiGeneralRRDataOfFinset (n) (T : Finset ℚ) : PsiGeneralRRDataWithDT n T
  -- u0 = psiChart0Coord n T, u1 = psiChartInfCoord n T, haffine = affine_compat_swapped,
  -- DT = DTFixed n T, hDT 由 psiChart0Coord_mem_iff（素理想含乘积 ⇔ 含一个因子）
theorem psiGeneralRRDataOfFinset_preimage_p1Zero_eq (n T) :
    (psiOfRRData n T (psiGeneralRRDataOfFinset n T).toPsiGeneralRRData) ⁻¹' p1Zero = DTFixed n T
```
即：RR-data 接口在有理点集上有具体实例，且与该接口外的 B2 全局定理
（`Mzk1G1B2Fixed5Actual.psiFixed_preimage_p1Zero_eq_DT`）一致（独立复核通过）。
一般 Galois-stable T 的实例仍需 Riemann-Roch（义务 (1)）——接口形状已由本实例固定。
## 6. 追加（2026-11-17 13:43）：O3 等式版已由 emmy 闭合 + donor 审计发现
- `Mzk1G1B1BranchIsoEqActual`（DONE 05:40:58，三公理）：
  `branch_hPolyL_eq (h)(hh) [LoFP (hPoly h hh)] [LoFP (hPolyL h hh)] : Branch (hPolyL h hh) = p1Inv '' Branch (hPoly h hh)`
  与消费版 `branch_hPolyL_eq_of_fp (h)(hh)`（LoFP 由 `of_fp` 内部提供）。
- **donor 审计**：`Mzk1G1BelyiRamificationActual` 已有两条 iso-消去等式（无需再造）：
  `branch_isIso_comp (line 399)`、`branch_comp_isIso (line 412)`；证明为纯 iso-消去（`hPolyL_def` 后两次 calc），**不需要** `Branch p1Inv = ∅`。
- **O2 强化**：等式版使 O2 归约去掉并集的 `Branch p1Inv` 项 ⇒ `Branch (hPolyL) ⊆ p1Inv '' Branch (hPoly)`，**唯一真输入是 `hbH`**。
