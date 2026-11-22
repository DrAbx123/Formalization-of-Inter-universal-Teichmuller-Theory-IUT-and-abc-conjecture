# 显式参数清单审计（grace lane 视角，2026-11-17 18:10 CST）

每条：`参数` → 等价未证对象 → owner → 真实构造计划。**均记待消义务，不计节点/目标闭合。**

## A. 本 lane（grace）相关

### A1. `T ⊆ DTFixed n Tr`（B1 的 T 选取）
- 等价未证对象：对任意有限点集 `T : Finset (fermatCurveScheme n)` 找 `Tr : Finset ℚ` 使 T 含于 DTFixed。
- 现状：**chart-0 且 chart 坐标有理**的情形已证（`Mzk1G1B1DTSubsetActual.chart0_point_mem_DTFixed_of_rational` / `_iff`，DONE 04:08:58）。
- owner：grace。
- 真实构造计划：一般 T 需 route §4.1 的 RR 段：由 `D_T = Σ[t]` 取 s0/s1 ⇒ u0（零点除子 D_T）⇒ `psiGeneral_preimage_p1Zero_eq`（DONE 05:24:22）+ `PsiGeneralRRDataWithDT.hDT` ⇒ T 含于 `ψ^{-1}(0)`；剩余 = RR sections 存在性（见 A3）。

### A2. `psiGeneralRRDataWithDT` 的有理点实例
- 现状：**DONE**（`Mzk1G1PsiGeneralRRInstanceActual` 05:39/05:44：`psiGeneralRRDataOfFinset` + `..._eq_psiFixed`）。

### A3. 一般 Galois-stable 有限几何点集 T 的 RR 存在性（G-C 主缺口）
- 等价未证对象：`∃ D : PsiGeneralRRDataWithDT n T`（任意 Galois-stable 有限几何点集 T，deg D_T ≥ deg K + 3）。
- owner：grace。
- 现状：接口已固定（`PsiGeneralRRData`/`WithDT`），有理点实例已给；**一般 T 无实例**。
- 真实构造计划：① 用 `AG_FLT_Def_AlgebraicCurve_CechSectionsOfDivisor` 的 `AlgebraicCurve.lSpaceOn`/`cechH0` 取 `s0,s1 ∈ H⁰(D_T)`（deg ≥ deg K+3 给非零且 s1 在 D_T 上非零）；② 把 s0/s1 落到 chart 环 `R n`/`Away (psiChartInfDenom n T)`（关键桥：函数域↔chart 环局部化；无现成 donor，需新写）;③ overlap 兼容用函数域相等 + 局部化泛性质；④ 用 `psiGeneral_preimage_p1Zero_eq` 收口 `ψ^{-1}(0)=D_T`。

### A4. `b3_omegaE_iso` / `omegaEIsoUnit_eq`（B3 第二式）
- 等价未证对象：`ω_Y(E_φ) ≅ φ^*O(1)` 的 unit 等式。
- owner：grace（**可选/待消义务**）。
- 现状：判定为**非 F8/F1 必需**（andrew 核对：F8 四引理/F1Consume/F1B3Link 只用 frameHeight 版；见 `coord/B3-OMEGAE-NECESSITY.md`）。对象层已 DONE（`Mzk1G1B3OmegaEIsoActual` 04:04:55/05:26:49 等）。
- 真实构造计划：extended cover 单层 Away 乘积 + `twistUnit`（f0/f1 单位比）+ `omegaEIsoUnit_eq`（route L334 逐点 dt/du，需 `SmoothCriterion`/`hbridge` 类 chart 光滑判定）→ S5 引擎；或**判定为不需要**、标可选。

## B. 其他 lane 的显式参数（与 B3/B1 相关）

### B1. `SmoothCriterion h`（emmy）
- 对象：`∀ q, q ∈ smoothLocus (chartMorphismInf h) ↔ derivative h ∉ q.asIdeal`。
- owner：emmy（`Mzk1G1B1HPolySmoothLocusActual` DONE 05:50:24，归约到此单一义务）。
- 计划（emmy 文件头）：单关系淹没表示 + Kähler `Ω ≅ A/(h′)`；无 scheme 级「光滑⇔导数≠0」桥。

### B2. `hout`（emmy）
- 对象：chart-0 外只有 `p1Zero`（`hPolyLam` 在 t=0 给 p1Zero）。
- owner：emmy。
- 现状：p1Zero 部分我方可供——**`Mzk1G1B1HPolyLamZeroActual.hPolyLam_mem_iff`（DONE 10:05:26）**：`hPolyLam h ∈ p ↔ X ∈ p`（hdeg>0）+ `chartMorphism0_mem_p1Zero_iff`；辅助 `hPolyLam_sub_eq`/`finite_primes_of_hPolyLam`（`Mzk1G1PsiFiberFiniteC2Actual:107/198`）。

### B3. `hpts`（emmy，已修正陈述）
- 对象：`Branch (hPoly) ⊆ Ci '' D ∪ p1Zero`（原陈述缺 p1Zero 是假的）。
- owner：emmy。现状：`hbH_of_value_and_ram_union_p1Zero`/`hbH_of_hbridge_and_out` 已给（decl 21/22，05:50:24）。

### B4. `SeparationInput`（alan）
- owner：alan；计划：monogenic DONE → SeparationInput → Serre δ≤B → 无条件 UFLE。grace 不重复。

### B5. `hC4`（kurt；`C2ThetaInput` 的 hThetaLower/hC4）
- owner：kurt；Route §5.3 J1（Kummer 元素 r 在 root extension L 上）尚未落。grace 不重复。

### B6. `hstepVIII`（sophie）
- owner：sophie；`Mzk1ULStepVIIIActual.hstepVIII_of_paperLetters` 已 de-conditionalized；grace 不重复。

### B7. `hlogK`/`hsQ`（david，λ）
- owner：david。grace 不重复。

### B8. `t-chart dictionary`
- **已 DONE**（emmy）：`Mzk1G1PhiFixedLChartInfBoundaryActual.chartMorphismInf_mem_boundarySetGlued_iff` + 14 条；chart-0 对偶在 `Mzk1G1PhiFixedLChart0BoundaryActual`。

## C. 结论
- grace 侧显式参数仅剩 A3（一般 T RR 存在性）为**实质缺口**；A4 为可选；A1 已部分闭合。
- 其余 lane 的参数不归 grace；与本 lane 的接口已由 `coord/B1-GC-GENERAL-PSI.md`/`coord/B3-TO-F8-20261117.md`/`coord/B3-OMEGAE-NECESSITY.md`/`coord/O3B-OBLIGATION.md` 记录。
## D. 追加（18:20）：G-C「0 处无分歧」的归约与可用件
- **值层已有**（`Mzk1G1NoncriticalPsiActual`，77 行）：
  - `psi_unramified_over_zero {T} {x : ℚ} (hx : eval x (protectedToZeroPolynomial T) = 0) : eval x (derivative (protectedToZeroPolynomial T)) ≠ 0`（27 行）
  - `psi_simple_zero {T} {t : ℚ} (ht : t ∈ T) : rootMultiplicity t (protectedToZeroPolynomial T) = 1`（34 行）
  - `psi_protected_fiber_maps_to_zero`（20 行）、`phi_protected_avoids_belyi`（40）、`phi_branch_values`（48）、`noncriticalPsi_twoChartActual`（59）。
- **scheme 层桥缺失**：值层「0 非临界值 ⇒ 简单零点 ⇒ 局部形式光滑」的 scheme 化与 emmy 的 `SmoothCriterion`（chart-0 `smoothLocus ↔ derivative ≠ 0`）是**同一个缺口**。
- ⇒ G-C 的「0 处无分歧」义务 = (i) 值层（已有）+ (ii) `SmoothCriterion` 型 scheme 桥（emmy 负责）+ (iii) 把 psiFixed 的 chart-0 多项式与 `chartMorphismInf` 的导数对应（`protectedToZeroPolynomial T` ↔ `psiChart0Coord` 的 chart 描述，已有 `psiFixed_chart0_apply` 等）。
- 结论：该义务不新增独立缺口，与 B 类共享 `SmoothCriterion`；grace 侧**不在该项上重复造**。
## E. A3 的精确阻塞分解（18:58 查证 donor 后）
`PsiGeneralRRDataWithDT` 的一般 T 存在性 = 三段，均有明确外部依赖：
1. **函数域 RR**：donor 已有现成定理 `Mzk1RRProvedActual.functionFieldRiemannRoch_proved`（`AlgebraicCurve.FunctionFieldRiemannRoch K F`），但要求一整套实例级输入：
   `[IsAlgClosed K]`、`[DecidableEq (RatFunc K)]`、`[AlgebraicCurve.HasCanonicalDivisor K F]`、`[∀ w, w.DCoordGenerates]`、`[Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [Algebra.IsIntegral (RatFunc K) F] [Module.Finite (RatFunc K) F]`、`[AlgebraicCurve.HasLocalResidue K F]`、`[∀ w, w.FiniteResidue]`、`[Nontrivial Ω[F⁄K]]`、`[AlgebraicCurve.IsCurveOver K F] ...`、`[HasCanonicalLocalResidueKStar K F]`、`[HasPrincipalDivisors K F]`、`[Algebra.IsSeparable (RatFunc K) F]`、`[Nontrivial Ω[(RatFunc K)⁄K]]` ...（见 `Mzk1RRProvedActual:30`）。
   另有 promotion 路线：`AG_FLT_RiemannRochPromotionActual.promotion_functionFieldRiemannRoch_of_riemann_and_duality (hWD : WeilDuality K F)`；`WeilDuality` 需 `RiemannIndexFormula` + `WeilDualityAdelic`（`promotion_weilDuality_of_riemannIndex_of_adelic`），即 AG_FLT 的 riemann/duality 义务。
2. **ℚ̄ → ℚ 的 Galois 下降**：donor 强制 `[IsAlgClosed K]`，而我们的曲线基域是 ℚ；route §4.1 的「Galois-stable」条件正是为此。下降段（ℚ̄ 上 section 组在 Galois 作用下的不变子空间 → ℚ 上 section）树内无现成件。
3. **函数域 → chart 环桥**：把 `AlgebraicCurve.lSpaceOn`/`cechH0` 的 section 限制到我们的固定 chart 环 `R n` / `Away (psiChartInfDenom n T)`（即 `u0 : R n`、`u1 : ...`），需要「函数域元素在 chart 上正则 ⇒ 属于 chart 环」的局部化桥；树内无 donor。
- **结论**：A3 不是单点缺口，而是依赖 (1) AG_FLT 的 RR 实例/riemann+duality、(2) Galois 下降、（3）函数域-chart 桥三段；grace 可在 (3) 先做界面（已由 `PsiGeneralRRData` 固定形状），(1)(2) 需 Lead 排期/合并其他 lane 的 RR 件。
## F. A3 重定形（route §4.2 L296 官方捷径）进展与剩余义务（19:05）
### F1. 已可证：B2 evaluation 引理的线性代数核心（DONE 11:04:34）
`Mzk1G1A3EvaluationActual.exists_forall_apply_ne_zero`（三公理）：
```lean
theorem exists_forall_apply_ne_zero
    {k : Type*} [Field k] [Infinite k] {V : Type*} [AddCommGroup V] [Module k V]
    {ι : Type*} (s : Finset ι) (K : ι → Type*) [∀ i, Field (K i)] [∀ i, Algebra k (K i)]
    (ev : ∀ i, V →ₗ[k] K i) (nev : ∀ i ∈ s, ev i ≠ 0) :
    ∃ v : V, ∀ i ∈ s, ev i v ≠ 0
```
即 route L251-261 的「有限多个真子空间不能覆盖」步骤（用 Mathlib `Subspace.exists_eq_top_of_iUnion_eq_univ`，`Mathlib.GroupTheory.CosetCover`），支持**变化的 residue field**（闭点 residue 可以是高次数域），不需要 ℚ̄→ℚ 下降件。

### F2. 剩余义务（显式，不伪装）
1. **evaluation 映射的产生**（route L257）：对每个闭点 x ∈ D_T，需要 `H⁰(O_Y(D_T)) → residue(x)` 非零。
   - 路线：`deg D_T ≥ deg K_Y + 3` ⇒ `deg(K_Y − D_T + x) ≤ −2` ⇒ 负次数线丛无截面 ⇒ Serre 对偶给 `H¹(O(D_T − x)) = 0` ⇒ 短正合列给出 evaluation 满射（几何点）/非零（闭点）。
   - 树内 donor：`AG_FLT_ProvedTheoremsPromotionActual.promotion_serrePairing_bijective_and_flip_bijective`（要求 `[PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F] [HasCanonicalDivisor] [∀ v, v.DCoordGenerates] [HasCanonicalLocalResidueKStar K F] (hC : ConstantsAreBase K F) (hRT : ResidueTheorem K F)` + 两 chart cover）；以及 `AG_FLT_SerrePairingPromotionActual.promotion_serrePairing_apply_mk (hRT)`. **`ResidueTheorem K F`、`ConstantsAreBase`、`HasCanonicalDivisor`、`DCoordGenerates`、`HasCanonicalLocalResidueKStar` 等实例均未在此 lane 构造**（属 route §4.2 第 1-5 步，其他 lane/AG_FLT 实例化义务）。
   - **精确 donor 清单**：`AG_FLT_ProvedTheoremsPromotionActual`（serrePairing_bijective、cechRiemannRoch_of_genusReached）、`AG_FLT_SerrePairingPromotionActual`（ResidueTheorem consumer）、`AG12CechRiemannRochActual.ag12_cechRiemannRoch`、`AG06bRRInterfaceActual.ag_rr_functionFieldRiemannRoch_of_duality`。
2. **闭点 evaluation 的 Galois 相容**（route L259）：先在 ℚ̄ 上逐几何点证，再用 H⁰ 域扩张相容性得每个闭点 evaluation 非零映射（核是 ℚ 上真子空间）。—— 需 H⁰ 的域扩张相容性；树内无现成件。
3. **chart 环落地**：s₀/s₁ 限制到 `R n`/`Away (psiChartInfDenom)` 得 u₀/u₁（`PsiGeneralRRData` 接口已 DONE 05:26:49；有理点实例 `psiGeneralRRDataOfFinset` DONE 05:39/05:44）—— 需 1+2 的 H⁰ section 与「函数域元素在 chart 正则」的局部化桥。

### F3. 与 F2 对应的结论
- A3 现在只剩 **F2.1/F2.2**（H⁰/Serre 的曲线实例化）与 F2.3（局部化桥）为外部依赖；route 明确“直接用已构造的 Serre pairing bijectivity”即走 F2.1 的 donor，**不接 AG_FLT 全 RR/WeilDuality 名字齐全路线**。
- F1 的线性代数核心与本 lane 的 `PsiGeneralRRData`/零纤维链已就绪；F2.1 的 `hRT : ResidueTheorem K F` 是唯一数学级大输入（其余为实例级）。
### F2.3 进展（19:25）
- **DONE 11:23:32（三公理）**：`Mzk1G1A3ChartFracActual.chartRing_isDomain (n)(hn : 0 < n) : IsDomain (R n)`。
  证明：`chartKbar_isDomain`（`IsDomain (R n ⊗[ℚ] K)`，K = 代数闭包）+ `R n` 在 ℚ 上 flat（`Module.Flat.of_free`）+ `Algebra.TensorProduct.includeLeft_injective` 给出 `R n → R n ⊗ K` 单射，再用 `Function.Injective.isDomain` 拉回。
- **下一步（已试，卡点精确）**：`away_isFractionRing (f : R n) (hf : f ≠ 0) : IsFractionRing (Localization.Away f) (FractionRing (R n))`。
  正确引理名：**`IsFractionRing.isFractionRing_of_isDomain_of_isLocalization`**（`RingTheory/Localization/LocalizationLocalization.lean:277`，需 `[IsDomain R]`、`[IsScalarTower R S T]`、`[IsLocalization M S]`、`[IsFractionRing R T]`）。
  **卡点**：Mathlib 未自动提供 `Algebra (Localization.Away f) (FractionRing (R n))` 实例（`synthInstanceFailed`）⇒ 需先手工构造该 Algebra 结构（`IsLocalization.Away` 的提升映射 `Localization.Away f ⟶ FractionRing (R n)`，f 在 fraction ring 中为 unit）。估 1 批。
- F2.1 状态不变：`ResidueTheorem K F` 无无条件 producer（全仓仅作 hypothesis），`CanonicalLocalResidueDataKStar` 是数据类（Laurent 展开性质作为字段），route §4.2 第 3-4 步未形式化 ⇒ 登记义务。
### F2.3 路线修正（19:30，查 Mathlib 后）
手工给 `Algebra (Localization.Away f) (FractionRing (R n))` 不是最佳路线；Mathlib 的 `Mathlib/AlgebraicGeometry/FunctionField.lean:119-175` 已有「affine open 的截面环 → functionField」的 `IsFractionRing` 机制（`delta IsFractionRing IsLocalization.AtPrime`、`isFractionRing_of_isDomain_of_isLocalization M ↑(stalk)`）。
**推荐路线**：
1. 用 `AG02FunctionFieldActual.agFunctionField_isFractionRing_of_isAffineOpen (U) [IsAffineOpen U] : IsFractionRing (X.presheaf.obj U) X.functionField` 于 chart-0 的开集（需 `X.presheaf.obj U ≃ R n`，即 chart 截面识别 —— 这是新的小义务）；
2. chart-inf 环 `Away (psiChartInfDenom)` 同法（其开集为 chart-∞ 片）；
3. 两者都 `IsFractionRing ... (Y_n).functionField` ⇒ 函数域桥完成，图表函数（u0/u1）与函数域元素的限制/比较有统一目标。
**新登记义务**：`chart0_presheaf_sections : (fermatCurveScheme n).presheaf.obj (chart-0 open) ≃+* R n`（及 chart-∞ 对偶）；无现成 donor（grep 无 `presheaf.obj.*chart`）。
### F2.3 batch 2（19:38）
- **DONE 11:31:02（三公理）**：`Mzk1G1A3ChartSectionsActual`：
  `chart0_sections_iso : Γ(fermatCurveScheme n, (fermatChart0ToCurve n).opensRange) ≅ CommRingCat.of (R n)`（`IsOpenImmersion.ΓIso` + `Scheme.ΓSpecIso`）；
  `chart0_sections_ringEquiv : Γ(curve, chart0Open) ≃+* R n`。chart-∞ 对偶同法（未做，登记）。
- **DONE 11:35:51（三公理，条件形式）**：`Mzk1G1A3AwayFracActual.away_isFractionRing_of_algebra (hn)(f)(hf) [Algebra (Away f) (FractionRing (R n))] [IsScalarTower …] : IsFractionRing (Away f) (FractionRing (R n))`。
  **待消义务**：手工构造 `Algebra (Localization.Away f) (FractionRing (R n))` + 相容 `IsScalarTower`（试过 `IsLocalization.lift`+`map_units`：卡 (i) `map_units` 参数形状、(ii) `algebraMap (f^k)` vs `(algebraMap f)^k`、(iii) `IsScalarTower.of_algebraMap_eq'` 的 `lift_comp` 对齐）；记在文件头。
- **下一步（F2.3 收口）**：`IsFractionRing (R n) (Y.functionField)`：
  1. `IsAffineOpen (fermatChart0ToCurve n).opensRange`（`AlgebraicGeometry.Scheme.Hom.image_of_isOpenImmersion`，`AffineScheme.lean:518`）；
  2. `[Nonempty opensRange]`（chart-0 非空）；
  3. `AG02FunctionFieldActual.agFunctionField_isFractionRing_of_isAffineOpen U hU : IsFractionRing Γ(X,U) X.functionField`；
  4. 沿 `chart0_sections_ringEquiv` 运输 `IsFractionRing` 到 `R n`（需 `AlgEquiv` 运输 `IsFractionRing`；Mathlib 有 `IsFractionRing.isFractionRing_iff`? 待查）。
### F2.3 batch 3（19:57）
- **DONE 11:45:07（三公理）** `Mzk1G1A3CurveDomainActual`：`chartInfRing_isDomain (R2 n)`、`overlapRing_isDomain (Overlap0 n)`（base change 到 k̄ + `includeLeft_injective` + `Function.Injective.isDomain`）。
- **DONE 11:49:19（三公理，重要）** `Mzk1G1A3CurveIntegralActual.curve_isIntegral (n)(hn : 0 < n) : IsIntegral (fermatCurveScheme n)`（**ℚ 上 Fermat 曲线整**）：用 generic `Scheme.GlueData.glued_isIntegral` + 两 chart/overlap 的 `IsDomain`（`Mzk1G1A3ChartFracActual`/`Mzk1G1A3CurveDomainActual`）+ overlaps 非空。
- **DONE 11:56:26（三公理，部分）** `Mzk1G1A3FunctionFieldActual.chart0_isAffineOpen : IsAffineOpen (fermatChart0ToCurve n).opensRange`（`image_of_isOpenImmersion` + `image_top_eq_opensRange`）。
  **F2.3 剩余两个精确阻塞**（文件头已记）：
  (i) `IrreducibleSpace (fermatCurveScheme n)` 的 instance 仍不被 typeclass search 发现（`IsIntegral` 给了 `haveI` 后仍失败）⇒ 需显式 `haveI : IrreducibleSpace … := (isIntegral_iff_irreducibleSpace_and_isReduced _).mp …`；
  (ii) `IsLocallyNoetherian (fermatCurveScheme n)` 不在树内 ⇒ 需用 `Scheme.GlueData.isLocallyNoetherian` 从 chart 环（MvPolynomial 商，Noetherian）构造，约 1 批。
  完成 (i)(ii) 后 `agFunctionField_isFractionRing_of_isAffineOpen` + `isFractionRing_iff_of_base_ringEquiv (chart0_sections_ringEquiv n)` 即可收口。
### F2.3 收口 DONE（20:11）
**`Mzk1G1A3FunctionFieldFinalActual` DONE 12:09:24（四公理三件套）**：
- `curve_locallyNoetherian (n) : IsLocallyNoetherian (fermatCurveScheme n)`（两 chart open cover + chart 环是 `MvPolynomial (Fin 2) ℚ` 商 ⇒ Noetherian）
- `curve_irreducibleSpace (n)(hn : 0 < n) : IrreducibleSpace (fermatCurveScheme n)`（由 `curve_isIntegral`）
- `chart0_opensRange_nonempty (n)(hn) : Nonempty (fermatChart0ToCurve n).opensRange`
- **`isFractionRing_chart0_functionField (n)(hn) [IrreducibleSpace (fermatCurveScheme n)] [Nonempty (fermatChart0ToCurve n).opensRange] : @IsFractionRing (R n) _ (fermatCurveScheme n).functionField _ ((algebraMap Γ(...) (functionField)).comp (chart0_sections_ringEquiv n).symm.toRingHom).toAlgebra`** —— F2.3 主结论（`Scheme.functionField` 的 `[IrreducibleSpace]` 参数使其必须作为 instance binder；消费者 `haveI := curve_irreducibleSpace n hn; haveI := chart0_opensRange_nonempty n hn`）。
- chart-∞ 对偶同法（未做，登记）。
## F2.2 前提审计（20:30）：ψ 的 0 纤维无分歧在这个具体实现下的适用范围

### 事实（证据）
`psiFixed` 的 chart-0 图 = `chartMorphism0 (psiChart0Coord n T)`，其中
`psiChart0Coord n T = ∏_{t∈T} (chartX n − algebraMap t)`（`Mzk1G1PsiChartMapsActual.psiChart0Coord`），
即 univariate `protectedToZeroPolynomial T = ∏ (X − C t)` 在 `x = chartX n` 处的取值（见 `Mzk1G1A3PsiChartPolyActual.psiChart0Coord_eq_aeval_protectedToZero`）。

在 `D_T` 的点 `p`（含某个 `chartX n − t`, `t ∈ T`）上：
- `t^n ≠ 1` ⇒ 曲线上 `y^n = 1 − t^n ≠ 0`，`y ≠ 0`；`df = n x^{n−1}dx + n y^{n−1}dy = 0` ⇒ `dx` 在 `Ω_{R n/ℚ}⊗k(p)` 非零；`dψ = g′(t)·dx`，`g′(t) ≠ 0`（值层 `Mzk1G1NoncriticalPsiActual.psi_unramified_over_zero`）⇒ **ψ 在 p 无分歧 ✓**。
- `t^n = 1` ⇒ `D_T` 上的点是 `(t, 0)`；此处 `f_y = n y^{n−1} = 0`, `f_x = n t^{n−1} ≠ 0` ⇒ 曲线光滑，但 `dx = 0`；展开 `x − t = (1 − y^n)^{1/n} − t = −(t/n) y^n + O(y^{2n})` ⇒ **`x − t` 在该点零阶 n ≥ 2** ⇒ `ψ`（作为 `∏(x−t)`）在 `(t,0)` **分歧**。
⇒ **route B2 的「ψ 在整个 0 纤维上无分歧」对本具体 ψ 只在 `T ∩ {t : t^n = 1} = ∅` 时成立**；一般 T 需要 route §4.1 的 RR 截面 s₀（零除子恰为 reduced `D_T`），即 A3/F2.1 的构造，不由 chart 乘积实现。

### 下游消费核对（andrew，`coord/P8-DEPENDENCY-AUDIT.md` §5）
- `b1FiniteProducer_of_branch`/`_of_chart0_data`、`B1HAvoidFinalActual`、`B2Fixed5`、P8 `perTriple.hPi`、F8 四引理均**不消费** `0 ∉ Branch(ψ)`/无分歧 ⇒ B1 的 restricted/conditional 声明不受影响；
- 该事实只影响 route B2 的语义附加结论；若未来 P8/G-K 需要 `0 ∉ S1`，必须作为显式附加条件登记（`0 ∉ Branch(psiFixed n Tr)` 或 `T ∩ {t : t^n = 1} = ∅`）。

### F2.2 条件版路线（Lead 裁 (a)）
1. **链式法则**：`D_ℚ (psiChart0Coord) = aeval (chartX n) (derivative g) • D_ℚ (chartX n)`——Mathlib 已有 `Derivation.map_aeval`（`RingTheory/Derivation/Basic.lean:150`: `D (aeval x P) = aeval x (derivative P) • D x`）⇒ 本 lane 只需实例化（`Mzk1G1A3PsiChartPolyActual`）。
2. **多变量 chart 判定**（待做，1–2 批）：`Ram (chartMorphism0 u) @ p ⇔ D_ℚ u ∉ p·Ω_{R n/ℚ}`，其中 Ω 秩 1（曲线 chart）、`D u = g′(x)·dx`；关键是 scheme-level `smoothLocus ↔ Kähler` 桥（Mathlib 有 `Derivation`/`Kaehler` 与 `FormallyUnramified/FormallySmooth` 件，但无直接的「morphism smooth ⇔ Ω 局部自由/非零」桥 ⇒ 需新写，或在其上做局部化）。
3. **条件版 F2.2 陈述**（拟）：`(hT : ∀ t ∈ T, t ^ n ≠ 1) → ∀ p ∈ D_T 对应素点, ψ 在 p 无分歧`；docstring 明示 `hT` 是纸面充分条件、general T 归 A3 RR 构造。
4. chart-∞ 对偶同法（后续 1 批）。
### 更正（20:40，Lead 裁）：F2.2 条件版 = restricted diagnostic，**不计 route B2 达成**
- 用户质疑条件版是否符合路线图；Lead 裁定**撤回**该口径：route §4.1 的 B2 是**无条件**的——`s0 = O_Y(D_T)` 的 canonical section（零除子恰为 reduced `D_T`）⇒ ψ 在 0 纤维简单零点、无分歧；
- `hT : t^n ≠ 1` 是我方 `psiFixed`（chart 乘积 `∏(x−t)`）的**实现缺陷限制**，不是 route 条件（`∏(x−t)` 的零除子只在 T 为 π-饱和且 `t^n≠1` 时等于 reduced `D_T`）；
- 因此审计 §F2.2 的条件版结论标 **restricted diagnostic only（不计 route B2 达成/不闭合）**；
- **route-conforming 路径 = A3 的 RR ψ**：由 F2.1 evaluation 引理取 `s0 ∈ H⁰(O(D_T))` 零除子恰为 reduced `D_T` ⇒ s0 在 D_T 简单零点 ⇒ du 非零 ⇒ B2 无条件（即 `PsiGeneralRRData` 的 u0/u1 构造）；
- 现状：andrew 已核对 B1/P8 当前消费链**不消费** `0 ∉ Branch(ψ)` ⇒ F2.2 降优先级，非当前阻塞项；A3 RR 数据构造（供 O5/hbranch general T）才是需要件。
- **A3 的 route-conforming 子件序列**：(1) evaluation 引理（`Mzk1G1A3EvaluationActual.exists_forall_apply_ne_zero` DONE 11:04:34）⇒ s1 避开 D_T；(2) s0 零除子 = reduced D_T ⇒ 简单零点（route B2 的实质）；(3) 简单零点 ⇒ `du` 非零（1-dim regular local ring: `ord_v(s0)=1 ⇒ D s0` 在 v 非零）⇒ ψ 无分歧；(4) u0/u1 与 chart 落地（`PsiGeneralRRData` 接口已 DONE）。
## 里程碑（21:25）：F2.3 完整（两 chart）+ F2.1 donor 级发现
### F2.3 完整 DONE
- chart-0：`Mzk1G1A3ChartSectionsActual.chart0_sections_iso/_ringEquiv`（11:31:02）；`Mzk1G1A3FunctionFieldFinalActual.isFractionRing_chart0_functionField`（12:09:24，含 `curve_locallyNoetherian`/`curve_irreducibleSpace`/`chart0_opensRange_nonempty`）。
- chart-∞：`Mzk1G1A3ChartInfSectionsActual.chartInf_sections_iso/_ringEquiv`（13:13:34）；`Mzk1G1A3FunctionFieldInfActual.chartInf_isAffineOpen`/`chartInf_opensRange_nonempty`/`isFractionRing_chartInf_functionField`（13:19:41）。
- 复用 donor：`Mzk1G1OmegaFreeActual`、`IsOpenImmersion.ΓIso`、`Scheme.ΓSpecIso`、`AG02FunctionFieldActual.agFunctionField_isFractionRing_of_isAffineOpen`、`IsFractionRing.isFractionRing_iff_of_base_ringEquiv`（全树内/ Mathlib，未重复造）。

### F2.1（evaluation 引理）donor 审计结论
- 树内 `serrePairing` 只对 **除子 0** 定义：`Def_AlgebraicCurve_SerrePairing.serrePairing (hRT) (hcover) : regularDifferentials →ₗ cechH1 ... (0) →ₗ K`；`rang_cechDiff_le_ker_residueSumOffChart` 等只处理 `(0 : Divisor)`。
- 一般 D 的对偶 API 需 `Def_AlgebraicCurve_AdelicIndex.residuePairing (W D)` + `WeilDuality K F`（或 `promotion_weilDualityAdelic_of_isAlgClosed`）+ `ResidueTheorem K F`；这些都**仍为 hypothesis/登记义务**（`AG_FLT_ProvedTheoremsPromotionActual` 需 16+ 实例 + `hC : ConstantsAreBase` + `hRT : ResidueTheorem`）。
- ⇒ F2.1 的 route L296 捷径在树内只能到「conditional on hRT/hC/curve instances」；无无条件 producer。**grace 侧可做**：以 `exists_forall_apply_ne_zero`（DONE 11:04:34）为 s1 存在性核心，把「evaluation 非零」作为显式数据接口（`A3EvalData`），其余保持义务——不再展开，因为真正 production 需要 AG_FLT 全链实例化（route 也不要求我们做）。
