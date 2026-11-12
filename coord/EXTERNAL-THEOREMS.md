# EXTERNAL-THEOREMS.md — 外部定理登记表（C 路线）

**政策（用户指令 A855）**：上游（anthro P2M、ImperialCollegeLondon/FLT、Mestre–Oesterlé、Pasten 等）**视为已证定理，不再搬运/编译**。凡进入我们的链，一律以 **class-B 输入 Prop**（显式假设）登记，不伪造 Lean 证明。

**来源与版本（只读）**

| 源 | 路径 | rev | toolchain | 许可 | 统计 |
|---|---|---|---|---|---|
| anthro fermats-last-theorem | `tmp/external/flt-lean`（Definitions 1450 文件、P2M/Sol 29505、Theorems 29504） | `6e837e75355538c7f80bab5b956861e86c4eacc2` | leanprover/lean4:v4.33.1 | Apache-2.0 | Definitions 0 sorry/0 axiom/0 opaque（已核） |
| ImperialCollegeLondon/FLT | `tmp/external/flt271` | `a3210204ad8876e851e32f73dd97d882bf1ccd0a` (2026-10-22) | leanprover/lean4:v4.35.0 (mathlib `56a0058`) | Apache-2.0 | 271 .lean；70 sorry；3 axiom（Assumptions/） |
| lana-agents/heights | 在线 manifest rev `f4379dbccc8cdc4faa894a236d5581a6a635c5b5`（本会话 git 连接失败，未 clone） | — | — | — | C 路线高度来源，待取 |

**方法**：A 类条目的“精确陈述”直接从上游 Lean 源文件读取 `theorem` 签名（原样，长签名截断处标 `…`；完整签名见 `tmp/external_theorem_statements.json`）；L 类为文献条目，登记工作形式并标注“待原文核对”。

## 1. A 类：上游 Lean 定理（外部已证）

| ID | 名称 | 源文件 | sorry/axiom | 采用形式 | 消费者 |
|---|---|---|---|---|---|
| A1 | `FreyPackage.frey_isModular` | Theorems/Thm_FreyPackage_frey_isModular.lean | 0/0 | class-B `Prop`：`∀ P : FreyPackage, P.freyCurve.IsModular`（Frey 曲线模性） | `P2M/Sol/S_FreyPackage_no_frey_package.lean`；C 链：Frey 曲线 → 模性 |
| A2 | `atPNewLowering` | Theorems/Thm_FreyPackage_atPNewLowering.lean | 0/0 | class-B `Prop`：`∀ P : FreyPackage, P.AtPNewLowering`（p 处新水平下降） | `S_FreyPackage_atPNewLowering`、`S_FreyPackage_level_lowering_at_p_of_conductorLevel` |
| A3 | `RibetIrr.irreducible_of_point_of_not_dvd` | Theorems/Thm_RibetIrr_irreducible_of_point_of_not_dvd.lean | 0/0 | class-B：Ribet 不可约性判据（点 + p∤N ⇒ 不可约） | `S_CuspForm_isFlatAt_of_point_of_not_dvd` |
| A4 | `RibetIrr.exists_dickson_eval_eq_of_span_ne_top` | Theorems/Thm_RibetIrr_exists_dickson_eval_eq_of_span_ne_top.lean | 0/0 | class-B：Dickson 求值存在性（span ≠ ⊤） | Ribet/Irr 链 |
| A5 | `TaylorWiles.exists_isTaylorWilesPrime` | Theorems/Thm_TaylorWiles_exists_isTaylorWilesPrime.lean | 0/0 | class-B：`∀ ρ p n seed T, ∃ q ∉ S,T, IsTaylorWilesPrime ρ p n q` | `S_ResidualGaloisRep_exists_taylorWilesPrime_notMem_of_seed`、`S_TaylorWiles_exists_isTaylorWilesPrime` |
| A6 | `CerednikDrinfeld.ShimuraCurveModel.ModuliWitnessD.exists_constantReduction_of_isGoodReductionModel_of_curveModel` | Theorems/Thm_CerednikDrinfeld_ShimuraCurveModel_ModuliWitnessD_exists_constantReduction_of_isGoodReductionModel_of_curveModel.lean | 0/0 | class-B：好约化模型 ⇒ 常约化（Cerednik–Drinfeld） | `S_CerednikDrinfeld_ShimuraCurveModel_eichlerShimura_of_rigidModuliWitness_of_two_mul_dvd` |
| A7 | `CerednikDrinfeld.ShimuraCurveModel.galJ_eq_self_of_mem_inertiaSubgroupIn_of_smoothOfRelativeDimension_one` | Theorems/Thm_CerednikDrinfeld_ShimuraCurveModel_galJ_eq_self_of_mem_inertiaSubgroupIn_of_smoothOfRelativeDimension_one.lean | 0/0 | class-B：Shimura 曲线 Jacobian 在惯性下不动（光滑相对维数 1） | Cerednik–Drinfeld/Shimura 链 |
| A8 | `CuspForm.IsNewform.eq_of_forall_qCoeff_eq` | Theorems/Thm_CuspForm_IsNewform_eq_of_forall_qCoeff_eq.lean | 0/0 | class-B：新形式由素数 q-系数决定 | `S_CuspForm_IsNewform_level_eq_and_qCoeff_eq_of_forall_qCoeff_eq` 等 |
| A9 | `AutomorphicForm.exists_analyticOnNhd_eq_sub_one_half_mul_peterssonIntegral_of_norm_le_archHeight_pow` | Theorems/Thm_AutomorphicForm_exists_analyticOnNhd_eq_sub_one_half_mul_peterssonIntegral_of_norm_le_archHeight_pow.lean | 0/0 | class-B：Petersson 积分表示（arch height 控制） | E7-Petersson/分析界链 |
| A10 | `AutomorphicForm.exists_norm_a_le_absNorm_rpow_and_norm_b_le_of_smoothCuspRealizationAt_of_peterssonPairing` | Theorems/…_of_peterssonPairing.lean | 0/0 | class-B：Petersson 配对下的 a/b 系数范数界 | E7-Petersson/分析界链 |
| A11 | FLT271 `Patching/` 框架（14 文件 = 7 顶层 + 7 Utils；import 闭包 19 = 14+1+4） | `tmp/external/flt271/FLT/Patching/` | 0/0（14 文件扫描） | 外部代码切片（Taylor–Wiles patching）：`ker_RtoT_le_nilradical`、`nonempty_inverseLimit_of_finite`、`exists_twoSidedIdeal_isOpen_and_subset` 等 | FLT271 `FLT/Deformations`/modularity lifting；C 链 Patching 步骤 |

### A 类精确陈述（从上游 Lean 源读取）

- **A1**：`theorem FreyPackage.frey_isModular (P : FreyPackage) : P.freyCurve.IsModular`
- **A2**：`theorem atPNewLowering (P : FreyPackage) : P.AtPNewLowering`
- **A3**：`theorem RibetIrr.irreducible_of_point_of_not_dvd (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (S : Finset ℕ) (_hpS : p ∈ S) (_hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S) (𝒪' : Type) [CommRing 𝒪'] [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪'] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪') 𝒪'] [Finite (IsLocalRing.ResidueField 𝒪')] [CharZero 𝒪'] (_hp𝒪' : (p : 𝒪') ∈ IsLocalRing.maximalIdeal 𝒪') (K : …) …`（完整签名见 JSON）
- **A4**：`theorem RibetIrr.exists_dickson_eval_eq_of_span_ne_top (p : ℕ) [Fact p.Prime] (N : ℕ) (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsAdicComplete …] [Finite …] [CharZero 𝒪] (K : Type) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (ρ : GaloisRepAdic 𝒪) (hp : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪) (hN : N ≠ 0) …`（完整签名见 JSON）
- **A5**：`theorem TaylorWiles.exists_isTaylorWilesPrime {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L] {𝕜 : Type*} [Field 𝕜] (ρ : TaylorWiles.ResidualRep L 𝕜) (p n : ℕ) {S : Finset ℕ} (seed : TaylorWiles.Seed ρ p n S) (T : Finset ℕ) : ∃ q : ℕ, q ∉ S ∧ q ∉ T ∧ TaylorWiles.IsTaylorWilesPrime ρ p n q`
- **A6**：`theorem CerednikDrinfeld.ShimuraCurveModel.ModuliWitnessD.exists_constantReduction_of_isGoodReductionModel_of_curveModel {N q q' : ℕ} [NeZero N] (hN : Squarefree N) [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q) (D : ℕ) (hD : 2 * N * q * q' ∣ D) (hq5 : 5 ≤ q) (hq'5 : 5 ≤ q') {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q') (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : …) …`（完整签名见 JSON）
- **A7**：`theorem CerednikDrinfeld.ShimuraCurveModel.galJ_eq_self_of_mem_inertiaSubgroupIn_of_smoothOfRelativeDimension_one {a b : ℚ} {R : Submodule ℤ ℍ[ℚ, a, b]} {ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ} {𝒮 : ℕ → Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ} (M : ShimuraCurveModel R ι 𝒮) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (i : O →+* AlgebraicClosure ℚ) (hi : …) …`（完整签名见 JSON）
- **A8**：`theorem CuspForm.IsNewform.eq_of_forall_qCoeff_eq {M R : ℕ} [NeZero M] {g g' : CuspForm (CongruenceSubgroup.Gamma0 R) 2} (hg : CuspForm.IsNewform g) (hg' : CuspForm.IsNewform g') (hR : R ∣ M) (h : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ModularFormClass.qCoeff g ℓ = ModularFormClass.qCoeff g' ℓ) : g = g'`
- **A9**：`theorem AutomorphicForm.exists_analyticOnNhd_eq_sub_one_half_mul_peterssonIntegral_of_norm_le_archHeight_pow (F : Type) [Field F] [NumberField F] (w a c u : ℝ) …`（完整签名见 JSON）
- **A10**：`theorem AutomorphicForm.exists_norm_a_le_absNorm_rpow_and_norm_b_le_of_smoothCuspRealizationAt_of_peterssonPairing (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) …`（完整签名见 JSON）

## 2. L 类：文献条目（E7 组件及 C 路线其它文献输入）

| ID | 组件 | 文献来源 | 工作形式（采用为 class-B Prop） | 状态 |
|---|---|---|---|---|
| L1 | Faltings 高度存在性/性质 | Faltings, *Endlichkeitssätze für abelsche Varietäten über Zahlkörpern*, Invent. Math. 73 (1983)（DOI:10.1007/BF01388432） | `FaltingsHeightExists`：对 ℚ 上椭圆曲线存在实值稳定高度 `h_F(E)`，同构不变、有限扩张下按次数归一；性质含 `h_F(E) ≥ C_0`（常数待原文核对） | 文献；无上游 Lean 源（anthro/FLT271 均无 Faltings 关键词） |
| L2 | Faltings 高度界（E7） | Faltings 1983；Silverman, *Advanced Topics*, Ch. XI | `FaltingsHeightBound`：`h_F(E) ≤ (1/2)·log|Δ_E| + C_1`（Frey/E 的显式对数界，常数待核） | 文献；上游无 Lean |
| L3 | Mestre–Oesterlé | Mestre & Oesterlé, *Courbes de Weil semi-stables de discriminant une puissance m-ième*, J. Reine Angew. Math. 400 (1989) 173–184, DOI 10.1515/crll.1989.400.173 — **UNVERIFIED** (原文未读；arXiv/发表状态未核) | `MestreOesterleBound`：素导子时 `e_p ≤ 5`、`p > 37 ⇒ e_p ≤ 2`，例外 `p ∈ {11,17,19,37}`（按 §12.2；精确陈述/例外表 **UNVERIFIED**） | 文献；上游无 Lean；**UNVERIFIED** |
| L4 | Pasten | P2018 arXiv:1705.09251v4、P2026 arXiv:2609.17390v1（两条均 **UNVERIFIED**: arXiv 页面本环境不可达，版本/日期/发表状态未核） | `PastenAbcBound`：导出 `log rad(abc)` 与 `max(a,b,c)` 的显式条件界（工作形式待原文） | 文献；上游无 Lean；**UNVERIFIED** |
| L5 | Ribet–Takahashi（E7） | Ribet–Takahashi（1990? “Ribet–Takahashi theorem” 关于 optimal quotient 的 Néron 模型/新形式）；具体 DOI 待核 | `RibetTakahashiOptimalQuotient`：最优商与模 Jacobian 的 Néron 模型/新形式匹配 | 文献；上游无 Lean |
| L6 | deg 公式（E7） | 最优商模参数化次数公式（Ribet–Takahashi / 模曲线度数公式；文献待核） | `OptimalQuotientDegreeFormula`：`deg(π: J_0(N) → A) = …`（按水平/新形式 level 的公式，工作形式） | 文献；上游无 Lean |
| L7 | Petersson 渐近（E7） | Petersson 公式/渐近（Iwaniec, *Topics in Classical Automorphic Forms*；Petersson 1932） | `PeterssonAsymptotic`：Petersson 内积 `⟨f,f⟩` 的 `log`-渐近界；上游 Lean 已有 A9/A10 的积分表示可用作校准 | 文献 + A9/A10 上游 Lean |
| L8 | Néron 周期下界（E7） | Néron 周期理论（Néron 1965；Néron period lower bounds，文献待核） | `NeronPeriodLowerBound`：`∏_v |ω|_v` 的下界（工作形式：`log Ω_E ≥ -C_2`） | 文献；上游无 Lean |
| L9 | optimal quotient 存在性/最优性（E7） | Optimal quotient（Mazur/Ribet；Shimura 曲线版） | `OptimalQuotientExistence`：存在 `A` 为 `J_0(N)`（或 Shimura 曲线 Jacobian）的最优商且满足 Hecke 特征匹配 | 文献；上游无 Lean |

## 3. 上游端口队列（后台，不占主线优先级，mainline 用）

### 3.1 FLT271 `Patching/`（14 文件 = 7 顶层 + 7 Utils；import 闭包 19；最高价值 Taylor–Wiles 机制）

- 闭包：**19 个 FLT 模块**（14 Patching + `FLT/Deformations/Lemmas` + 4 个 `FLT/Mathlib` 回填）。
- 管道：`tools/port_flt_downgrade.mjs`；已跑：19 模块转换完成，编译 3 个后停止；首失败原因 **mathlib 模块源码缺失**（stage4 A868 纠正）：`Mathlib.Topology.Algebra.Group.Neighborhood` 在我们的 mathlib 905b958 中不存在（只有 `Mathlib/Topology/Neighborhoods.lean`，属 mathlib 56a0058/v4.35 时代），不是 olean 缺失，`lake build` 不能生成。
- 后台命令：先移植/改写该 Mathlib 模块，再：`node tools/port_flt_downgrade.mjs --src tmp/external/flt271 --dst tmp/external/ported/flt271 --prefix tmp.external.ported.flt271 --targets FLT.Patching --compile --json tmp/flt271_patching_report.json`
- 报告：`tmp/flt271_patching_report.json`；单文件日志 `tmp/flt271_port_*.log`。

### 3.2 anthro 定理闭包（按规模排序，依赖序文件已生成）

| 顺序 | 目标定理 | repo 文件 | 字节 | P2M/Definitions/Theorems | Mathlib 模块（源码+olean 均可用） | 拓扑序文件 |
|---|---|---|---|---|---|---|
| 1 | A5 `TaylorWiles.exists_isTaylorWilesPrime` | 47 | 147,576 | 22/4/21 | 26 | `tmp/port_order_taylorwiles.txt` |
| 2 | A8 `CuspForm.IsNewform.eq_of_forall_qCoeff_eq` | 165 | 1,195,987 | 71/24/70 | 48 | `tmp/port_order_isnewform.txt` |
| 3 | A7/A6 Shimura/Cerednik `galJ…` | 1,628 | 17,334,126 | 739/151/738 | 253 | `tmp/port_order_shimuraCerednik.txt` |
| 4 | A3 `RibetIrr.irreducible_of_point_of_not_dvd` | 4,934 | 63,060,545 | 2,308/319/2,307 | 574 | （按需生成） |
| 5 | A2 `atPNewLowering` | 12,752 | 187,890,169 | 6,100/553/6,099 | 721 | （按需生成） |
| 6 | A1 `FreyPackage.frey_isModular` | 55,981 | 1,065,917,062 | 27,290/1403/27,288 | 1,651 | （按需生成） |

- anthro Definitions 全量依赖图：`tmp/anthro_defs_graph/graph.json`（1450 节点、2620 内部边、DAG 无环）；拓扑序 `tmp/anthro_defs_graph/topo_order.txt`；Mathlib 导入集合 `mathlib_imports.txt`（513 个）。
- 闭包明细：`tmp/port_closures.json`；定理签名：`tmp/external_theorem_statements.json`。

### 3.3 其它外部源

- `leanprover-community/flt-regular` @ `83f477ccc8cef9fd9a022b90d87aed49368e7bbd`（v4.36.0-rc2，25 文件，Kummer/分圆正则情形）：需要 4.36→4.32 附加规则；低优先级。
- `anthropics/fermats-last-theorem` Definitions 全量：`tmp/external/flt-defs/Definitions`（1450 文件，0 sorry/axiom/opaque）——供 stepxi 按 `tmp/anthro_defs_graph/topo_order.txt` 批量排序（无需 port 编译，仅语句索引）。

## 4. 采用/状态汇总

- A 类 11 条：上游 Lean 精确语句已读；全部 0 sorry / 0 axiom（A11 为 14 文件框架切片）；**不移植、不编译，只作 class-B Prop 假设**。
- L 类 9 条：E7 六组件（L2 Faltings height bound、L3 Mestre–Oesterlé、L5 Ribet–Takahashi、L6 deg 公式、L7 Petersson 渐近、L8 Néron 周期下界、L9 optimal quotient）+ L1/L4；均文献，标注“待原文核对精确常数”。
- 合计 **20 条**（A1–A11、L1–L9）。

## 5. E7 组件（六条，专表）

每条均：**来源待核**（文献 DOI/精确常数待原文录入）、**我们采用形式**（class-B 输入 Prop，显式假设，不伪造 Lean 证明）、**状态**（未移植/未编译；上游 Lean 无对应条目）。

| ID | E7 组件 | 来源（待核） | 我们采用形式（class-B Prop） | 状态 |
|---|---|---|---|---|
| E7-1 | **Ribet–Takahashi** | Ribet–Takahashi（1990 年代，最优商/Néron 模型；DOI 待核） | `RibetTakahashiOptimalQuotient : Prop`（最优商与模 Jacobian 的 Néron 模型/新形式匹配） | 文献；上游无 Lean；待原文核对 |
| E7-2 | **deg 公式** | 最优商模参数化次数公式（Ribet–Takahashi/模曲线度数公式；待核） | `OptimalQuotientDegreeFormula : Prop`（`deg(π : J_0(N) → A)` 的显式公式） | 文献；上游无 Lean；待原文核对 |
| E7-3 | **Petersson 渐近** | Petersson 1932；Iwaniec, *Topics in Classical Automorphic Forms*（待核） | `PeterssonAsymptotic : Prop`（Petersson 内积的对数渐近界）；可用上游 A9/A10 积分表示校准 | 文献 + A9/A10 上游 Lean（0 sorry/0 axiom）；待原文核对 |
| E7-4 | **Néron 周期下界** | Néron 1965 周期理论及周期下界文献（待核） | `NeronPeriodLowerBound : Prop`（`∏_v ‖ω‖_v` 的下界，工作形式 `log Ω_E ≥ -C₂`） | 文献；上游无 Lean；待原文核对 |
| E7-5 | **Faltings 高度界** | Faltings 1983（Invent. Math. 73，DOI:10.1007/BF01388432）；Silverman AT Ch. XI | `FaltingsHeightBound : Prop`（`h_F(E) ≤ (1/2)log‖Δ_E‖ + C₁`；常数待核） | 文献；上游无 Lean；待原文核对 |
| E7-6 | **optimal quotient** | Mazur/Ribet 最优商理论（Shimura 曲线版；待核） | `OptimalQuotientExistence : Prop`（存在最优商且满足 Hecke 特征匹配） | 文献；上游无 Lean；待原文核对 |

**E7 条数 = 6**（E7-1…E7-6）。这些条目与 §2 的 L2/L5/L6/L7/L8/L9 一一对应；§2 的 L1（Faltings 高度存在性）与 L3（Mestre–Oesterlé）、L4（Pasten）为 E7 之外的 C 路线文献输入。

**消费者（链位置）**：E7-1/E7-6 → Ribet 水平下降/最优商步骤；E7-2 → 模参数化次数；E7-3 → 解析/Petersson 估计；E7-4 → 周期比较；E7-5 → 高度比较（Frey 曲线高度/判别式）；均作为 class-B 输入进入 C 链，当前记为 PENDING，不进入 `#print axioms` 计数（除非显式假设）。


## 6. L 类新增：Pasten 2018/2026 精确条目（A863）

来源：P2018 = Pasten, arXiv:1705.09251v4 (2018)；P2026 = Pasten, arXiv:2609.17390v1 (2026-09-15)。**UNVERIFIED**: arXiv 页面本环境不可达，版本/日期/发表状态均未 original-level 核验。
均为文献/外部定理，不移植、不编译、不伪造 Lean；class-B 输入 Prop 仅登记工作形式。

### L10 — P2018 Theorem 1.5（Ribet–Takahashi δ 比较）

精确陈述（原文 Cor 6.2；N=DM admissible）：
在下列任一条件下：
(i) N squarefree 且 M 不是素数；或
(ii) A 与 Frey–Hellegouarch 曲线同源，且 M 至少被两个奇素数整除，

    log( ∏_{p|D} v_p(Δ_A) ) = log δ_{1,N} - log δ_{D,M}
      + O( log D / log log D ),

其中 δ_{D,M} 由 q_{D,M} ∘ q_{D,M}^∨ = [δ_{D,M}] 定义，δ_{1,N}=deg(φ:X_0(N)→A)，
隐式常数绝对。

假设清单：E/Q 椭圆曲线；A 是 J_0(N) 的最优商（N=DM admissible）；f∈S_2(N)
Fourier 归一化、有理 Hecke 特征；D 为偶数个不同素数之积且 (D,M)=1；上述 (i)/(ii)。

我们可用形式（class-B Prop）：

    Pasten2018DeltaComparison : Prop
    -- 输入：admissible N=DM、optimal quotient A、newform f、条件 (i) 或 (ii)
    -- 输出：存在绝对常数 C_abs > 0，使
    --   | log(∏_{p|D} v_p(Δ_A)) - (log δ_{1,N} - log δ_{D,M}) |
    --     <= C_abs * log D / log log D

（需要真实类型 FreyHellegouarchCurve、OptimalQuotient、delta、vpDelta；
当前均 PENDING，不能直接编译成 Lean 定理。）

消费者：E7-2（deg 公式）/ E7-1（RT）/ E7-5（高度比较）；C 链的
δ_{1,N} 与 δ_{D,M} 比较步骤。该定理只给相对比较，不给 δ 的绝对上界。

### L11 — P2026 Theorem 1.1（Faltings height 的 admissible 分解界）

精确陈述：E/Q，N=DM admissible（gcd(D,M)=1、D squarefree、D 有偶数个素因子），
ℓ 素数且 ℓ∤N。则

    h(E) << M * φ(D) * log(ℓ),

隐式常数绝对、有效（不依赖 E,N,D,M,ℓ）。

假设清单：E/Q；N 为导子；N=DM 为 admissible factorization；ℓ∤N；h(E) 是
Faltings height（非 stable）；φ 为 Euler totient。

我们可用形式（class-B Prop）：

    Pasten2026FactorizedHeightBound : Prop
    -- ∃ C_abs > 0, ∀ E, ∀ N=DM admissible, ∀ prime ℓ ∤ N:
    --   h(E) <= C_abs * M * φ(D) * log ℓ

消费者：E7-5（Faltings 高度界）；C 链高度/判别式比较的上游输入。

### L12 — P2026 Corollary 1.2（所有 E/Q 的高度界）

精确陈述：对所有 E/Q，

    h(E) << N * log log N,

隐式常数绝对、有效。

class-B 形式：

    Pasten2026AllCurvesHeightBound : Prop
    -- ∃ C_abs > 0, ∀ E/Q: h(E) <= C_abs * N_E * log log N_E

消费者：E7-5；取代原先 GRH 条件下的估计（原文明确指出 unconditional）。

### L13 — P2026 Corollary 1.3（半稳定外曲线的高度界）

精确陈述：对固定有限素数集 S，所有在 S 外半稳定的 E/Q 满足

    h(E) <<_S N,

常数有效且只依赖 S。

class-B 形式：

    Pasten2026SemistableHeightBound : Prop
    -- ∀ finite S, ∃ C_S > 0, ∀ E/Q semistable outside S:
    --   h(E) <= C_S * N_E

消费者：E7-5；半稳定/Frey 曲线情形的 Szpiro 方向界。

### L14 — 高度到判别式（原文第 1 节）

原文引用 [8]：

    log Δ << max{1, h(E)},

Δ=|Δ_min(E)|。因此 L12 给出 log Δ << N log log N（所有 E/Q）；L13 给出
log Δ <<_S N（S 外半稳定）。

class-B 形式：

    FaltingsHeightControlsLogDelta : Prop
    -- ∃ C_abs > 0, ∀ E/Q:
    --   log |Δ_min(E)| <= C_abs * max 1 (h(E))

消费者：E7-5 → Szpiro6Shape 的判别式/高度桥。

## 7. 与 E7 目标（δ_{N,1} <= N^{2+ε}）的差距

E7 需要的形式（见 coord/ROUTE-C.md）：

    ∃C, log δ_{N,1} <= (2+ε) log N + C
    （等价于 δ_{N,1} <= N^{2+ε}，差常数）

再经 Frey 关系 log q = 2 log δ、log df = log N 得到

    log q <= (4+2ε) log N + 2C,  即 log Δ 约为 (4+2ε) log N + O(1).

这与 Szpiro6Shape（log q <= 6 log df + C'）只差常数；E7 的 core 是 δ 的
多项式上界。

Pasten 的实际结论与 E7 的差距：

| 来源 | 给出 | 与 E7 需要相比 |
|---|---|---|
| P2018 Thm 1.5 | log(∏ v_p(Δ_A)) = log δ_{1,N} − log δ_{D,M} + O(logD/loglogD) | 相对比较，无绝对 δ 上界；只能消去 δ_{D,M}，仍需 δ_{1,N} 或 δ_{D,M} 的独立界 |
| P2026 Thm 1.1 | h(E) << M φ(D) log ℓ | 取 D=1,M=N,ℓ固定时是 h(E) << N logN 型；E7 需要 h(E) << log N（因 logΔ 约 2logδ << logN），差 N logN vs logN |
| P2026 Cor 1.2 | h(E) << N log log N | 同上：N loglogN 远大于 logN；取对数后才 log h << log N，不是 h << logN |
| P2026 Cor 1.3 | h(E) <<_S N（S 外半稳定） | 仍是 N vs logN 的指数级差距 |

结论：P2018/P2026 是真实的 Szpiro 方向定理/框架，但没有给出 E7 所需的
δ 多项式上界；从 h(E) << N loglogN 到 h(E) << logN 不是简单常数优化，而是
本质强化（等价于接近 Szpiro）。因此 L10–L14 只能作为 class-B 输入/校准，
不能宣称 E7 已由 Pasten 解决。

状态：L10–L14 均为文献条目；无 Lean 源、无编译、无 sorry/axiom 新增；
精确常数编号 L10/L11 已按 P2018 Thm 1.5 / P2026 Thm 1.1 登记，L12/L13 为推论。
