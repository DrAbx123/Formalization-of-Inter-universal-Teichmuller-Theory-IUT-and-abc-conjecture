# A3 / F2.1：AG donor 直接接线图（不重造）
（grace，2026-11-17 21:45 CST；替换早前的假设映射表；含排期）

## 0. 结论
AG 层（scheme 级 proper/smooth/relative-dim/几何连通 + 函数域/除子/Serre/RR 定义层）**已全部 olean 在位**；F2.1 的工作 = 在 `fermatCurveScheme n` 上把这些接口**实例化/接线**，不重造数学。

## 1. scheme 级（本 lane 已有件，DONE）
| 需要 | exact 名 | 状态 |
|---|---|---|
| proper | `Mzk1G1FermatPiProperActual.fermatCurveToSpec_isProper_final` | DONE 17:19:19 |
| smooth rel dim 1 | `Mzk1G1FermatCurveSmoothFinalActual.fermatCurveToSpec_smoothOfRelativeDimension` | DONE 17:40:31 |
| 几何连通（k̄ 连通+非空） | `Mzk1G1FermatKbarConnectedActual.kbar_connected` / `kbar_nonempty` | DONE 21:42:57 |
| 整性（ℚ 上） | `Mzk1G1A3CurveIntegralActual.curve_isIntegral` | DONE 11:49:19 |
| 两 chart 截面/函数域 | `Mzk1G1A3ChartSectionsActual` / `Mzk1G1A3ChartInfSectionsActual` / `Mzk1G1A3FunctionFieldFinalActual` / `Mzk1G1A3FunctionFieldInfActual` | DONE 11:31/13:13/12:09/13:19 |

## 2. AG 抽象层（olexan 在位，直接 import + 引用）
| 模块 | 关键 exact 名（probe 已核） |
|---|---|
| `AG01CurveFoundationsActual` | `S3133CurveOver k`（proper/smooth/geomConnected/relativeDimOne 打包） |
| `AG02FunctionFieldActual` | `agFunctionField_isFractionRing_of_isAffineOpen`（本 lane 已用于 F2.3） |
| `AG02bPrincipalDivisorActual` | 主除子/degree 0 相关（`Divisor.mem_principal`、`Divisor.degree_*`） |
| `AG02GenusActual` | `ell`/`indexOfSpecialty`/genus 层 |
| `AG04bResidueFieldActual` | `agResidueClass`、`agSectionResidue`（闭点 residue/evaluation） |
| `AG11SerrePairingConsumerActual` | `ag11ResidueTheorem`（ResidueTheorem 的 consumer 形式） |
| `AG_FLT_PromotionActual` + `AG_FLT_Def/Thm_*` | Divisor / AdelicIndex（`residuePairing`）/ Repartitions / CanonicalDivisor |
| 定义层（`flt_core`） | `mem_lSpace_iff`、`mem_lSpace_iff_ord`、`ell_zero_eq_one_of_constantsAreBase`、`finrank_adeleBdd_inf_global_eq_ell`、`Divisor.degree_single/smul` 等（`_AGProofCompletenessProbe.lean` ~80 名） |

## 3. 接线步骤与 owner（依赖顺序）
| # | 步骤 | 用到的 donor | owner | 估时 |
|---|---|---|---|---|
| 1 | 函数域与点：`F := ↥(fermatCurveScheme n).functionField`、`K := ℚ`，构造 `AlgebraicCurve.IsCurveOver ℚ F`、places↔闭点（ord 映射 + properness 延拓 + separatedness 唯一） | `AG01.S3133CurveOver`、`AG02FunctionFieldActual`、`AG04bResidueFieldActual`、`mem_lSpace_iff_ord` | **henry**（route item 1） | 2–3 批 |
| 2 | `HasCanonicalDivisor ℚ F`：由 A4 的 ω₀（`Mzk1G1OmegaActual.omegaForm/dX/dY`，Ω 自由秩 1：`Mzk1G1OmegaFreeActual.phiEquiv/omegaEquivO`）给 canonical 除子（ω₀ 的零/极点除子），与 AG 层 canonical 定义对齐 | item 1 + `OmegaFree`/`OmegaBasis`/`AG_FLT_Def_AlgebraicCurve_CanonicalDivisor` | **grace** | 1–2 批（依赖 item 1） |
| 3 | `∀ v, v.DCoordGenerates`：每 DVR 取 uniformizer u，Ω 局部由 du 生成（用 `mem_lSpace_iff_ord`/`Place.adicValuation_*` + OmegaFree 的局部化） | item 1、2 + `OmegaFree`/`ChartDiff` | **grace** | 1–2 批（依赖 item 1） |
| 4 | `HasCanonicalLocalResidueKStar`（residue 数据：等特征零 Laurent 展开 + residue-field trace） | AG04b、AG_FLT_Def_AlgebraicCurve_LocalResidue | henry（route item 3） | 2–3 批 |
| 5 | `ResidueTheorem ℚ F`（全局 residue 和 0：沿 π trace 到 ℚ(λ) + ℙ¹ partial fractions） | AG11、LocalResidue 数据（item 4） | henry（route item 4） | 2–3 批 |
| 6 | `ConstantsAreBase ℚ F` + `HasPrincipalDivisors ℚ F` | AG02b、AG01 | henry（route item 5） | 1–2 批 |
| 7 | Čech↔真实截面 + `RiemannGenusReachedAt`（plane model 0→O(m−n)→O(m)→i_*O_Y(m)，m≥n−2 时 H¹=0 的 Laurent 单项式计算 + Hilbert 函数差） | AG_FLT_Def_AlgebraicCurve_CechSectionsOfDivisor、AG_FLT_PromotionActual | andrew（route item 6,7） | 3–4 批 |
| 8 | F2.1 evaluation：`H¹(O(D−x))=0`（由 item 5+7 的 `cechRiemannRoch_of_genusReached` 或 Serre 对偶）+ 短正合列 ⇒ 每闭点 eval 非零 ⇒ `A3EvalData.hne` | `Mzk1G1A3EvalDataActual`、`exists_forall_apply_ne_zero` | grace（数据侧已 DONE；生产依赖 1–7） | 1 批（接线） |

## 4. `A3EvalData.hne` 的逐项依赖 → owner
- `H⁰`/`H¹`/`lSpaceOn`/`ell`（定义层）→ **已 DONE**（AG_FLT_Def_AlgebraicCurve_CechSectionsOfDivisor），grace 直接用；
- `Serre pairing bijectivity` → henry（item 5：`ResidueTheorem` + `WeilDuality` promotion）；
- `ConstantsAreBase` → henry（item 6）；
- `ResidueTheorem` → henry（item 5）；
- `RiemannGenusReachedAt`（Čech RR）→ andrew（item 7）；
- `hasCanonicalDivisor`/`DCoordGenerates` → **grace**（items 2,3，依赖 item 1）；
- item 1（`IsCurveOver`/places 接线）→ henry（阻塞 2,3）。

## 5. translation trick 复核（保持结论：不可行）
`H¹` 线性等价不变、次数不变；平移只能到除子 0 版（`serrePairing` 只对 0 定义，`H¹(O(0))=g≠0`）。消失必须来自 `deg(D−x) > 2g−2` 的负次数 `H⁰(K−D+x)=0` 或 `cechRiemannRoch_of_genusReached` 的 `D₀≤D⇒Subsingleton (cechH1 D)`（item 7）。
## 6. 里程碑更新（21:50）
- **DONE**：`Mzk1G1A3EvalDataActual` 13:27:20（三公理）：`structure A3EvalData` + `A3EvalData.exists_avoiding`（数据侧闭合）。
- **DONE**：`Mzk1G1A3ChartDiffCriterionActual` 13:28:48（三公理，5 条）：`mem_smul_top_iff`、`mem_smul_top_iff_Psi`、`chartY_notMem_of_chartX_sub`（x−t∈p, t^n≠1 ⇒ y∉p）、`aeval_notMem_of_value`（g(t)≠0 ⇒ g(x)∉p）、**`D_psiChart0Coord_not_mem_smul`**（p 素、x−t∈p、t^n≠1、g′(t)≠0、2≤n ⇒ `D psiChart0Coord ∉ pΩ`）——受限诊断件（NOT route B2）。
- **`HasCanonicalDivisor` 抽象版可行性复核（item2）**：类定义 `class HasCanonicalDivisor : Prop where exists_divisor : ∀ ω ≠ 0, ∃ D : Place →₀ ℤ, ∀ v, D v = v.ordDifferential ω`；`ordDifferential ω := v.ord (v.differentialCoeff ω)`（`Def_ModularCurve_CanonicalDivisor:85`，需 `DCoordGenerates`）。**树内无任何 producer**（grep 仅 class/使用）；抽象构造需要：
  (i) Ω[F⁄ℚ] 为 F-秩 1（`Module.finrank`/`Nontrivial Ω`；在函数域层需先有 F/ℚ trdeg 1）；
  (ii) 对固定 ω≠0，`v ↦ ordDifferential ω v` 的**有限支撑**——这是实质数学（只有限多 places 上系数非单位），route §4.2 step 2（uniformizer/Ω 局部自由 + 全局微分延拓）才能给；
  ⇒ **item2 不能抽象先行**，依赖 item1（F/places 接线）+ item3 的局部化机器；已在排期表标注。
- item3 `DCoordGenerates` 同样依赖 item1（`v.differentialCoeff` 的存在性即其定义所需）。
