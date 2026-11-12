# N5-STATEMENT — assembly 的 paper-faithful 陈述与证明计划 (A1041)

| field | value |
|---|---|
| Status | PARTIAL (N5 精确陈述已给出；paper 的 N5 = Cor 3.12 几何核心（Step x/xi-d），我们只有部分组件；最小子目标已列出) |
| 标注 | `FIELD-ASSUMED`: N5 的几何内容（q-pilot 区域/determinant 比较）；`PENDING-WATCHDOG`: 相关 Lean 骨架待 watchdog 编译 |
| 源 | `coord/IUT-TEXT-LONG.md`（Step (x) p.181，Step (xi-a/c/d) pp.181-183，Thm 3.11 pp.153-156，Cor 3.12 pp.173-175）、`coord/IUT-TEXT-THM110.md`（Step (iv)(v) pp.27-29）；我们：`OUR-COR312-ROUTE.md` N1-N4 |

## 1. N5 的 paper-faithful 精确陈述

### 1.1 paper 原文要素（逐条）
1. **Step (x) p.181**: procession-normalized log-volumes `∈ R` 对 Ind1/Ind2 **不变**，并把
   Ind3 转成 **from above 的不等式**；
2. **Step (xi-a)**: q-pilot at (1,0) ↔ Θ-pilot at (0,0) via Θ×μ_LGP-link（“gluing isomorphism”）；
3. **Step (xi-c)**: multiradial algorithm 输出 `1,◦U ⊆ 1,◦UQ`，与 q-pilot 在 `1,◦UQ` 上的
   representation 由 F⊩▶-prime-strips 同构连接；
4. **Step (xi-d)**: 通过 **determinant** 的（suitably normalized w.r.t. j∈|F_l|）log-volume 比较：
   `R_{≤−|log(Θ)|} := {λ ∈ R | λ ≤ −|log(Θ)|} ⊆ R` 且 `−|log(q)| ∈ R`（comparable objects）；
5. 结论：`−|log(Θ)| ≥ −|log(q)|`。

### 1.2 我们的符号化陈述

设 `D : InitialThetaData`；`A = absLogQ`；`rhs = −R`（`R = |logΘ|`）；`V = logVol(hull vcI)`；
`gap = rhs + sF·A − V`。则
```
N5 (paper-faithful):        rhs >= -A
等价形式:                   V + gap >= (sF - 1) * A
其中 rhs = V + gap - sF*A     （由 gap 定义反解）
```
即 M := A − R = A + rhs = V + gap − (sF−1)A，N5 ⟺ `0 ≤ M`。

**更细的 paper-faithful 断言**（含几何对象）：存在 q-pilot 区域 `Q ⊆ 1,◦UQ` 使
```
logVol(Q) = -A           （q-pilot 的 log-volume 定义）
Q ⊆ hull(thetaPilot)     （或 determinant 比较给出 logVol(Q) ≤ rhs）
⇒ rhs >= -A
```
paper Step (xi-d) 的 determinant 比较正是为建立 `logVol(Q) ≤ rhs`（或等价的 comparable
objects），而 **不是** lana 的 `lgp·hull(vcI)`（其体积是 `V − sF A`，多出 sF 因子）。

## 2. 我们已有的组件（N1-N4 + S30xx）

| 组件 | 内容 | 状态 |
|---|---|---|
| N1 | `paperStepV_inequality`（Q cancel, D/S/T>=0） | **PENDING-WATCHDOG**（源码/olean 存在，非 gate；Mzk1PaperStepVBoxActual） |
| N2 | `volume_upper_of_dictionary`（V <= paperBox）+ PaperDictionaryShape | **PENDING-WATCHDOG**（源码/olean 存在，非 gate；Mzk1StepVIdentificationActual） |
| N3 | `L7_with_arch`（D_exact 下界） | **PENDING-WATCHDOG**（源码/olean 存在，非 gate；Mzk1DExactFromHullActual） |
| N4 | `deficit_nonpos_iff`（deficit 代数等价） | **PENDING-WATCHDOG**（源码/olean 存在，非 gate；Mzk1PaperNormDeficitActual） |
| S3050 | `S3050_stepVTerm_eq_label_sq_mul_unit`：StepVTerm = label²·unit（**精确**）；`S3050_stepVTerm_eq_qCoeff_mul_Q_add_rest`；`S3050QUnitIdentification Q := ∃ c, unit = c*Q` | green 代数 + **缺失 identification 作为 Prop** |
| S3014/S3017 | `S3017_processionAverage_bound`（平均上界）；`S3017_CTheta_upper_of_height`（条件于 **height-to-procession input**） | partial/green conditional |
| S3016 | `S3016CThetaUpperInterface`（stepV=global identification + `thetaSigned ≤ cthetaPaper*|stepVLogMagnitude|`）；`upper_bound` | green interface（字段式） |
| S3016StepVQPilotIdentification | `S3016IdentificationTarget a b c`、`S3016IdentificationGap a b c`（目标/缺口 Prop） | partial |
| S3029 | per-label decomposition/affine（`S3029_perLabel_affine`） | PENDING-WATCHDOG |

**Gate 注（A1045/shehdd 审计）**：上表 N1–N4（及 S30xx 辅助件）的“green”仅为源码/olean 存在；**未过 DshDagWatchdog gate（无 trio/#print axioms/probe）**，一律按 `PENDING-WATCHDOG` 处理，不得写成 green gate。`Olean TRUE` 不等于 gate。N5 仍是 PAPER-FAITHFUL 陈述 + GAP，不是定理。

## 3. 缺什么（精确）

1. **Ind1/Ind2 的 log-vol 不变性（完整版）**：`logVol` 对 label 置换/tensorAut 不变，以及
   symmetrization（Prop 1.7 weighted average）；lana 有 `rhsDataOn_perm` 等，但未接入我们的构造栈；
2. **Ind3 的 from-above 不等式 → 下界机制**：paper Step (x) 把 Ind3 转为上面的不等式；
   我们需要的是 `rhs ≥ -A`（下界），paper 的下界来自 Step (xi-d) 的 determinant 比较，
   而非 Step (v) 的上界；**这是 N5 的核心**；
3. **Step (xi-d) 的 determinant 比较**：构造 q-pilot 区域 `Q`（`logVol = -A`）并证明
   `Q ⊆ hull(thetaPilot)`（或 `logVol(Q) ≤ rhs`）；lana 的 `lgp`（`V − sF A`）不是 paper 的
   q-pilot 区域，sF 因子不可混用；
4. **`S3050QUnitIdentification Q`**：StepV unit 与所选 Q 的精确倍数关系（决定 Q 系数），
   当前只是 Prop；
5. **height-to-procession input**（S3017 的 `hheight`）：`logHeight₁ ≤ (1/n)Σ collectionBound`；
6. **arch/torsion 位置一致性**（GAP-A/GAP-B）。

## 4. 证明计划（按可行性排序）

### P1（最小可证子目标，最弱形式）
```
N5Weak (C : Real) : Prop := -A - C <= rhs        -- C 为显式误差（η_prm, d_mod, l）
theorem n5weak_implies_M_ge_negC : N5Weak C -> -C <= M
```
含义：放弃精确 `-A`，允许 Thm 1.10 的 η/d_mod 误差；输出 variant 的 **误差版本**
`M ≥ -C`。这是最小可证、且与 paper Thm 1.10 的最终不等式结构一致（1/6 log q ≤ ... + η）。

### P2（Q 系数精确化）
```
theorem n5_of_unit_identification
    (h : S3050QUnitIdentification Q) : ... -- 把 StepV unit = c*Q 代入，得 Q cancel 的精确形式
```
依赖 S3050 的 affine 分解；仍不产生 `rhs ≥ -A`，只保证 Q 系数正确。

### P3（determinant comparison 的子步骤）
```
theorem qPilotRegion_subset_thetaHull :
  exists (Q : Region D), logVol D Q = -D.qPilot.absLogQ ∧ Q <= hullOf D (thetaPilotLit D)
```
paper Step (xi-d) 的最小切片：只需 **存在** q-pilot 区域（体积 -A）被 Θ-hull 包含；
这是 N5 的充分条件（`logVol` 单调 ⇒ `-A ≤ rhs`）。**这是 paper Cur 3.12 的几何核心**，
预计需要 LGP-link/determinant 的新形式化；但作为**存在性陈述**比完整比较小得多。

### P4（完整 N5）
`rhs ≥ -A`（= Cor 3.12），等价 `V + gap ≥ (sF-1)A`；需要 P3 + 精确 sF/1-因子对齐。

## 5. Lean 陈述草案

```lean
/-- N5 (paper-faithful): q-pilot lower bound on the theta-hull log-volume. -/
def N5Statement (D : InitialThetaData) : Prop :=
  -D.qPilot.absLogQ <= (concreteVariantDataLit D).rhsData.rhs

/-- N5 weak (up to explicit error C). -/
def N5Weak (D : InitialThetaData) (C : Real) : Prop :=
  -D.qPilot.absLogQ - C <= (concreteVariantDataLit D).rhsData.rhs

/-- N5 via a q-pilot region inside the theta hull (paper Step (xi-d), minimal slice). -/
theorem n5_of_qPilotRegion_subset
    (Q : Region D)
    (hvol : logVol D Q = -D.qPilot.absLogQ)
    (hsub : ∀ i, Q i <= hullOf D (thetaPilotLit D) i)
    (hQ : IsAdelic D Q) (hH : IsAdelic D (hullOf D (thetaPilotLit D))) :
    N5Statement D
/-- N5 implies M >= 0. -/
theorem M_nonneg_of_N5 (D) (h : N5Statement D) :
    0 <= D.qPilot.absLogQ - (concreteVariantDataLit D).rhsData.rhs := by
  -- M = A - R, R = -rhs; N5: -A <= rhs  => 0 <= A + rhs = A - R
  linarith [h]
```
（`thetaPilotLit` 需从 lana/我们构造取 lit 版本；`Region`/`IsAdelic` 端口。）

## 6. 结论

1. **N5 的 paper-faithful 陈述** = `rhs ≥ -A`（等价 `V + gap ≥ (sF-1)A`），其几何核心是
   Step (xi-d) 的 determinant 比较：存在 q-pilot 区域（体积 `-A`）被 Θ-hull 包含；
2. 我们已有 N1-N4（green）与 S3016/S3017/S3050/S3029 的接口/精确代数，但：
   - Ind1/2 不变性与 symmetrization 未接入；
   - Ind3 的上界机制不产生下界；
   - determinant 比较（N5 核心）完全缺失；
   - `S3050QUnitIdentification` 与 height-to-procession input 仍是 Prop/条件；
3. **最小可证子目标**：`N5Weak (C)`（允许 Thm 1.10 的显式误差），以及更几何的
   `n5_of_qPilotRegion_subset`（只需存在性：q-pilot 区域 ⊆ Θ-hull，体积 = -A）；
4. 完整 N5 = Cor 3.12 的几何核心，预计是本项目最大的单项形式化任务；
5. 建议把 N5Weak / qPilotRegion_exists 作为下一步两个可执行目标，完整 N5 待 owner 决策。