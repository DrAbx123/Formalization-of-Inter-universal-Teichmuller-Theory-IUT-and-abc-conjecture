# N5-WEAK-PLAN — N5Weak 的可拼装 Lean 目标 (A1042)

| field | value |
|---|---|
| Status | PARTIAL (N5Weak 陈述/常数/对齐/条件主定理/paper 对应已给出；Lean 骨架为草案，未编译) |
| 前链 | `OUR-COR312-ROUTE.md`（N1–N4）、`N5-STATEMENT.md`（N5 = rhs ≥ −A ⇔ V+gap ≥ (sF−1)A） |

## 1. N5Weak(C) 的精确陈述

### 数学形式
```
N5Weak (C : Real) : Prop  :=  rhs + C >= -A
等价:                        (sF - 1) * A <= V + gap + C
其中 A = absLogQ, rhs = -R (signed), R = |log Theta|, V = logVol(hull vcI),
     gap = rhs + sF*A - V。
```
- 若 `C = 0` 即 N5（Cor 3.12 精确形式）；
- 允许 `C ≥ 0` 表示 paper Thm 1.10 的误差项（η_prm、d_mod、log d_F、log f_F 等）；
- **不需要 `hheight` 来陈述 N5Weak**；`hheight` 只在**证明** C 的候选值时需要（见 §2）。

### C 的具体候选（paper Thm 1.10 p.22-23）
```
C_paper := (1 + 20 * d_mod / l) * (log d_F + log f_F) + 20 * (e*_mod * l + eta_prm)
其中 d_mod = [F_mod : Q], e*_mod = 2^12*3^3*5*e_mod,
     eta_prm > 0 是 Prop 1.6 的正实数；
     d_F, f_F 是 F 的 discriminant/conductor 型量（Thm 1.10 最终不等式）。
```
若只保留 Step (v) 的 box，则 `C` 可取 `((l+5)/4)*logdf + C0` 中的常数项 `C0`（或
`paperBox l logd logf C0` 的 C0 部分）；与本链 N2 的 `paperBox` 一致。

### Lean 陈述（草案）
```lean
/-- N5 weak: the theta-hull lower bound up to an explicit error C. -/
def N5Weak (D : InitialThetaData) (C : Real) : Prop :=
  -D.qPilot.absLogQ - C <= (concreteVariantDataLit D).rhsData.rhs

/-- N5Weak with C given by the paper Thm 1.10 error terms. -/
def CPaper (l d_mod dF fF eStar eta : Real) : Real :=
  (1 + 20 * d_mod / l) * (Real.log dF + Real.log fF) + 20 * (eStar * l + eta)

/-- N5Weak with C = CPaper. -/
def N5WeakPaper (D : InitialThetaData) (l d_mod dF fF eStar eta : Real) : Prop :=
  N5Weak D (CPaper l d_mod dF fF eStar eta)
```

## 2. 与 S3016/S3017/S3034 的对齐

### `S3016CThetaUpperInterface`（S3016CThetaUpperActual）
```
structure S3016CThetaUpperInterface where
  stepVLogMagnitude : Real
  stepVLogMagnitude_eq : stepVLogMagnitude = S3016StepVQPilot a b c
  globalLogMagnitude : Real
  globalLogMagnitude_eq : globalLogMagnitude = S3016WeightedGlobalQPilot T
  identification : stepVLogMagnitude = globalLogMagnitude
  thetaSigned : Real
  cthetaPaper : Real
  upper : thetaSigned <= cthetaPaper * |stepVLogMagnitude|
theorem ...upper_bound : ...
```
- 给出的是 **upper bound**：`thetaSigned ≤ cthetaPaper * |stepVLogMagnitude|`；
- 若 `thetaSigned` 对应 `rhs`（或 `−|logΘ|`），这是 **上界**，方向与 N5Weak（需下界）**相反**；
- 若 `thetaSigned` 实际对应 `A − rhs`（deficit 方向），则 upper bound 可转成 `rhs ≥ A − C`，
  需要 `thetaSigned` 的精确定义（S3016StepVQPilot/S3016WeightedGlobalQPilot）与符号核对。
- **对齐结论：不能由 upper_bound 直接得 N5Weak；需先钉死 thetaSigned 的符号/方向（GAP-DIRECTION）。**

### `S3017_CTheta_upper_of_height`（S3017StepVUpperGapAssembly）
```
theorem S3017_CTheta_upper_of_height
    (n : Nat) (hn : 2 <= n)
    (hheight : forall a b c, IsABCTriple a b c ->
      Height.logHeight1 (abcJInvariant a b c) <=
        (1/n) * sum_{j in Icc 1 n} collectionBound (2n+1) S2921D (S2921Q a b c) (S2921S a b c) (S2921T a b c) j)
    (a b c : Nat) (habc : IsABCTriple a b c) :
    Height.logHeight1 (abcJInvariant a b c) <= S3015FinalBound n a b c
```
- 条件于 **`hheight`（height-to-procession input）**；输出 `logHeight₁ ≤ S3015FinalBound`；
- 这是 **C_Θ 型上界**，可用于给 N5Weak 的 `C` 提供 paper 常数（若方向对齐）；
- 因此：**若 `hheight` 成立且 thetaSigned 方向对齐，则可得 `N5Weak C` 的某个 C**（候选路径）。

### `S3034_hscalar_iff`
- 当前工作树 `tmp/sheaf/xif/paper/` 与 `tmp/` 中**未找到** `S3034_hscalar_iff`/`S3034` 的 Lean 文件
  （grep 仅命中无关的 `hscalar` 局部假设）；
- 若它存在于其它 lane/未落盘，则对齐方式应为：它是**标量恒等式**（`hscalar ↔ ...`），
  用它将 StepV unit 或 Q 系数重写为 `c·Q` 形式（与 S3050 的 `S3050QUnitIdentification` 配合）；
- **状态：文件缺失/未确认；登记为 GAP-S3034。**

## 3. 条件版主定理（先条件后填）

```lean
/-- Conditional Cor 3.12 variant from N1-N4 + N5Weak. -/
theorem our_cor312_variant_of_N1_N4_N5Weak
    (D : InitialThetaData)
    (l Dbox Q S T logd logf C0 : Real)
    (C : Real)
    (hN1 : paperLHS l Dbox Q S T <= paperRHS l Dbox Q S T)      -- N1 (green 可用)
    (hN2 : logVol D (hullOf D (vcI D)) <= paperBox l logd logf C0)  -- N2
    (hl7 : (∑ v, (1 - 1/l) * ...) <= DExactWithArch ...)       -- N3
    (hdeficit : (ssCoeff - cLana) * A + arch - torsion <= diff) -- N4 等价
    (hN5 : N5Weak D C)
    (hA : A = D.qPilot.absLogQ)
    : 0 <= D.qPilot.absLogQ - (concreteVariantDataLit D).rhsData.rhs := by
  -- N5Weak: -A - C <= rhs ⇒ A + rhs >= -C ⇒ M >= -C；C=0 时 M>=0
  sorry -- 条件版骨架（GAP：N5 的 C=0 部分 + 方向）
```
说明：`M = A − R = A + rhs`；N5Weak 给 `A + rhs ≥ −C`，即 `M ≥ −C`；
**要得 `M ≥ 0` 需 `C ≤ 0`**（即 N5 exactly），或把 C 吸收到最终不等式并改用误差版本：
```lean
theorem our_variant_error_form (D) (C : Real) (hC : 0 <= C) (hN5 : N5Weak D C) :
    -C <= D.qPilot.absLogQ - (concreteVariantDataLit D).rhsData.rhs := by
  linarith [hN5]
```
即 paper-faithful 的输出应是 **带误差 C 的 variant**（与 Thm 1.10 的 η 项一致），
而不是精确 `M ≥ 0`；精确版需 N5（C=0）。

## 4. N5Weak 中属于 paper Step (xi-d) 原文的内容

对照 `coord/IUT-TEXT-LONG.md` / `IUT-TEXT-COR312.md`：
1. **Step (x) p.181**：log-volumes 对 Ind1/Ind2 不变，Ind3 转为 **from above 的不等式**；
   ⇒ 我们 N5 的 **上界侧**（box/C_Θ），对应 `S3017`/`S3016` 的上界；
2. **Step (xi-a) p.181**：q-pilot (1,0) ↔ Θ-pilot (0,0) via Θ×μ_LGP-link；
   ⇒ q-pilot 区域 `Q` 与 Θ-pilot 区域的对应（我们缺 `Q ⊆ hull` 的构造）；
3. **Step (xi-c) p.182**：multiradial algorithm 输出 `1,◦U` 与 q-pilot representation 在 `1,◦UQ`；
4. **Step (xi-d) pp.182-183**：determinant 的 normalized log-volume 比较，构造
   `R_{≤−|log(Θ)|} ⊆ R` 与 `−|log(q)| ∈ R` ⇒ 最终 `−|log(Θ)| ≥ −|log(q)|`；
   ⇒ **N5Weak 的下界侧（C=0 时）完全来自 Step (xi-d)**；这是 lana/我们构造栈中缺失的部分；
5. **Thm 1.10 Step (v) pp.27-29**：给出的是 **上界**（box/C_Θ），不是下界；
6. **Cor 3.12 p.173**：结论不等式；其证明的下界由 Step (xi-d) 提供。

结论：N5Weak 的 **上界/常数 C** 可由 S3016/S3017 路径（+hheight）提供；
N5Weak 的 **精确下界（C=0）** 需要 Step (xi-d) 的 determinant 比较（完全缺失）。

## 5. Lean 骨架草案（文件级，未编译）

```lean
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.N5WeakPlan

def N5Weak (A rhs C : Real) : Prop := -A - C <= rhs
def M (A rhs : Real) : Real := A + rhs

theorem M_ge_negC_of_N5Weak {A rhs C : Real} (h : N5Weak A rhs C) : -C <= M A rhs := by
  unfold N5Weak M at *
  linarith

theorem variant_of_N5Weak_zero {A rhs : Real} (h : N5Weak A rhs 0) : 0 <= M A rhs := by
  have := M_ge_negC_of_N5Weak h
  simpa using this

/-- N5Weak with paper C. -/
def N5WeakPaper (A rhs l d_mod dF fF eStar eta : Real) : Prop :=
  N5Weak A rhs ((1 + 20 * d_mod / l) * (Real.log dF + Real.log fF) + 20 * (eStar * l + eta))

end LeanFormal.IUT.XiFPaper.N5WeakPlan
```
（真实文件需接 `InitialThetaData`/`concreteVariantDataLit`/`rhsData.rhs`；本骨架只记录
`N5Weak ⇒ M ≥ −C` 的纯算术核心。）

## 6. 结论

1. **N5Weak(C)**：`rhs + C ≥ −A`；`C=0` 即 N5/Cor 3.12；`C>0` 是 paper 误差版本；
2. **不需要 hheight 来陈述**；hheight 只用于从 S3017 得到 C 的 paper 值；
3. **S3016/S3017 给上界（方向相反）**：不能直接得 N5Weak，需先钉死 `thetaSigned` 的方向
   （GAP-DIRECTION）；若方向对齐 + hheight 成立，可得 N5Weak 的 C 候选；
4. `S3034_hscalar_iff` 在工作树中未找到（GAP-S3034）；
5. 条件主定理：`our_cor312_variant_of_N1_N4_N5Weak` 只能给 `M ≥ −C`（误差版）；
   精确 `M ≥ 0` 需 N5（C=0），其下界来自 paper Step (xi-d) determinant 比较——完全缺失；
6. 建议：先形式化 `N5Weak ⇒ M ≥ −C` 的算术骨架（可直接写），再决定是否攻 Step (xi-d)。