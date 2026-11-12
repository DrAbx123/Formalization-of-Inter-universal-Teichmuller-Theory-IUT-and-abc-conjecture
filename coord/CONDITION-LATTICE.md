# CONDITION-LATTICE — 目标拆成可满足、且与目标不等价的条件 DAG (A1047)

| field | value |
|---|---|
| Status | PARTIAL (条件 DAG 已列；每条件给 Lean 陈述/数据/强弱/可满足性；最优拆法给出；不编译) |
| 目标 G | `M = A - R = V + gap - (sF-1)*A >= 0` ⇔ `V + gap >= (sF-1)*A`（我们的较弱 variant） |
| 纪律 | 禁止把 G 或其等价形式（尤其 `N5Weak(0)`、`gap >= (sF-1)A - V` 精确式）当作“条件”；所有条件必须**严格弱于**或**独立于** G；循环性检查见 §6 |

## 0. 记号与目标分解骨架

```
G  : V + gap >= (sF - 1) * A
A  = absLogQ = logQ/(2l)          (q-pilot, 无 1/nC)
V  = logVol(hull(vcI))            (q-无关)
gap = rhs + sF*A - V              (>=0 by source)
R  = -rhs = |log Theta|
M  = A - R = A + rhs = V + gap - (sF-1)*A
sF = sFactor nC = l(l+1)/12, nC = (l-1)/2
```

DAG 顶层：`G <- (group-by-place A) ∪ (group-by-m B) ∪ (item C) ∪ (data D) ∪ (error E)`。
每组条件单独**不蕴含** G，只组合后可推出 G（见 §4）。

## 1. Group A：按 place / 坏素数 / 任意分组

### A1 逐位条件（per finite place）
```lean
def PerPlace (T H arch torsion : Place -> Real) : Prop :=
  forall v, T v <= H v
```
- 关系：`(forall v, PerPlace) ⇒ G`（在 arch>=0、torsion=0、sum 换序假设下）；
- **严格强于 G**（G 允许部分位为负，只要总和够）；非等价；
- 所需数据：`T_v = (sF-1)*weight_v*ord_v(q_v)*logp_v/(2l)`，`H_v = hullPacket`；
- 可满足性：逐位 tame 有 green 公式；ramified 位 H_v 可负（A1010）⇒ **OPEN**。

### A2 按坏素数分组（per prime）
```lean
def PerPrime (T H buffer : Nat -> Real) : Prop :=
  forall p, (sum_{v|p} T v) <= (sum_{v|p} H v) + buffer p
```
- 关系：`PerPrime + buffer 总和 <= arch 等 ⇒ G`（分组求和）；严格弱于 A1、强于 G（固定 buffer 时非等价）；
- 数据：坏素数有限集、`weight` 归一（`sum weight = 1`）、`buffer_p = (1-1/e_p)log p`；
- 可满足性：tame 展开（VcI:844）green-by-source；wild 位 buffer 重复计数问题（A991 C2）⇒ **OPEN**。

### A3 任意分组（finite partition）
```lean
def Grouped (part : Finset (Finset Place)) (hpart : ...) (T H : Place -> Real) : Prop :=
  forall S in part, (sum_{v in S} T v) <= (sum_{v in S} H v) + slack S
```
- 关系：任意分组的逐块条件 + `sum slack <= arch - torsion` ⇒ G；
- 用途：把最小可行块（qpilot 的 admissible cells）按块聚合；
- 可满足性：由 A1/A2 覆盖；独立分组可逐块验证（qpilot 2604 cells = 数值证据，非证明）。

## 2. Group B：按 m = qOrder 阈值分段

### B1 有限段（m <= B）
```lean
def BoundedQ (B : Nat) : Prop :=
  forall (D : InitialThetaData), (forall w hw, D.qOrder w hw <= B) -> (V + gap >= (sF-1)*A)
```
- 关系：**严格弱于 G**（只覆盖有界 qOrder）；不是等价；
- 可满足性：有限段数值 2604/21027 全过（qpilot），但**未形式化**；
- 所需：qOrder 的界 B、逐 D 的枚举/估计（当前无）。

### B2 渐近段（m > B）
```lean
def AsymptoticGap (B : Nat) : Prop :=
  forall (D), (exists w hw, B < D.qOrder w hw) -> (V + gap >= (sF-1)*A)
```
- 关系：与 B1 互补；`(forall B, BoundedQ B) ⇒ G`（非单 B）；每个 `BoundedQ B` 严格弱于 G；
- 可满足性：literal 读法 gap=sF*A（A1029）⇒ 渐近段可证；iv 读法不稳定（A1027/A1030）⇒ **OPEN/ROUTE-DEP**；
- 关键：B2 在 **lit 读法**下可满足（gap=sF*A, V>=0 ⇒ G）；在 iv 下需要 Step (xi-d)（N5）。

### B3 分段误差版
```lean
def SegmentedError (B : Nat) (C : Real) : Prop :=
  forall D, (V + gap + C >= (sF-1)*A)   -- N5Weak(C) 的全局形式，不限于 m>B
```
- 注意：`SegmentedError 0` = G（等价，**禁止当条件**）；`C>0` 严格弱于 G；
- 可满足性：无证明；是误差版目标（paper Thm 1.10 的 η 项）。

## 3. Group C：按项拆（独立可满足项）

| 条件 | Lean 陈述 | 与 G 关系 | 可满足性 |
|---|---|---|---|
| C1 VNONNEG | `0 <= V` | 独立；与 gap>=... 合取可推 G（非等价） | GAP-VNONNEG（logShellRadius>=0 端口） |
| C2 GAPNN | `0 <= gap` | 独立；green-by-source（Gap:514 `gap_nonneg`） | **可满足（源级）** |
| C3 GAPLOW g0 | `g0 <= gap` | 独立；与 `V + g0 >= (sF-1)A` 合取 ⇒ G | 若 g0 小（与 tame 同阶）可证？**OPEN** |
| C4 N5Weak C>0 | `-A - C <= rhs` | **严格弱于 G**（G ⇒ C4 for C>=0），C=0 时等价（禁用） | FIELD-ASSUMED；GAP-N5 |
| C5 HSCALAR | `exists c, S3050Unit = c * Q`（S3050QUnitIdentification） | 独立（Q 系数识别） | OPEN（S3050 已把它作为 Prop） |
| C6 CTHETA | `thetaSigned <= cthetaPaper * abs(stepVLogMagnitude)` | 独立（上界）；方向与 G 相反（GAP-DIRECTION） | **可满足（S3016 interface 字段）** |
| C7 IND2NN | `0 <= ind2Term i p c` | 独立；green-by-source（Gap:756） | **可满足（源级）** |
| C8 IND2BOUND K | `abs(ind2Term) <= K` | 独立（有界）；A1022 frac 版 | 条件（需 rounding 引理） |
| C9 ARCHNN | `0 <= arch` | 独立；常数 | **可满足**（若 arch=log(sqrt2*pi)） |
| C10 TORSION | `torsion >= 0` (或 r/n ∈ [0,1]) | 独立 | green 算术（Mzk1RDefinitionAudit） |

注意：**C4 的 C=0 版本（N5Weak 0，即 −A ≤ rhs）与 G 等价，禁止作条件**；C4 只取 C>0。

## 4. Group D：数据层（实例化条件）

| 条件 | Lean 陈述 | 与 G 关系 | 可满足性 |
|---|---|---|---|
| D1 L-CARRIER | `Nonempty (SourcePilotRegionLGeneric I)` | 数据层；独立（logical） | class-B 假设（A966） |
| D2 N1 | `paperLHS <= paperRHS` | 与 G 独立；代数 Step V | **green（Mzk1PaperStepVBoxActual）** |
| D3 N2 | `V <= paperBox l logd logf C0` | 独立（上界） | green 条件（StepVDictionary 3 fields） |
| D4 N3 | `sum (1-1/l) logp <= DExactWithArch` | 独立（下界） | **green（L7_with_arch）** |
| D5 N4 | `deficit <= 0 <-> (ssCoeff-cLana)*A + arch - torsion <= diff` | 代数等价（不是条件） | **green（deficit_nonpos_iff）** |
| D6 S14xx | S3014ProcessionData fields | 数据层 | green-by-source/条件 |
| D7 S1487 | `S1487FaithfulInput`/`S1487FaithfulC3` | 具体数据 | **green（S1487 文件 olean）** |

## 5. Group E：paper 误差常数拆（C_paper）

```lean
def CPaper (l d_mod dF fF eStar eta : Real) : Real :=
  (1 + 20*d_mod/l)*(Real.log dF + Real.log fF) + 20*(eStar*l + eta)
def ErrorVariant (C : Real) : Prop := forall D, -C <= M D
```
- 关系：`ErrorVariant C` 对 `C>0` **严格弱于 G**；`C=0` 等价（禁用）；
- 可满足性：paper Thm 1.10 的最终不等式结构；我们只有 CTheta 上界（方向需核）；
- 用途：把精确 G 拆成 `{C1..C10}` 的合取 + 误差项 C，得到**可满足的误差版**；
- 最优组合：`{C1 V>=0, C2 gap>=0, C4 N5Weak C, C9 arch>=0, C10 torsion>=0}` ⇒ `M >= -C`；
  该组合各条件均**不等价**于 G（C4 取 C>0）。

## 6. 最优拆法与循环性

### 6.1 已可满足条件（green/源级）
```
N1（paperStepV_inequality, green）
N3（L7_with_arch, green）
N4（deficit_nonpos_iff, green 等价，只作代数工具）
C2（gap_nonneg, 源级）
C7（ind2Term_nonneg, 源级）
C9（arch>=0, 常数）
C10（torsion>=0, green 算术）
D7（S1487 具体数据, green）
```

### 6.2 组合推出 G 的最小候选（均非等价条件）
```
(i)  C1(V>=0) ∧ C3(g0 <= gap) ∧ (V + g0 >= (sF-1)A)   ⇒ G
     其中 g0 为固定下界（如 tame 总和），第三条是纯算术，独立于 gap 的具体值；
(ii) A1（逐位，严格强） ⇒ G（在 arch/torsion 归位假设下）；
(iii) B1(B) ∧ B2(B)（分段互补，单段均弱于 G） ⇒ G；
(iv)  ErrorVariant C（C>0，误差版，非等价） ⇒ G 的 -C 近似。
```
注意：(i) 的第三条 `V + g0 >= (sF-1)A` 若取 g0 = gap 则与 G 等价（禁用）；必须固定 g0
为**独立可算**的量（如 tame 展开下界），从而第三条比 G 弱/独立。

### 6.3 明显比 G 弱（更容易）的条件
```
BoundedQ B（有限 m 段）
AsymptoticGap B（渐近段）
N5Weak C (C>0)          -- 误差版
ErrorVariant C (C>0)    -- paper C_Θ 误差
PerPrime + buffer       -- 分组聚合
```
这些条件可各自独立地尝试；它们的合取（非等价）可覆盖 G。

### 6.4 循环性检查（严禁）
```
禁止条件：  M >= 0、V + gap >= (sF-1)A（G 本身）
禁止条件：  N5Weak 0（与 G 等价）
禁止条件：  gap >= (sF-1)A - V（精确式，与 G 等价）
禁止条件：  SSIneq、Corollary312Variant、PaperNormVerdict（目标的形式）
允许依赖：  V>=0、gap>=0、ind2>=0、arch>=0、torsion>=0、N1/N3/N4 代数、
           N5Weak C>0、PerPlace/PerPrime 固定分组、BoundedQ B、AsymptoticGap B。
```

## 7. Lean 骨架（条件定义与组合定理的形态）

```lean
def PerPlace (T H : Place -> Real) : Prop := forall v, T v <= H v
def PerPrime (T H : Nat -> Real) (buffer : Nat -> Real) : Prop :=
  forall p, (∑ v in fiber p, T v) <= (∑ v in fiber p, H v) + buffer p
def BoundedQ (B : Nat) : Prop := forall D, (forall w hw, D.qOrder w hw <= B) -> G D
def AsymptoticGap (B : Nat) : Prop := forall D, (exists w hw, B < D.qOrder w hw) -> G D
def N5Weak (A rhs C : Real) : Prop := -A - C <= rhs
def VNonneg : Prop := 0 <= V
def GapNonneg : Prop := 0 <= gap
def ErrorVariant (C : Real) : Prop := forall D, -C <= M D

/-- Combination: C1 + C3 + arithmetic -> G (non-equivalent conditions). -/
theorem G_of_VNonneg_gapLower (hV : 0 <= V) (hg : g0 <= gap)
    (harith : V + g0 >= (sF - 1) * A) : V + gap >= (sF - 1) * A := by linarith
```

## 8. 结论

1. G 被拆成 5 组条件：A（place/prime/分组）、B（m 阈值分段）、C（项独立）、D（数据层）、E（误差常数）；
2. 每个条件均**不与 G 等价**（C4 取 C>0；分段/分组/项条件均严格弱或独立）；
3. 已可满足（green/源级）：N1、N3、N4（代数工具）、C2、C7、C9、C10、D7；
4. 组合路径：(i) `V>=0 ∧ g0<=gap ∧ V+g0>=(sF-1)A` ⇒ G（第三条为独立算术）；
   (ii) 逐位 A1（严格强）；(iii) 分段 B1∧B2；(iv) 误差版 ErrorVariant C>0；
5. 仍 OPEN：N2（V≤box 的字典）、C1（V>=0 端口）、C4（N5Weak C，GAP-N5）、C5（hscalar）、
   A2 wild buffer、B1 有限段形式化；
6. 严禁把 G/N5Weak(0)/精确 gap 下界当条件；本 DAG 已满足用户“逐条件可满足且非等价”要求。