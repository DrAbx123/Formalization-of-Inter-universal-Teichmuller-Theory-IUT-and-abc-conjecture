# OUR-COR312-ROUTE — 用我们自己的构造栈重建 Cor 3.12 路线 (A1040)

| field | value |
|---|---|
| Status | PARTIAL (组件已盘点；形成 N1-N5 链；N5 装配恒等式仍是唯一 GAP；不依赖 lana variant/SSIneq)。**Gate 注（A1045）：N1–N4 及 S30xx 均为 PENDING-WATCHDOG（源码/olean 存在，未过 watchdog trio/#print axioms/probe），不得写 green gate；Olean TRUE ≠ gate。** |
| 范围 | 仅用 `tmp/sheaf/xif/paper/` 下我们的 green 定理；不引用 lana 的 `Corollary312Variant`/`SSIneq`/`ConcreteVariantData` 作前提 |
| 目标 | `M := A - R >= 0`，A = logQ/(2l)（q-pilot），R = |log Theta|；最终对应 paper Cor 3.12 的 variant |

## 1. 组件清单（PENDING-WATCHDOG；非 green gate）

### 1.1 Step-V 代数不等式（paper Step (v)）
`Mzk1PaperStepVBoxActual`：
```
def paperLHS (l D Q S T) : Real := ((l+5)/4)*D - ((l+1)/24)*Q + S + (l+5)*T
def paperRHS (l D Q S T) : Real := ((l+1)/4)*((1+4/l)*D - Q/6 + (4/l)*S + (20/3)*T)
theorem paperStepV_inequality (l D Q S T) (hl : 5 <= l)
    (hD : 0 <= D) (hS : 0 <= S) (hT : 0 <= T) :
    paperLHS l D Q S T <= paperRHS l D Q S T
```
- 已 green；**Q 精确抵消**（差值 = `(1/l)D + (1/l)S + ((2l-10)/3)T >= 0`）；
- 类型：代数不等式（纯实数算术）；
- 用途：paper Step (v) 的 `per-j + symmetrization + j-average` 化简后的**核心比较**。

### 1.2 V 的 Step-V 上界接口
`Mzk1StepVIdentificationActual`：
```
structure StepVDictionary where
  V floorTerm sumB logp lambda sumDiff exceptional l logd logf C0 : Real
  V_le_step : V <= stepVExpr floorTerm sumB logp
  step_bound : stepVExpr ... <= stepVRHS lambda sumDiff logp exceptional
  box_bound : stepVRHS ... <= paperBox l logd logf C0
theorem volume_upper_of_dictionary (D : StepVDictionary) :
    D.V <= paperBox D.l D.logd D.logf D.C0
def PaperDictionaryShape (l logd logf ... C0) : Prop :=
  paperBox l logd logf C0 = ((l+5)/4)*(logd + logf) + C0
```
- `V <= paperBox`（green，条件于 three fields）；
- `PaperDictionaryShape` 是**定义/待填**（paper `logdf = logd + logf`，见 `Mzk1StepVVolumeUpperActual:29 logdf := logd + logf`）；
- 类型：对象识别（V 的字典）+ 数值上界。

### 1.3 D_exact 的 L7 下界（paper Step (v) 的 D 项）
`Mzk1DExactFromHullActual`：
```
def DExact (w h logp : ι -> Real) : Real := sum v, w v * h v * logp v
def DExactWithArch ... := DExact ... + arch
theorem tame_height_ge (l e) (hl : 0 < l) (hle : l <= e) : 1 - 1/l <= 1 - 1/e
theorem L7_term (w logp l e) (hw : 1 <= w) (hl : 1 <= l) (hle : l <= e) (hlogp : 0 <= logp) :
    (1 - 1/l)*logp <= w*(1 - 1/e)*logp
theorem L7_global : (sum v, (1 - 1/l)*logp v) <= DExact w h logp
theorem L7_with_arch ... (harch : 0 <= arch) :
    (sum v, (1 - 1/l)*logp v) <= DExactWithArch w h logp arch
```
- 类型：逐位估计 + 求和；green；
- 用途：D 项的 tame 下界 `(1 - 1/l) sum logp`。

### 1.4 deficit 展开（q-pilot 侧与 theta 侧的比较）
`Mzk1PaperNormThetaActual` / `Mzk1PaperNormDeficitActual`：
```
def thetaSumPaper (nC) (l A) : Real := (1/nC) * sum_{j< nC} ((j^2 - 1)/(2l)) * A
def clana (nC) (l) : Real := (sFactor nC - 1) / (2*l)
theorem thetaSumPaper_eq_clana_mul : thetaSumPaper nC l A = clana nC l * A
theorem deficit_expanded_form (ssCoeff A diff arch torsion cLana) :
    ssCoeff*A - ((diff - arch + torsion) + cLana*A) = ssCoeff*A - diff + arch - torsion - cLana*A
theorem deficit_nonpos_iff :
    ssCoeff*A - diff + arch - torsion - cLana*A <= 0 <->
      (ssCoeff - cLana)*A + arch - torsion <= diff
```
- 类型：定义展开 + 等价重写；green；
- 用途：把 deficit 条件化为最终线性不等式 `(ssCoeff - cLang)*A + arch - torsion <= diff`。

## 2. 节点链 N1-N5

### N1: paper Step (v) 代数（green）
`paperStepV_inequality`：`paperLHS <= paperRHS`（假设 D,S,T>=0）；Q 抵消。
类型：不等式。所需：`Mzk1PaperStepVBoxActual`（green）。

### N2: V 的上界（green）
`volume_upper_of_dictionary : V <= paperBox`；若 `PaperDictionaryShape` 则
`V <= ((l+5)/4)*(logd + logf) + C0`。
类型：对象识别 + 上界。所需：`StepVDictionary` 的 3 个字段 + `PaperDictionaryShape`。

### N3: D_exact 下界（green）
`L7_with_arch`：`sum (1 - 1/l) logp <= DExactWithArch`（arch>=0）。
类型：估计。所需：逐位 tame 假设 `l <= e`、`w >= 1`、`logp >= 0`。

### N4: deficit 条件（green 代数）
`deficit_nonpos_iff`：`deficit <= 0 <-> (ssCoeff - cLana)*A + arch - torsion <= diff`。
类型：等价重写。所需：`thetaSumPaper_eq_clana_mul` + `deficit_expanded_form`。

### N5: 装配恒等式（**唯一 GAP**）
把 N1-N4 组装成 `M = A - R >= 0` 需要：
```
(ASSEMBLY)  M = A - R
  且  R <= paperRHS（或其等价形式）
  且  A >= paperLHS 的 q 部（或等价）
```
具体地，缺失的恒等式是：
```
M = A - R = A + rhs = A + (V + gap - sF*A)      -- Gap 链（我们自己的 DECOMP-NORMALIZATION）
  = V + gap - (sF - 1)*A
```
于是 `M >= 0 <-> V + gap >= (sF - 1)*A`；N2 给 `V <= box`，N4 给 deficit 条件；
**把 `gap`/`R` 与 `box`/`deficit` 连接起来的那条等式不在我们的 green 文件里**——
这是 N5 的全部内容，也是 Cor 3.12 的实质数学内容。

## 3. 最终不等式与 variant 的精确对应

paper 的关键量与我们符号：
| paper | 我们 | 来源 |
|---|---|---|
| `D` | `D_exact`（含 arch）/ `log d^K` 型 | 1.3 |
| `Q` | q 项，`(l+1)/24 log q = sF*A` | A1038（j-average） |
| `S` | arch/shell 项（`log s^Q`） | 1.2/1.3 |
| `T` | `l*_mod log s^<=` 项 | 1.2 |
| `paperLHS <= paperRHS` | Step V 代数（N1） | green |
| `V <= box` | 1.2 | green |
| `deficit <=0` | N4 | green 等价 |
| `M = A - R` | N5 GAP | — |

**目标形式**（待 N5 补全）：
```lean
theorem our_cor312_variant
    (hstep : paperLHS l D Q S T <= paperRHS l D Q S T)   -- N1 (green)
    (hbox : V <= paperBox l logd logf C0)                 -- N2 (green)
    (hl7 : sum (1 - 1/l) logp <= DExactWithArch ...)      -- N3 (green)
    (hdeficit : (ssCoeff - cLana)*A + arch - torsion <= diff) -- N4 (green 等价)
    (hassembly : M = A - R ∧ R <= paperRHS_related)       -- N5 GAP
    : 0 <= M
```

## 4. 还缺哪条（精确）

1. **N5 (ASSEMBLY)**：`M = A - R` 与 `R <= paperRHS`（或 `V + gap >= (sF-1)A`）的等价；
   这是 paper Cor 3.12 的几何内容（Θ-pilot hull 与 q-pilot 的比较），我们的组件只到
   `V <= box` 和 `deficit` 条件；
2. **`PaperDictionaryShape` 的证明**（paper `logdf = logd + logf`）：待把 `logdf` 定义与 box 对齐；
3. **D/Q/S/T 的数值识别**：`D = D_exact`、`Q = (l+1)/24 log q = sF*A`、`S = arch/shell`、
   `T = l*_mod log s^<=` 的具体实例化；
4. **arch/torsion 位置**：N4 的 `arch`/`torsion` 与 N2/N3 的 arch 一致性（GAP-A/GAP-B，见 DECOMP-NORMALIZATION）；
5. **deficit 的符号方向**：`deficit <=0` 是 `(ssCoeff - cLana)A + arch - torsion <= diff`，
   与 `M>=0` 的方向需 N5 才能对齐（A1035 已确认 deficit 是下界方向，不能单独当 variant）。

## 5. 结论

1. 我们自己的 green 组件已覆盖 N1（Step V 代数）、N2（V 上界）、N3（D_exact 下界）、
   N4（deficit 代数）；
2. 唯一实质缺口是 **N5 装配恒等式**：`M = A - R` 与 `R <= paperRHS（box）` 的连接，
   即 `V + gap >= (sF-1)A` 的几何内容；
3. 在 N5 缺失的情况下，**不能声称**我们已有 Cor 3.12 或 variant；N1-N4 是必要条件；
4. 本路线不依赖 lana 的 variant/SSIneq；所有前提均来自我们自己的文件（或显式假设）；
5. 建议：把 N5 作为 C 线唯一剩余任务，形式化为
   `assembly_identity : V + gap = paperRHS - (sF-1)*A` 或等价的 `R = paperRHS_related`，
   并明确其与 paper Step (xi-d)（determinant/log-volume 比较）的对应。