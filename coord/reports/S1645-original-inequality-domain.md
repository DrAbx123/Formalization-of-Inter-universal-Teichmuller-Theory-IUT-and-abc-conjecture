# S1645: 原文不等式定义域审计

日期：2026-10-31。只读审计；未修改生产 Lean，未新增 axiom/sorry，未写假证明。

**结论先行。** 项目

- `s839HolomorphicLattice` = `O_hol` = 局部整闭包 `(R_I)~`，
- `s853FractionalZero` = `F(0)` = 整数张量格 `R_I`，

之间的 `F(0) <= O_hol` 确实是 IUT IV, Proposition 1.1 的第二条包含 `R_I ⊆ (R_I)~`，但它不是 IUT III, Corollary 3.12 的 Route C 不等式，也不是 S853/S1570/S1574/S1634 实际需要的吸收条件。原文 Route C 对应的全局不等式是

```
−|log(Θ)| ≥ −|log(q)|
```

（IUT III, Cor. 3.12），对象是 multiradial representation 中 possible images 的 holomorphic hull 的 procession-normalized log-volume；定义域不是一个 tensor block 上的 lattice，而是带 `j ∈ |F_l|`、`v_Q ∈ V_Q`、Kummer isomorphism 与 (Ind1),(Ind2),(Ind3) 的全局 hull。二者不是同一个不等式。

---

## 0. 审计边界

### 0.1 报告文件位置

截至本审计读取时，`coord/reports/` 下没有 S1475/S1567/S1570/S1574/S1579/S1634 的独立 `.md` 报告。这些编号的内容在：

| 编号 | 文件 | 作用 |
|---|---|---|
| S1475 | `tmp/sheaf/xif/paper/S1475ReportCExactInputsActual.lean` | Route C 三项输入；S863 由 S841 absorption 推出 |
| S1567 | `tmp/sheaf/xif/paper/S1567AbsNormNatGeneratorActual.lean` | 证明 `S1087CoeffLe` |
| S1570 | `tmp/sheaf/xif/paper/S1570ReportCInputsClosedActual.lean` | containment actual；product 条件于 `O_hol <= F(0)` |
| S1574 | `tmp/sheaf/xif/paper/S1574ProductImageAbsorptionActual.lean` | `O_hol <= F(0)` 到 absorption/product equality |
| S1579 | `tmp/sheaf/xif/paper/S1579OLeFractionalZeroAnalysisActual.lean` | 证明反向 `F(0) <= O_hol`；正向 missing |
| S1634 | `tmp/sheaf/xif/paper/S1634OLeFractionalZeroActual.lean` | 把 `O_hol <= F(0)` 命名为 "Route C basic inclusion"，无 inhabitant |

`coord/XI_F_ORIGINAL_ROUTE.md` 只登记 S1475/S1567 的验收状态，没有原文不等式定义域。原文锚点从 IUT III/IV 文本读取。

### 0.2 原文没有 `F(0)` / `O_hol` 这两个符号

对 IUT III、IUT IV 源文本做字面检索：`F(0)`、`F (0)`、`O_hol`、`O hol` 均为 0 次。原文使用

- `R_I = ⊗_{i∈I} R_i`，`R_i = O_{k_i}`；
- `(R_I)~`，即 `R_I` 在其分式环中的 normalization；
- `p^λ · (R_I)~`，`log_p(R_I^×)`，`φ`，`λ`，`d_I`，`a_I`，`b_I`。

所以 `F(0)`、`O_hol` 是项目缩写，不是原文符号。把缩写当原文对象，是本次命名混淆的根源之一。

### 0.3 证据状态

- 只读读取了上述 Lean 文件、`FinitePlace*` 定义、IUT III/IV 源文本。
- 另建 `tmp/_S1645Probe.lean`：只含 `def ... : Prop` 与 `#check`，不含 theorem/inhabitant/sorry；`lake env lean` exit 0。这是 statement_compiles，不是 proof_body_checked。
- 没有重新构建 S839/S853/S1475/S1634 的 olean，没有运行 Project/comparator。已有 olean 的 mtime 只作辅助，不作本次验收结论。

---

## 1. 原文的三层不等式

原文没有 "Route C" 这个术语。Route C 是项目 S1475 的内部叫法。相关原文命题分三层。

### 1.1 全局层：IUT III, Corollary 3.12

原文（IUT III, lines 10324–10353）：

> `−|log(Θ)|` ∈ R ∪ {+∞} for the procession-normalized mono-analytic log-volume of the holomorphic hull of the union of the possible images of a Θ-pilot object, relative to the relevant Kummer isomorphisms, in the multiradial representation of Theorem 3.11, (i), which we regard as subject to the indeterminacies (Ind1), (Ind2), (Ind3).
>
> `−|log(q)|` ∈ R for the procession-normalized mono-analytic log-volume of the image of a q-pilot object, ..., which we do **not** regard as subject to (Ind1), (Ind2), (Ind3).
>
> Then ... `−|log(Θ)| ≥ −|log(q)|`.

实际对象：

- 左边：holomorphic hull 的 procession-normalized log-volume；hull 是 possible images 的并集的 hull；average 取 `j ∈ F_l^×`；带 Kummer isomorphism 与 (Ind1),(Ind2),(Ind3)。
- 右边：q-pilot image 的 procession-normalized log-volume；**不带** Ind1/2/3。

定义域：

- 全局 multiradial representation 的 `IQ`/log-shell 容器；
- 索引包括 `n ∈ Z`、`j ∈ |F_l|`、`v_Q ∈ V_Q`；
- hull 定义见 IUT III, Remark 3.9.5(i)（lines 7652–7680）：hull 是包含给定 region 的、形如 `λ · O` 的 **最小** subset，且 `λ` 的每个分量 **nonzero**；若 region 不 relatively compact，则 hull 定义为整个 `IQ`。

方向：

```
−|log(Θ)| ≥ −|log(q)|
```

等价地，记 `qSigned = −|log(q)|`、`thetaSigned = −|log(Θ)|`，则 `qSigned <= thetaSigned`。这不是 lattice inclusion，而是两个 log-volume 实数的比较。

### 1.2 局部层：IUT IV, Proposition 1.1

原文（IUT IV, lines 400–450；核心 display 426–427）：

```
p^{d_{I*}} · (R_I)~ ⊆ R_I ⊆ (R_I)~
```

其中 `I` 有限，`|I| ≥ 2`；`k_i / Q_p` 有限扩张；`R_i = O_{k_i}`；`R_I = ⊗_{i∈I} R_i`（over `Z_p`）；`(R_I)~` 是 normalization；`d_i` 是 different order，`d_I = Σ d_i`，`I* = I \ {*}`，`d_{I*} = Σ_{i∈I*} d_i`。

实际对象：`R_I` 与 `(R_I)~`，都是 `⊗ K_i` 中的 `Z_p`-lattice。

定义域：一个固定的 local tensor `⊗_{i∈I} K_i`，有限 index set `I`。

方向：两条方向相反、带不同 shift 的包含：

1. `p^{d_{I*}} (R_I)~ ⊆ R_I`：normalization 乘 different shift 后落回整数张量；
2. `R_I ⊆ (R_I)~`：整数张量落在 normalization 中。

这不是 Route C 的 q/Θ 比较，只是 IUT IV §1 的 normalization/different 辅助引理。项目中的 `F(0) <= O_hol` 精确对应第 2 条；第 1 条对应 `p^d O_hol <= F(0)`，项目当前没有以这个 shift 作为 S853 的输入。

### 1.3 局部层：IUT IV, Proposition 1.2(ii) 与 1.4(iii)

原文（IUT IV, lines 508–511）：

```
φ(p^λ · (R_I)~) ⊆ p^{⌊λ−d_I−a_I⌋} · log_p(R_I^×)
  ⊆ p^{⌊λ−d_I−a_I⌋−b_I} · (R_I)~
```

原文（IUT IV, lines 696–712）：

```
μlog(p^{⌊λ−d_I−a_I⌋} · log_p(R_I^×))
  ≤ (−λ + d_I + 1 + 4·|I*|/p) · log(p)

μlog(p^{⌊λ−d_I−a_I⌋−b_I} · (R_I)~)
  ≤ (−λ + d_I + 1) · log(p) + Σ_{i∈I*} (3 + log(e_i))
```

实际对象：

- `p^λ · (R_I)~`：带 λ 的 normalized fractional lattice；
- `log_p(R_I^×)`：log-shell；
- `φ`：`log_p(R_I^×) ⊗ Q_p` 上保持 `log_p(R_I^×)` 子模的 automorphism；
- `μlog`：normalized log-volume，满足 `μlog((R_E)~)=0`、`μlog(p·(R_E)~)=−log(p)`（IUT IV, 1.4(i), lines 671–682）。

定义域：同样的 local tensor，但对象已经是 **normalized** `p^λ (R_I)~`，不是 `R_I` 本身。

方向：先 `φ`，再落入 log-shell，再落入带 shift 的 normalization；log-volume 是 **上界**（`≤`）。这里没有 `O_hol <= F(0)` 的无 shift 包含。正确 shift 是 `⌊λ−d_I−a_I⌋`，并带 `d_I`、`b_I` 修正项。

---

## 2. 项目对象与原文对象的逐项对应

### 2.1 项目定义

`tmp/sheaf/xif/paper/S839PaperRootMinimalProductCompactActual.lean`（lines 51–69）：

```lean
noncomputable def s839FractionalLattice : Submodule ℤ_[(qVFamTensorP T b)]
    (qVFamTensorBlock T b) :=
  arithmeticTupleFractionalLattice (qVFamTensorPlaces T b) qVFamTensorTuple
    (paperRootCoefficientFamily (l := l) T b)

noncomputable def s839HolomorphicLattice : Submodule ℤ_[(qVFamTensorP T b)]
    (qVFamTensorBlock T b) :=
  arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b) qVFamTensorTuple
```

`tmp/sheaf/xif/paper/S853OInFZeroAbsorptionActual.lean`（lines 47–60）：

```lean
noncomputable def s853FractionalZero : Submodule ℤ_[(qVFamTensorP T b)]
    (qVFamTensorBlock T b) :=
  arithmeticTupleFractionalLattice (qVFamTensorPlaces T b) qVFamTensorTuple
    (fun _ => 0)

def S853HolomorphicLeFractionalZero : Prop :=
  s839HolomorphicLattice (l := l) T b <= s853FractionalZero (l := l) T b

def S853FractionalMulHolomorphicLe : Prop :=
  s839FractionalLattice (l := l) T b * s839HolomorphicLattice (l := l) T b <=
    s839FractionalLattice (l := l) T b
```

展开：

- `s839FractionalLattice = F(cRoot)`，`cRoot = paperRootCoefficientFamily = order(qVFamily)/(2l)`；
- `s853FractionalZero = F(0) = arithmeticTupleValuationIntegerLattice = R_I`（`arithmeticTupleFractionalLattice_zero`，`FinitePlaceFractionalTensorLattice.lean` lines 53–61）；
- `s839HolomorphicLattice = O_hol = (integralClosure ℤ_[p] ...).toSubmodule = (R_I)~`（`FinitePlaceNormalizedUnitScalingLogVolume.lean` lines 75–87；`FinitePlaceHolomorphicIntegralClosure.lean` 明确把 Prop 1.1 的 `O_hol` 解释为 integral closure）。

### 2.2 关键恒等式与包含

1. `F(0) = R_I`：`s1579FractionalZero_eq_integerLattice`（S1579 lines 36–40）。
2. `F(0) <= O_hol`：`s1579IntegerLattice_le_holomorphic`（S1579 lines 42–59），即原文 Prop 1.1 的 `R_I ⊆ (R_I)~`。
3. `O_hol = (R_I)~`：`coefficient_arithmeticTupleHolomorphicLattice`（`FinitePlaceNormalizedUnitScalingLogVolume.lean` lines 81–87）。
4. `F(0) * O_hol = O_hol`：`arithmeticTupleValuationIntegerLattice_mul_holomorphicLattice`（`FinitePlaceStepVAssembly.lean` lines 47–75）。这是原文的 local normalization 事实，不是 `O_hol <= F(0)`。
5. `F(c) * O_hol` 是项目中的 `paperLambdaORegion c`（S793 lines 64–70），也就是原文 `p^c (R_I)~` 的 local 类比；它一般 **不等于** `F(c)`。
6. `F(c) * O_hol <= F(c)` 等价于把 normalized 对象压回未 normalized 的 `F(c)`。在 principal one-factor 模型中，两边同乘 `p^{-c}` 后就是 `O_hol <= F(0)`，即 `(R_I)~ <= R_I`。这与原文 Prop 1.1 的 `R_I <= (R_I)~` 方向相反；原文只给 `p^{d}(R_I)~ <= R_I`，不是 `(R_I)~ <= R_I`。

### 2.3 逐项对比表

| 项目 | 原文 IUT III Cor. 3.12 | 原文 IUT IV Prop. 1.1 | 原文 IUT IV Prop. 1.2(ii)/1.4(iii) | 项目 s839/s853 |
|---|---|---|---|---|
| 对象 | `−abs(log(Θ))`：holomorphic hull 的 log-volume | `R_I`，`(R_I)~` | `p^λ (R_I)~`，`log_p(R_I^×)` | `F(c)` tensor lattice，`O_hol` integral closure |
| ambient | global `IQ`/multiradial representation | local `⊗_{i∈I} K_i` | local `⊗_{i∈I} K_i` | 单个 `qVFamTensorBlock T b`，index `Unit` |
| index/quantifier | `n∈Z`，`j∈F_l`（含 0），`v_Q∈V_Q`；all possible images | finite `I` | finite `I`，`λ∈(1/e_i)Z` | 固定 bad place `b`；无 `j`、无 `n`、无 `v_Q` |
| Ind | (Ind1),(Ind2),(Ind3) | 无 | `φ` automorphism | 无 |
| 方向 | `−abs(log(Θ)) ≥ −abs(log(q))` | `p^{d}(R_I)~ ⊆ R_I ⊆ (R_I)~` | `φ(p^λ(R_I)~) ⊆ p^{...} log_p(R_I^×) ⊆ p^{...}(R_I)~`；`μlog ≤ ...` | `F(0) <= O_hol`（已证）；或 `O_hol <= F(0)`（missing）；或 `F(c)*O_hol <= F(c)`（missing） |
| normalization | procession average，`μlog(O)=0` | `μlog((R_E)~)=0` | `μlog((R_E)~)=0`，带 `d_I,b_I` shift | 无 paper normalization；Haar/log-volume 是另一层 |
| 原文地位 | 目标不等式 | 辅助 normalization 引理 | 局部 Step(v) 的 shift/log-volume 估计 | `F(0)<=O_hol` 只对应 Prop 1.1 第二条；其余是项目构造 |

---

## 3. S1475/S1567/S1570/S1574/S1579/S1634 链条审计

### 3.1 S1475：Route C 三项输入

S1475 header（lines 12–18）说 Route C 有三项 exact inputs：

1. `S1086Q1UImageContainment`（等价 `S1087CoeffLe`）；
2. `S1086Q1URegionMeasurable`；
3. `S863ProductImageEq`。

S1475 证明第 2 项 unconditional（lines 238–244），并把第 1 项归约到 region inclusion（lines 253–270）：

```lean
S1086Q1UImageContainment ↔
  qPilotQ1URegion ⊆ paperLambdaORegion (paperRootCoefficientFamily)
```

第 3 项由 `S841PointwiseAbsorption` 推出（lines 280–306），docstring 写成 "equivalently the existing S853 input `O_hol <= F(0)`"（lines 274–278）。

审计判断：

- S1475 的 Route C 是 **三项输入的合取链**，不是单一不等式；
- 第 1 项对象是 `qPilotQ1URegion` 与 `paperLambdaORegion(cRoot)`，都是 `F(c)*O_hol` 形状，系数是 `qVFamPureCoefficient` 与 `order/(2l)`，**不是 `F(0)`**；
- 第 3 项才是 `F(c)*O_hol <= F(c)` / `O_hol <= F(0)` 的用武之地；它和 Cor 3.12 全局 log-volume 不等式仍不是同一命题。

### 3.2 S1567：实际的系数比较

S1567 证明 `s1567CoeffLe_actual : S1087CoeffLe`。其中 `S1087CoeffLe`（S1087 lines 35–38）：

```lean
def S1087CoeffLe : Prop :=
  ∀ i : qVFamTensorV,
    paperRootCoefficientFamily (l := l) T b i <= qVFamPureCoefficient T b i
```

这是系数不等式 `cRoot <= cQ`。配合 `s1087RegionContainment`（S1087 lines 40–55）得到 `qPilotQ1URegion ⊆ paperLambdaORegion cRoot`；再由 S1475 的等价性得到 `S1086Q1UImageContainment`；S1570 组装为 `s1570Q1UImageContainment_actual`（S1570 lines 38–42）。

审计判断：

- 这是当前项目中对原文 q/Θ 局部比较的 **actual** 实现；
- 对象是 `F(cQ)*O_hol` 与 `F(cRoot)*O_hol`，不是 `F(0)`；
- 它是 Cor 3.12 的 **局部充分条件/局部影子**，不是 Cor 3.12 的全局不等式本身。

### 3.3 S1570/S1574：product equality 条件于 `O_hol <= F(0)`

S1570：

- `s1570Q1UImageContainment_actual`：containment actual（lines 38–42）；
- `s1570ProductImageEq_of_pointwiseAbsorption`：S841 ⇒ S863（lines 46–49）；
- `s1570ProductImageEq_of_OLeZero`：`O_hol <= F(0)` ⇒ S863（lines 53–57）；
- `S1570ProductImageEqExactInput : Prop := S853OLeFractionalZeroRequired`（lines 61–62），把 `O_hol <= F(0)` 当作 product side 的 exact input。

S1574：

- `s1574PointwiseAbsorption_of_OLeZero`：`O_hol <= F(0)` ⇒ S841（lines 32–35）；
- `s1574ProductImageEq_of_OLeZero`：`O_hol <= F(0)` ⇒ S863（lines 38–41）；
- docstring 明确写："the tree currently proves only the reverse `F(0) <= O_hol`, not this inclusion"（lines 43–47）。

审计判断：

- S1570/S1574 没有证明 `O_hol <= F(0)`；只证明 **条件构造器**；
- 这个条件构造器是 `F(c)*O_hol <= F(c)` 的充分条件，而 `F(c)*O_hol <= F(c)` 本身不是原文命题；
- 因此 S1570/S1574 不能作为 "原文 Route C 不等式已满足" 的证据。

### 3.4 S1579：证明的是反向

S1579：

- `s1579FractionalZero_eq_integerLattice`：`F(0) = R_I`；
- `s1579IntegerLattice_le_holomorphic : F(0) <= O_hol`（lines 44–59）；
- `S1579ForwardInclusionRequired : Prop := S853OLeFractionalZeroRequired`（lines 61–64），即 `O_hol <= F(0)`，无 inhabitant；
- docstring（lines 61–62）明确："No proof is available from the reverse inclusion, and no counterexample is asserted."

审计判断：

- S1579 证明的是原文 Prop 1.1 第二条，不是 S853 需要的第一条（带 shift 的那条更不是）；
- 它证明了 `F(0) <= O_hol`，不能反过来当成 `O_hol <= F(0)`；
- 把 S1579 的 `F(0) <= O_hol` 当作 Route C 不等式的证明，是把 **反向 normalization 包含** 当成 **正向吸收条件**。

### 3.5 S1634：命名误导的核心

S1634（lines 32–65）：

```lean
def S1634RouteCBasicInclusion : Prop :=
  s839HolomorphicLattice (l := l) T b <= s853FractionalZero (l := l) T b

theorem s1634RouteCBasicInclusion_iff :
    S1634RouteCBasicInclusion ↔ S853OLeFractionalZeroRequired :=
  Iff.rfl

theorem s1634ReverseInclusion_actual :
    s853FractionalZero (l := l) T b <= s839HolomorphicLattice (l := l) T b :=
  s1579IntegerLattice_le_holomorphic (l := l) T b

abbrev S1634ExactFirstInput : Prop :=
  S853OLeFractionalZeroRequired (l := l) T b
```

审计判断：

- `S1634RouteCBasicInclusion` 的定义是 `O_hol <= F(0)`，不是 `F(0) <= O_hol`；
- 它没有 inhabitant；`s1634ReverseInclusion_actual` 证明的是反向 `F(0) <= O_hol`；
- 把 `O_hol <= F(0)` 命名为 "Route C basic inclusion" 是 **项目命名**，不是原文命名；原文没有这个无 shift 的包含；
- 这个定义的实际作用是把 S853 的 missing input 重述为 "Route C"，从而在报告语言上把 "Route C 已归约到 S853" 误读成 "Route C 就是 S853 的 lattice inclusion"。审计结论：**不能按名字等同**。

---

## 4. 哪些是充分条件，哪些不是原文

| 命题 | 项目状态 | 能推出什么 | 是否原文 |
|---|---|---|---|
| `F(0) <= O_hol` | 已证（S1579） | 只给出 `R_I ⊆ (R_I)~`；对 `F(c)*O_hol <= F(c)` 没有帮助（方向相反） | 是，IUT IV Prop. 1.1 第二条；但只是 normalization 辅助引理，不是 Route C 不等式 |
| `O_hol <= F(0)` | missing（S853/S1579/S1634 均无 inhabitant） | `F(c)*O_hol <= F(c)`（S853）⇒ S841 ⇒ S863 | 不是原文；原文是 `p^{d}(R_I)~ <= R_I`，带不同 shift；无 shift 版本一般更强 |
| `F(c)*O_hol <= F(c)` | missing / 条件构造 | S841 pointwise absorption ⇒ S863 product equality | 不是原文；原文对象是 `F(c)*O_hol` 本身，不把它压回 `F(c)` |
| `S863ProductImageEq` | 条件构造（S1475 lines 280–306） | product compactness / S806 closedness | 不是原文；是项目为 compactness 引入的 set-level identification |
| `S1087CoeffLe`（`cRoot <= cQ`） | 已证（S1567） | `qPilotQ1URegion ⊆ paperLambdaORegion(cRoot)` ⇒ `S1086Q1UImageContainment` | 不是原文全文；是原文 q/Θ 局部比较的系数影子/充分条件 |
| `qPilotQ1URegion ⊆ paperLambdaORegion(cRoot)` | 已证（S1567 + S1087 + S1475，S1570 组装） | S1086 per-b log inequality（还需 measurability、Haar/pushforward 等） | 不是原文全文；是 Cor 3.12 的局部充分条件 |
| `qPilotThetaHullComparison`（`qSigned <= thetaSigned`） | 目标/条件；`GlobalThetaHullVsQPilotComparisonActual` 只给等价与条件构造 | 原文 Cor 3.12 的全局 signed log-volume 比较 | 是，Cor 3.12 的 Lean 候选陈述；尚无证明 |
| `arithmeticTuple_fractionalAbsorption_of_order` | 已证（`FinitePlaceFractionalAbsorption.lean` lines 397–435） | 原文 Prop 1.2(ii) 的 element chain / 带 shift 的包含 | 是，IUT IV Prop 1.2(ii) 的局部精确陈述 |

要点：

1. `F(0) <= O_hol` 是原文的，但它是 **反向 normalization**，不是 S853 的正向吸收条件，也不是 Cor 3.12 的比较。
2. `O_hol <= F(0)` 是 S853 的充分条件，但 **不是原文**；原文只给 `p^{d}O_hol <= F(0)`。
3. `F(c)*O_hol <= F(c)` 是 S841/S863 的充分条件，但 **不是原文**；它把 normalized 对象压回 unnormalized 对象，等价于 `O_hol <= F(0)`。
4. `S1087CoeffLe` / q region containment 是原文局部比较的 **actual 充分条件**，但不是 Cor 3.12 全局不等式，也不是 `F(0)` 的陈述。
5. Cor 3.12 的全局不等式 `qSigned <= thetaSigned` 才是 Route C 最终要的比较；它目前没有证明。

---

## 5. 精确的原文不等式 Lean 陈述（只声明类型，不写证明）

以下 `def ... : Prop` 只声明命题类型，不含 theorem、不含 inhabitant、不含 sorry。它们已在 `tmp/_S1645Probe.lean` 中通过 `lake env lean` exit 0 的 elaboration 检查；这是 statement_compiles，不是 proof_body_checked。

### 5.1 原文 IUT IV Prop. 1.1 第二条（已由 S1579 证明）

```lean
/-- 原文 IUT IV Prop. 1.1: `R_I ⊆ (R_I)~`. -/
def S1645OriginalProp11_RI_le_normalization : Prop :=
  s853FractionalZero (l := l) T b <= s839HolomorphicLattice (l := l) T b
```

对应证明：`s1579IntegerLattice_le_holomorphic`。注意这是 `F(0) <= O_hol`，不是 `O_hol <= F(0)`。

### 5.2 原文 IUT IV Prop. 1.1 第一条（带 shift；项目当前没有这个形式的 inhabitant）

```lean
/-- 原文 IUT IV Prop. 1.1 的 one-factor 形式:
    `p^d * O_hol <= F(0)`，其中 `d = d_{I*}` 是 different order。
    这是带 shift 的包含，不是 `O_hol <= F(0)`。 -/
def S1645OriginalProp11_primeShift (d : ℕ) : Prop :=
  ∀ x : qVFamTensorBlock T b,
    x ∈ s839HolomorphicLattice (l := l) T b →
    (qVFamTensorP T b : qVFamTensorBlock T b) ^ d * x ∈
      s853FractionalZero (l := l) T b
```

说明：

- 原文是 `p^{d_{I*}} (R_I)~ ⊆ R_I`；
- 项目的多因子 different-generator 版本在 `IntegralTraceDualTensorInclusion.lean` 中有绿色 build14 的声明 `arithmeticTensorDifferentGenerator_mul_mem_arithmeticTupleValuationIntegerLattice`，但该文件当前在 line 684 处编译失败，不能整体 import；
- 因此这里只给出 type-level 的 `p^d` 形式，不声称已有证明。

### 5.3 项目 S853 的 missing input（不是原文）

```lean
/-- 项目 S853 需要的正向包含 `O_hol <= F(0)`。
    原文没有这个无 shift 的包含；原文只有 `p^d * O_hol <= F(0)`。 -/
def S1645ProjectOhol_le_Fzero : Prop :=
  s839HolomorphicLattice (l := l) T b <= s853FractionalZero (l := l) T b
```

### 5.4 项目 S841/S863 的 absorption 充分条件（不是原文）

```lean
/-- 项目 S841 的 pointwise/submodule absorption:
    `F(c) * O_hol <= F(c)`。这不是 IUT IV 的命题；
    在 principal one-factor 模型里它等价于 `O_hol <= F(0)`。 -/
def S1645ProjectAbsorption : Prop :=
  s839FractionalLattice (l := l) T b * s839HolomorphicLattice (l := l) T b <=
    s839FractionalLattice (l := l) T b
```

### 5.5 原文 Route C 的局部系数/区域比较（S1567 已证）

```lean
/-- 原文 q/Θ 局部比较的系数形式: `cRoot <= cQ`。
    这是 S1087CoeffLe，S1567 已证。 -/
def S1645OriginalRouteCCoeff : Prop :=
  ∀ i : qVFamTensorV,
    paperRootCoefficientFamily (l := l) T b i <= qVFamPureCoefficient T b i

/-- 原文 q/Θ 局部比较的区域形式:
    `qPilotQ1URegion ⊆ paperLambdaORegion cRoot`。
    由 S1087CoeffLe 与 fractional lattice 的 antitone 性推出；
    它不是 `F(0) <= O_hol`，也不是 `O_hol <= F(0)`。 -/
def S1645OriginalRouteCLocalRegion : Prop :=
  qPilotQ1URegion (l := l) T b <=
    paperLambdaORegion (l := l) T b (paperRootCoefficientFamily (l := l) T b)
```

### 5.6 原文 IUT III Cor. 3.12 的全局陈述（目标；无证明）

```lean
/-- 原文 IUT III Cor. 3.12 的 signed log-volume 比较:
    `-|log(Θ)| >= -|log(q)|`，
    在项目中写成 `qPilotSignedLogVolume <= thetaHullSignedLogVolume`。
    这是全局 hull 的 log-volume 比较，不是 lattice inclusion。 -/
def S1645OriginalCor312
    {V : Type uv} [Fintype V]
    {I : Theorem311Source.OriginalInput.{ua, uv, upi, umon, ui} l V}
    (R : ∀ v : V, I.SourceImageRealization v)
    (n : Theorem311Source.OriginalInput.ThetaPilotCarrier l) : Prop :=
  I.qPilotSignedLogVolume <= thetaHullSignedLogVolume (I := I) R n
```

等价的现成声明是 `LeanFormal.IUT.XiFPaper.GlobalThetaHullVsQPilotComparisonActual.qPilotThetaHullComparison`；该文件只证明

```lean
qPilotThetaHullComparison ↔
  globalThetaHullLogVolume <= qPilotMagnitude
```

以及从 `GlobalComparisonCondition` 到 `qPilotThetaHullComparison` 的条件构造，没有证明这个比较本身。

### 5.7 原文 IUT IV Prop. 1.2(ii) 的精确局部陈述（已证）

现成定理（`FinitePlaceFractionalAbsorption.lean` lines 397–435）的签名是：

```lean
theorem arithmeticTuple_fractionalAbsorption_of_order
    (places : (i : ι) → V i → FinitePlaceAtPrime K p)
    (tuple : (i : ι) → V i) [Fintype ι] [DecidableEq ι]
    (istar : ι)
    (varpi : CommonPrimeCompletion (places istar (tuple istar)))
    (alpha delta : (i : ι) → CommonPrimeCompletion (places i (tuple i)))
    (hvarpi : varpi ≠ 0) (hα : ∀ i, alpha i ≠ 0) (hδ : ∀ i, delta i ≠ 0)
    (m : ℤ)
    (hm : (m : ℝ) <= localNormOrder p varpi -
      ∑ i, (localNormOrder p (alpha i) + localNormOrder p (delta i))) :
    ∃ r ∈ arithmeticTupleCanonicalUnitReference places tuple,
      arithmeticTupleTprod places tuple (Function.update 1 istar varpi) =
        ((p : ℚ_[p]) ^ m) •
          (arithmeticTupleTprod places tuple alpha *
            arithmeticTupleTprod places tuple delta * r)
```

这是原文 Prop 1.2(ii) 的带 shift 局部陈述：`ϖ = p^m · α · δ · r`，`r ∈ O_hol`。对应集合形式是

```
p^m · α · δ · O_hol  ⊇  ϖ · O_hol
```

而不是 `F(c) * O_hol <= F(c)`。它正是项目应当用于替代 `O_hol <= F(0)` 的原文局部输入；但它的 shift 是 `m = ⌊λ−d_I−a_I⌋`，不是 `0`。

---

## 6. 结论与建议

1. **不能按名字等同。** `F(0) <= O_hol` 是 IUT IV Prop. 1.1 的第二条 normalization 包含；Cor 3.12 的 Route C 不等式是全局 `−|log(Θ)| ≥ −|log(q)|`。前者是局部 `Z_p`-lattice 包含，后者是全局 holomorphic hull 的 log-volume 比较。对象、ambient、index、normalization、Ind 都不同。

2. **S853 的 `O_hol <= F(0)` 不是原文。** 原文是 `p^{d_{I*}} O_hol <= F(0)`。无 shift 版本一般更强；把它写成 "Route C basic inclusion" 只是项目命名。

3. **S1579 证明的是反向。** `F(0) <= O_hol` 已证，但不能推出 `O_hol <= F(0)`；两者同时成立会迫使 `F(0)=O_hol`，而项目明确计算 `[O_hol:O_tensor]` 是一个未必为 1 的有限 index。

4. **S841/S863 的 absorption 不是原文。** 原文对象是 normalized `F(c)*O_hol`；把 `F(c)*O_hol` 压回 `F(c)` 等价于 `O_hol <= F(0)`，不是 IUT IV 的命题。原文只给带 shift 的 `p^{d}O_hol <= F(0)`，由此得到的是 `F(c+d)*O_hol <= F(c)`，不是 `F(c)*O_hol <= F(c)`。

5. **Route C 的局部 actual 比较已经由 S1567 提供。** `S1087CoeffLe`（`cRoot <= cQ`）⇒ `qPilotQ1URegion ⊆ paperLambdaORegion(cRoot)`，这是当前项目中最接近原文 q/Θ 局部比较的 actual 结果；它和 `F(0)` 无关。

6. **Cor 3.12 仍是目标。** `qPilotThetaHullComparison` 只有条件构造，没有证明。不能用 `F(0) <= O_hol`、`O_hol <= F(0)` 或 `F(c)*O_hol <= F(c)` 冒充它。

建议的命名修正（不改代码，仅报告建议）：

- 把 `S1634RouteCBasicInclusion` 改名为 `S1634AbsorptionSufficientInclusion` 或 `S1634OholLeFzero`，避免 "Route C" 的歧义；
- 在 S853/S1570/S1574 的 docstring 中明确："this is a project sufficient condition for absorption, not the original IUT IV Prop. 1.1 shifted inclusion, and not Cor. 3.12"；
- 在 S1475/S1570 的 Route C 说明中，把 "product equality" 与 "q[1u] containment" 分开：前者是项目 compactness 输入，后者才是原文局部 q/Θ 比较的影子；
- 若要用原文局部输入替代 S853，应使用 `p^{d} O_hol <= F(0)`（或 `arithmeticTensorDifferentGenerator * O_hol <= F(0)`），并接受 shift `d`，而不是无 shift 的 `O_hol <= F(0)`。

---

## 附录 A. 源文本锚点

| 内容 | 文件 | 行 |
|---|---|---|
| IUT IV §1 导言 | `papers/motizuki_corpus/text/Inter-universal Teichmuller Theory IV.txt` | 391–395 |
| IUT IV Prop. 1.1 | 同上 | 400–450（核心 display 426–427） |
| IUT IV Prop. 1.2 | 同上 | 451–567（核心 display 508–518） |
| IUT IV Prop. 1.4 | 同上 | 656–821（核心 display 696–712，772–819） |
| IUT III Cor. 3.12 | `papers/motizuki_corpus/text/Inter-universal Teichmuller Theory III.txt` | 10324–10353 |
| IUT III Remark 3.9.5(i) holomorphic hull | 同上 | 7652–7680 |

## 附录 B. 本次审计文件的 SHA256（节选）

| 文件 | SHA256 |
|---|---|
| S839PaperRootMinimalProductCompactActual.lean | `A4E9F806A67AFDDAFA053E0F9040F8AF843B01B1965A4B8C9831403857F531D1` |
| S853OInFZeroAbsorptionActual.lean | `53CCFEA57BF57ACB9E29F8FCB2F853720B50FAC7F6E06A0271524ACC1DA13482` |
| S841FractionalCompactAbsorptionActual.lean | `B2642104B28E7F59D4A7AA0353CDA4F77655005B06438936BD1185488119D883` |
| S863ProductImageCompactActual.lean | `36BC7A09360F2FE16B3123B1EFADBED5EDDFADC7A92A6203172C0A6E622BA8C5` |
| S1475ReportCExactInputsActual.lean | `8AA83A4F36B78C65A8FBBD43821A3F7C7A28C49FB05DD0315125A46C5D015379` |
| S1567AbsNormNatGeneratorActual.lean | `ADE25099707F15B82F8C518A8E530F0EEB9FB1C4644F17F2E5036341A19B4BC2` |
| S1570ReportCInputsClosedActual.lean | `DBC1F31AD63A344D562D36DD9B984FC27F5F0083107F0BB2C9CC76DB9792CAB5` |
| S1574ProductImageAbsorptionActual.lean | `E480AB2623EB0254EBB8DF7E94090B45B6F04B2718CAA03763263AEF0A036BF5` |
| S1579OLeFractionalZeroAnalysisActual.lean | `8C8B66B2689D01E134E4DDE44441F8B7765364C6246128191356C3577B71A6B8` |
| S1634OLeFractionalZeroActual.lean | `E1C5C52808171754FE3D3A66EE7D827B0EC75CD1E0CE806294E3F61E646F75A0` |
| FinitePlaceFractionalTensorLattice.lean | `ABB0A8D6C6EB447861FA0D903C16EBCB28D5B430567722360A00ADA4939C8C9E` |
| FinitePlaceNormalizedUnitScalingLogVolume.lean | `45C4A881FA8724A44029BDF9213E9886016D44CA7CD0EFD62947F232D21E7C6B` |
| FinitePlaceIntegerTensorComparison.lean | `E7E99ACD8C5FA0D76F3BDC4AFEFF564836844B5CC953F349E008348A818F5EDC` |
| FinitePlaceHolomorphicIntegralClosure.lean | `EF2DEF735F29CB5864F50E517094F2F47D8AFF4AC1E78DBB304AF4B7166F575A` |
| FinitePlaceFractionalAbsorption.lean | `40D0E3372CF8C1E33610D6CF6AF597C291FBFCE09D54F7758E0C2B744AAABF4D` |
| FinitePlaceStepVAssembly.lean | `864C372A59446E77BEEB40A1925E06487A2565B8E7BE729019943C8A6A192C03` |
| GlobalThetaHullVsQPilotComparisonActual.lean | `D93FEAB7F1938321874601758CA42DFEB86686A85BEF4878D6E8226C2865EA28` |
| IUT III text | `876EBC732CAD5DCA89C1446A6055018583512254E3FF5AB333797175EBE9181F` |
| IUT IV text | `8E6B47D21DC19E86FD4178895B773276573110FE3F16BF7E760E19F3188181FB` |

## 附录 C. 本次 statement probe

文件：`tmp/_S1645Probe.lean`

- 内容：仅 `def ... : Prop` 与 `#check`，没有 theorem、没有 inhabitant、没有 sorry/axiom。
- 命令：`lake env lean tmp/_S1645Probe.lean`。
- 结果：exit 0。
- 检查的命题类型：
  - `S1645OriginalProp11_RI_le_normalization`
  - `S1645OriginalProp11_primeShift`
  - `S1645ProjectOhol_le_Fzero`
  - `S1645ProjectAbsorption`
  - `S1645OriginalRouteCCoeff`
  - `S1645OriginalRouteCLocalRegion`
  - `S1645OriginalCor312`

该 probe 只证明这些命题类型能 elaborate，不证明任何命题为真。

---

## 附录 D. 一句话回传

`F(0) <= O_hol` 是 IUT IV Prop. 1.1 的局部 normalization 包含；S853/S1570/S1574/S1634 实际需要的 `O_hol <= F(0)` 不是原文（原文是 `p^{d_{I*}} O_hol <= F(0)`）；原文 Route C 的全局不等式是 Cor. 3.12 的 `−|log(Θ)| ≥ −|log(q)|`，其定义域是 possible images 的 holomorphic hull，不是单个 tensor block 的 lattice。三者不能按名字等同。
