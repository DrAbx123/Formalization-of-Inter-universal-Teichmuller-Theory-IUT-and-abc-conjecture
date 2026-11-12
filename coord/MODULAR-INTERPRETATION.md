# MODULAR-INTERPRETATION — q-pilot 是否具有模曲线解释 (A1098)

| field | value |
|---|---|
| Status | ANALYSIS (source-level audit; no Lean, no compile) |
| 结论 | **当前数据下 q-pilot 没有模曲线解释**：它是 Gaussian 整数环中的显式分数理想线丛（素数 5、2161），SourceDefinition31Data 的 orbicurve/torsion/sections/cusp 都是抽象 carrier/Prop，没有 E/K、full level 结构或 `Spec O_K → X(N)` 点。判定 **C（不能陈述/不蕴含）**；补 (D1)–(D6) 后才可能 A（GAP-MODPOINT） |

## 1. q-pilot line bundle 的源级构造（S2735）

```lean
abbrev S2735Arithmetic : InitialThetaArithmeticData l := gaussianInitialThetaArithmeticData l
noncomputable def qPilotIdeal : Ideal (SourceOK (A := S2735Arithmetic l)) :=
  gaussianFieldFivePrimePlus * gaussianFieldFivePrimeMinus *
    gaussianField2161Plus * gaussianField2161Minus
noncomputable def qPilotLineBundle : SourceLineBundle := (qPilotIdeal l : FractionalIdeal ...)
theorem qPilotIdeal_factorization : qPilotIdeal l = <the four Gaussian primes>
```
**事实**：q-pilot 是 `O_{Q(i)}` 中 π₅⁺π₅⁻π₂₁₆₁⁺π₂₁₆₁⁻ 型**分数理想**；
- 不含 q-展开/Fourier 系数；
- 不含椭圆曲线/模曲线/level 数据；
- 其支持（S2735IdealSupport/VbadSupport）是坏位集合，不是 cusp/level 结构。

## 2. SourceDefinition31Data 的几何字段（抽象，无模解释）

`SourceDefinition31Data`（SourceDefinition31Boundary.lean:667-690）字段：
```
arithmetic : InitialThetaArithmeticData l        (数域/位/范数数据)
selectedPlaces/badPlaces : Type u               (抽象类型索引)
reduction : SourceReductionClause ...            (bad/selected 分区 + 稳定/乘法归约 Prop)
torsion : SourceTorsionClause l                  (抽象 torsion carrier/order 数据)
orbicurve : SourceOrbicurveClause               (curve/puncturedCurve/cover/structureGroup +
                                                 exactSequence + cuspCount，均为抽象 Type/Prop)
sections : SourceSectionClause                  (valuationCarrier 间的 section/inverse 抽象数据)
cusp : SourceCuspClause                         (仅 epsilon, cuspScale : Real)
```
**关键**：`SourceOrbicurveClause`（:452-465）只有
`curve : Type`、`puncturedCurve : Type`、`cover : Type`、`structureGroup : Type`、
抽象映射与 `exactSequence`、`cuspCount : Nat`——**没有**：
- 椭圆曲线 `E/K`（或 `E/O_K` 模型）；
- full level `N` 结构 `E[N] ≅ (Z/N)²`；
- `Spec O_K → X(N)`/`Y(N)` 的点；
- q-展开/Fourier 系数（cusp 只有两个实数）。

## 3. S1487 Gaussian 数据

`S1487SourceData`（:400-424）用 `S1487Arithmetic := concreteGaussianInitialThetaArithmeticData l`
（K = Q(i)），`selectedPlaces = Unit`，`badPlaces := Bad`（任意有限类型），
`reduction.qParameter := q : Bad → ℝ` 由调用者给出；torsion/orbicurve/sections/cusp 均由通用构造填充。
**事实**：S1487 数据只是“Gaussian 算术 + 任意实 q-参数 + 抽象 clause”，
没有带 full level 结构的椭圆曲线，故也没有模曲线点。

## 4. 若要有模解释，需要新增的精确数据

```
(D1) E/K 椭圆曲线（K = Fmod，S1487 情形 K = Q(i)）及 O_K 整模型；
(D2) full level N 结构 α_N : E[N] ≅ (Z/N Z)²（N 与 l/ℓ 幂相关）；
(D3) 模点 x : Spec O_K → X(N)（等价于 (E, α_N) 的 K-点）；
(D4) Klein/Siegel 线丛 𝕂_{a,b} / 单位 g_a 在 X(N) 上的定义；
(D5) q-pilot 线丛 ≅ x^*𝕂_{a,b}（或 x^*g_a 的除子）的**显式同构**；
(D6) 归一化：x^* 的度量/arch 范数与我们的 `−sF·A`、det⊗M 归一化一致。
```
精确陈述（待 (D1)-(D6)）：
```
theorem qPilotLineBundle_modular_pullback :
  ∃ (x : Spec O_K → X(N)) (a b : (1/N Z)²),
    qPilotLineBundle ≅ x^* (𝕂_{a,b})   （或 = x^* g_a 的除子类）
```

## 5. 判定

| 子命题 | 类型 | 理由 |
|---|---|---|
| q-pilot = 模曲线/level 数据的拉回 | **C（当前不可陈述）** | 数据中无 E/K、level、X(N) 点 |
| 若补 (D1)-(D6) 后 | **A 条件** | 需要新增几何构造 + 同构证明 |
| 用 qPilotIdeal 的素数结构直接对应 Klein 参数 | **C** | 素数 5/2161 是理想因子，不是模参数 (a,b) |
| S1487 数据给出模点 | **C** | S1487 只有 Gaussian 算术 + 任意实 q |

**结论：当前 q-pilot 是纯算术分数理想，无模解释；Klein/Siegel 路线的映射半边缺少 (D1)-(D6)，
这是比 A1097 的 GAP-MODPOINT 更具体的源级缺口。**

## 6. Lean 签名草案

```lean
/-- Modular point data for a level-N interpretation (explicit data, no inhabitant). -/
structure ModularPointData where
  -- E/K with full level N structure and a modular point x : Spec O_K -> X(N)
  level : Nat
  fullLevel : Prop          -- alpha_N : E[N] ≅ (Z/N)^2
  modularPoint : Prop       -- x : Spec O_K -> X(N)
  kleinParams : Prop        -- (a,b) in (1/N Z)^2

/-- q-pilot line bundle as the pullback of a Klein line bundle (target statement). -/
def QPilotModularPullback (D : ModularPointData) : Prop :=
  True   -- placeholder: qPilotLineBundle ≅ x^* Klein_{a,b}
```

## 7. 建议

1. 不把模解释当作既有事实：当前分类 C；
2. 若继续 Klein 路线，需先新增 (D1)-(D6)（大型几何构造，可能超出当前 lane 范围）；
3. 否则保留 FEAS-KLEIN 的 arch 显式公式作为 LITERATURE 输入，但**不声称** q-pilot 有模解释；
4. 替代：继续 Step (xi-d) 的 determinant/localization 路线（我们的 det⊗M 簿记已 green）。