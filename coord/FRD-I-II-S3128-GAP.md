# [FrdI-II] / IUTchI Def 6.13(i) 现状与 S3128 prestack 缺口

日期：2026-11-09。审计对象：Stage 3/4 Frobenioid/anabelioid 侧。

## 1. 论文对象（原文）

### 1.1 IUTchI Def 6.13(i) / Theorem A

- `papers/motizuki_corpus/text/Inter-universal Teichmuller Theory I.txt:735-780`
  - Theorem A：initial Θ-data 决定一个 Θ±ellNF-Hodge theater `†HT^{Θ±ellNF}`，
    “in essence, a system of Frobenioids”；
  - 对应的 D-Θ±ellNF-Hodge theater `†HT^{D-Θ±ellNF}`，
    “in essence, the system of base categories associated to the system of Frobenioids”；
  - base category 的具体对象是 connected finite étale coverings of X_K / orbicurve C_K 的 Galois category，
    并带 `F_l^{⋊±}` / `F_l^{⋇}` poly-action。
- `papers/motizuki_corpus/text/Alien Copies, Gaussians, and Inter-universal Teichmuller Theory.txt:3217-3218`
  - initial Θ-data 是 “somewhat complicated system of Frobenioids [cf. [IUTchI], Definition 6.13, (i)]”。

因此 Stage 4 的 Frobenioid 对象不是任意 Z/2 quotient sheaf，而是：

1. 一个 **base category D**（connected finite étale covers / Galois category）；
2. 一个 **model Frobenioid C**（[FrdI] Theorem 5.2）；
3. 一个按 Θ±ellNF 标签/place 组织的 **system of Frobenioids** 及其 base categories，
   带 gluing/poly-action（IUTchI Def 6.13(i)）。

### 1.2 [FrdI] Theorem 5.2

- `The Geometry of Frobenioids I.txt:4974-5045`：
  - `Φ : D → Mon` divisorial monoid；
  - `B : D → Mon` group-like monoid；
  - `DivB : B → Φ^{gp}` monoid homomorphism on D；
  - objects `(A_D, α)`，其中 `α ∈ Φ(A_D)^{gp}`；
  - morphisms `(degFr ∈ N_{≥1}, Base, Div, u)`，满足
    `degFr·α + Div = Φ(Base)(β) + DivB(u)`；
  - C 是 isotropic/model type 的 Frobenioid；
  - Theorem 5.2(ii) 给出 model Frobenioid。

### 1.3 [FrdI] Definition 1.3

Definition 1.3 的七个 axiom group 在 Lean 中逐字段对应
`Iut/Foundations/Frobenioid.lean:767` 的 `FrobenioidAxioms`：
baseRepresented, commonPreSteps, pullbackBaseSlices, frobeniusDegree,
coAngular, unitTransport, outgoing/incoming divisor, factorization,
preStep factorization, faithfulUpToUnits, isotropicHull 等。

## 2. 当前 Lean 实际对象（已存在，不是 S3128）

### 2.1 通用 model Frobenioid

- `Iut/Foundations/Frobenioid.lean:68`：
  `DivisorialMonoidOn D IsFSM`，含 `obj`, `pullback`, id/comp,
  characteristicallyInjective, fsmPullbackIsIso。
- `Iut/Foundations/Frobenioid.lean:897/915`：
  `PreFrobenioidPresentation`, `FrobenioidPresentation`（含 `axioms`）。
- `Iut/Foundations/SourceModelFrobenioid.lean:87`：
  `Input Phi`，含 `rationalFunctions : GroupLikeAddMonoidOn D IsFSM`,
  `divisor`, `divisor_natural`。
- `Iut/Foundations/SourceModelFrobenioid.lean:121/127`：
  `Object Phi` = `(base : D, divisorClass)`；
  `Hom Phi data` = `frobeniusDegree : ℕ+`, `base`, `divisor`,
  `rationalFunction`, `balance`。
- `Iut/Foundations/SourceModelFrobenioidAxioms.lean:193`：
  `frobenioidAxioms` 生成完整 `FrobenioidAxioms`。
- `Iut/Foundations/SourceModelFrobenioidPresentation.lean:25`：
  `frobenioidPresentation [IsConnected D] ... : FrobenioidPresentation`
  = [FrdI] Theorem 5.2(ii) 的 packaged endpoint。

### 2.2 具体有限 place 实例

- `Iut/Foundations/SourceFiniteStageModelFrobenioid.lean:35` `StageBase place`；
- `:360` `stageModelInput place : SourceModelFrobenioid.Input (stageDivisorialMonoidOn place)`；
- `:409` `stageModelPreFrobenioidPresentation place`；
- `:418` `stageModelFrobenioidPresentation place : FrobenioidPresentation`。

即：**实际 model Frobenioid 对象已落地**（对一个 finite place 的 finite-stage
base category 实例化），不是 S3128 的 Z/2 quotient sheaf。

## 3. 当前 S3128 presentation 是什么

- `tmp/sheaf/xif/paper/S3128QuotientSheafObjActual.lean:13`：
  `S3128ZMod2QuotientSheafObj` = points sheaf + Z/2 action + torsor + `mapPoint`。
- `tmp/sheaf/xif/paper/S3128QuotientSheafStrongActual.lean:13`：
  `S3128StrongHom` = pointsIso + equivariant + mapCompat。
- `tmp/sheaf/xif/paper/S3128StrongBaseChangeFunctorActual.lean:16`：
  `S3128StrongBaseChangeFunctor f` 是这些对象的 base change。

这是 **anabelioid / fiber-side 的 Z/2 quotient sheaf 模型**，
不是 Frobenioid：没有 D、Φ、B、DivB、degFr、Div、u、balance，
也没有 `FrobenioidAxioms` 或 `FrobenioidPresentation`。

### 3.1 prestack mapId/mapComp 的真实障碍

`S3128PrestackMapIdActual` build_guard EXIT=1（2026-11-09，log
`tmp/build-guard-logs/20261109-023348-d95ed62b.log`）：

```
line16 rw [Over.mapId_eq] motive is not type correct
```

根因：`baseChange (𝟙 U)` 的 `points` 被 precompose 到 `(Over.map (𝟙 U)).op`，
`mapPoint V p = A.mapPoint ((Over.map (𝟙 U)).op.obj V) p`；
identity functor 的 `mapPoint V p = A.mapPoint V p`。
构造 mapId 的 `mapCompat` 分量需要

```
A.mapPoint ((Over.map (𝟙 U)).op.obj V) p ≅ A.mapPoint V p
```

但 `S3128ZMod2QuotientSheafObj` 没有 `mapPoint` 对 Over 测试对象态射的自然性字段。
这是结构缺口，不是 tactic 问题。按 lead 决定：**不临时加 mapPoint_natural 字段**。

## 4. 差什么（S3128 presentation vs 论文实际对象）

| 论文要求 | S3128 prestack | 当前 Lean 实际对象 |
|---|---|---|
| base category D | 无 | `DivisorialMonoidOn D IsFSM` 的 D 参数 |
| divisorial monoid Φ | 无 | `DivisorialMonoidOn` |
| group-like B + DivB | 无 | `Input Phi.rationalFunctions`, `divisor`, `divisor_natural` |
| objects (A_D, α) | 只有 points sheaf/Z/2 torsor/mapPoint | `SourceModelFrobenioid.Object Phi` |
| morphisms (degFr, Base, Div, u) + balance | 只有 StrongHom | `SourceModelFrobenioid.Hom` |
| Frobenioid Def 1.3(i)-(vii) | 无 | `FrobenioidAxioms` + `frobenioidAxioms` |
| Theorem 5.2(ii) packaged | 无 | `frobenioidPresentation` |
| concrete finite place model | 无 | `stageModelFrobenioidPresentation` |
| system of Frobenioids / gluing / poly-action | 无 | 仍缺（只有单 place 单 model） |

结论：

1. **S3128 prestack 不是 [FrdI-II] 主线对象**；它与实际 Frobenioid 对象之间没有可用的
   bridge，且其 mapId 需要造 `mapPoint_natural` 空壳。应从主线移除/标为孤儿基础设施。
2. **实际 Frobenioid 对象已存在**：通用 `frobenioidPresentation` 和有限 place 实例
   `stageModelFrobenioidPresentation`。当前真正缺口是 IUTchI Def 6.13(i) 的
   **system**：多 place/多标签的 Frobenioid family、base categories family、
   gluing/poly-action；不是 S3128 的 mapId/mapComp。
3. 最小下一步 actual（不造壳）：
   - 为 `stageModelFrobenioidPresentation` 建立 place 族/标签族接口，
     并证明每个分量是实际 `FrobenioidPresentation`；
   - 或先在已有 `SourceFrobenioid*` 文件中找已有 base-change/transport 接口
     （`SourceFrobenioidBasePullbackLift` 等），把它们接到 system 的 gluing 数据；
   - 不再给 `S3128ZMod2QuotientSheafObj` 增加新字段。

## 5. 状态标记

```
S3128 prestack (Z/2 quotient sheaf)   = [FrdI-II] 基础设施缺口 / 孤儿，停止 mapId/mapComp
[FrdI] Thm 5.2 model Frobenioid        = ACTUAL（Iut/Foundations/SourceModelFrobenioidPresentation.lean）
finite place concrete model            = ACTUAL（SourceFiniteStageModelFrobenioid.lean:418）
IUTchI Def 6.13(i) system of Frobenioids = 未落（family/gluing/poly-action）
```
