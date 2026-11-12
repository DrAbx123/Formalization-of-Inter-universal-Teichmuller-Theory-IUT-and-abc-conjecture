# S1540: promachina snapshot 1fa orbicurve/fundamental-group 只读审计

日期：2026-10-31
快照：`D:\lean\vendor\promachina\snapshots\1fa6387f11fb6dc67eb618b8138e6bc64f56b039`
commit：`1fa6387f11fb6dc67eb618b8138e6bc64f56b039`（2026-08-05，Merge pull request #254）
工具链：Lean `v4.30.0`，Mathlib `v4.30.0`（快照 `lean-toolchain`、`lakefile.toml`）；本地工程为 Lean `v4.32.2`。
审计文件：`Iut/Foundations/Orbicurve.lean`、`SourceInitialThetaData.lean`、`EtaleThetaCovers.lean`、`OrbicurvePullback.lean`。
审计方式：只读源码/行号审计；未在快照内运行 `lake build`，未修改 `vendor/promachina`；用快照已有 `.olean` 直接做了 `#check`、`#print axioms`、类型类合成探针和一个环境扫描。临时文件只写在 `D:\lean\tmp`。

## 0. 结论摘要

| 问题 | 判定 | 关键依据 |
|---|---|---|
| `OrbicurveEtaleFundamentalGroup` 是否有 actual inhabitant/constructor？ | **没有。** 只有 `structure` 和 `mk`，`mk` 需要 16 个字段。 | `Orbicurve.lean:854-938`；结果头扫描中该类型只有 `mk`，另有字段投影 `arithmetic`/`geometric`（来自 `OrbicurveFundamentalGroupData`）和反向 forgetful 的 `toEtaleFundamentalGroup`。 |
| `OrbicurveFundamentalGroupData` 是否有 actual inhabitant/constructor？ | **没有。** 只有 `structure` 和 `mk`，`mk` 需要 6 个字段；`exactSequence` 是输入数据的派生，不是构造器。 | `SourceInitialThetaData.lean:47-62`、`:71-76`；结果头扫描中该类型只有 `mk` 和字段投影（如 `SignQuotientOrbicurveData.xFundamentalGroups`），没有非投影构造器。 |
| `GaloisCategory` 是否有 target inhabitant？ | **对 orbicurve cover 没有。** 类本身在别处有实例（如 `ContAction`），但 `OrbicurveFiniteEtaleCover` 上连 `Category` 实例都没有。 | `SourceContinuousAnabelioid.lean:283-285` 是别处的实际实例；四个目标文件中只在 `Orbicurve.lean:766`、`:859-861` 作为结构字段出现（另有 `SourceInitialThetaData.lean:239` 字段访问）。 |
| `coverCategory` 的 identity/composition coherence 是否已构造？ | **没有。** 没有 `Category`/`CategoryStruct`，没有 `id`/`comp`，没有结合律/单位律；`coverMorphism_id`/`coverMorphism_comp` 只是证书字段（义务）。 | `Orbicurve.lean:526-534` 只有 `map` + `commutes`；`:894-907` 是字段；四个文件无 `CategoryStruct`、`id_comp`、`assoc` 的构造。 |
| 本地相邻障碍（非快照） | S405 的 `idMap` 只是 over-map 的 id；S1549 记录 `Category.{0,1}` 的 Hom 必须在 Type 0，而 `OrbicurveFiniteEtaleCoverMap : Type 1`；首缺是 small Hom carrier + equivalence + category structure。 | `tmp/sheaf/xif/paper/S405...:21-27`、`S1549...:37-45`、`coord/reports/S1549-cover-category-obstruction.md` |
| 能否从快照补 S1522？ | **不能。** 首缺字段是 `coverCategory` + `galoisCategory`；完整 `OrbicurveEtaleFundamentalGroup` 还要求 16 个字段，其下游 `OrbicurveFundamentalGroupData` 又要求两份这样的证书和一个 `OrbicurveScalarExtension`。 | 见 §6.1；快照没有 inhabitant，也没有可直接调用的构造定理。 |
| 能否从快照补 S1529？ | **不能直接补。** S1529 是条件归约，前提 `S1529CoverCategoryFirstMissing` + `S1529GaloisCategoryRemaining` 均未由快照提供。 | 见 §6.2；本地 `S1529OrbicurveGaloisCategoryActual.lean:31-99`；快照无 `Category.{0,1}` 实例。 |

一句话：**snapshot 1fa 给出的是 orbifold fundamental group 的接口/证书类型，不是 inhabitant；S1522/S1529 仍然停在此前 S1538 记录的 first missing field，本地 S1549 进一步把 coverCategory 的首缺细化为 small Hom carrier + universe 问题，快照没有改变这一点。**

判定口径：`structure` 自带的 `mk` 和字段投影不算 inhabitant；只有不依赖待填证书的 `def`/`instance` 或 `Nonempty` 证明才算。

## 1. 证据方法与全树检索

### 1.1 类型类探针

对任意 `X : HyperbolicOrbicurve F`，下面两条都以 `synthInstanceFailed` 失败（快照 Lean 4.30.0，导入 `Iut.Foundations.SourceInitialThetaData`）：

```lean
example (X : Iut.HyperbolicOrbicurve F) : Category (Iut.OrbicurveFiniteEtaleCover X) :=
  inferInstance

example (X : Iut.HyperbolicOrbicurve F) (G : ProfiniteGrp.{u}) :
    GaloisCategory (Iut.OrbicurveFiniteEtaleCover X) :=
  inferInstance
```

第一条失败信息是 `failed to synthesize instance ... Category ... (Iut.OrbicurveFiniteEtaleCover X)`；第二条在 `Category` 前提处失败。

### 1.2 环境结果头扫描

扫描导入闭包内所有常量的类型，剥掉 `forall`/`let` 后看结果头；与本题三个对象相关的结果只有：

```text
[ctor]    Iut.OrbicurveEtaleFundamentalGroup.mk
[def]     Iut.OrbicurveFundamentalGroupData.arithmetic
[def]     Iut.OrbicurveFundamentalGroupData.geometric
[def]     Iut.OrbicurveEtaleFundamentalGroup.coverCategory
[theorem] Iut.OrbicurveEtaleFundamentalGroup.galoisCategory
```

`arithmetic`/`geometric` 是 `OrbicurveFundamentalGroupData` 的字段投影；`coverCategory`/`galoisCategory` 是 `OrbicurveEtaleFundamentalGroup` 的字段投影。没有非投影的 `instance`/`def` 以 `Category (OrbicurveFiniteEtaleCover X)` 或 `GaloisCategory (OrbicurveFiniteEtaleCover X)` 为结果头；列出的是结构投影。

### 1.3 全树 grep 计数

| 模式 | 命中 | 说明 |
|---|---:|---|
| `Category.*OrbicurveFiniteEtaleCover` | 2 | 仅 `Orbicurve.lean:858`、`:861` 两个字段类型。 |
| `instance.*Orbicurve` | 0 | 无任何 orbicurve 相关实例声明。 |
| `CategoryStruct.*Orbicurve` | 0 | 无 `CategoryStruct`。 |
| `def .*coverCategory` / `instance .*coverCategory` | 0 / 0 | `coverCategory` 只作为字段和字段访问。 |
| `GaloisCategory.*OrbicurveFiniteEtaleCover` | 1 | 仅 `Orbicurve.lean:861` 的字段类型。 |
| `Nonempty.*OrbicurveEtaleFundamentalGroup` | 0 | 没有任何 `Nonempty` 断言。 |
| `Nonempty.*OrbicurveFundamentalGroupData` | 0 | 同上。 |
| `def .*OrbicurveEtaleFundamentalGroup` | 0 | 无构造器 `def`。 |
| `def .*OrbicurveFundamentalGroupData` | 0 | 无构造器 `def`。 |

### 1.4 公理检查

对快照的关键派生声明运行 `#print axioms`，结果均为 `[propext, Classical.choice, Quot.sound]`；没有 `sorryAx`。检查对象包括：`profiniteClosedSubgroupEmbedding`、`profiniteKernelEmbeddingOfSquare`、`profiniteKernelExactSequenceEmbedding`、`OrbicurveFiniteEtaleMorphismScalarExtension.resultCover`、`EtaleTheta.GroupExactSequence.projection_comp_inclusion`、`EtaleTheta.ArithmeticThetaQuotientData.geometric_quotient_is_derived`、`EtaleTheta.ThetaRootSplittingData.quotientByNegativeEigenspaceEquivCusp`、`OrbicurveEtaleFundamentalGroup.group`、`.toEtaleFundamentalGroup`、`OrbicurveFundamentalGroupData.exactSequence`。

四个目标文件 `grep` 也没有 `sorry`、`axiom`、`admit`。

## 2. 三个对象的实际声明

### 2.1 `OrbicurveEtaleFundamentalGroup`

`Orbicurve.lean:854-938`：

```lean
structure OrbicurveEtaleFundamentalGroup
    {F : Type u} [Field F]
    (X : HyperbolicOrbicurve F)
    (group : ProfiniteGrp.{u}) where
  coverCategory : Category.{u} (OrbicurveFiniteEtaleCover X)
  galoisCategory :
    letI := coverCategory
    @GaloisCategory (OrbicurveFiniteEtaleCover X) coverCategory
  baseScheme : SchemeOverField F
  basePoint : ...
  fiber : ...
  fiberFunctor : ...
  coverMorphism : ...
  coverMorphism_over : ...
  coverMorphism_bijective : ...
  coverMorphism_id : ...
  coverMorphism_comp : ...
  geometricFiberFintype : ...
  fiberIdentification : ...
  fiberIdentification_natural : ...
  action : ...
  isFundamentalGroup : ...
```

字段与行号：`coverCategory` `:858`、`galoisCategory` `:859-861`、`baseScheme` `:862`、`basePoint` `:863-866`、`fiber` `:867-869`、`fiberFunctor` `:870-873`、`coverMorphism` `:874-877`、`coverMorphism_over` `:878-885`、`coverMorphism_bijective` `:886-893`、`coverMorphism_id` `:894-899`、`coverMorphism_comp` `:900-907`、`geometricFiberFintype` `:908-912`、`fiberIdentification` `:913-917`、`fiberIdentification_natural` `:918-926`、`action` `:927-932`、`isFundamentalGroup` `:933-938`。

`#check` 显示它是 `Type (u+1)`，`mk` 恰好接收上述 16 个字段。没有 `def`/`instance` 返回这个类型；唯一的非投影声明是 `toEtaleFundamentalGroup`（`Orbicurve.lean:947-957`），它把现有数据忘成 `EtaleFundamentalGroup`，方向相反。`group`（`:960-963`）只是读回参数。

因此：**没有 inhabitant，也没有构造器；结构体本身只是证书类型。**

### 2.2 `OrbicurveFundamentalGroupData`

`SourceInitialThetaData.lean:47-62`：

```lean
structure OrbicurveFundamentalGroupData
    {F : Type u} [Field F]
    (X : HyperbolicOrbicurve F)
    (galois : ProfiniteGrp.{u}) where
  arithmeticGroup : ProfiniteGrp.{u}
  arithmetic : OrbicurveEtaleFundamentalGroup X arithmeticGroup
  projection : arithmeticGroup ⟶ galois
  projection_surjective : Function.Surjective projection
  geometricBaseChange : OrbicurveScalarExtension F (AlgebraicClosure F) X
  geometric : OrbicurveEtaleFundamentalGroup
    geometricBaseChange.result
    (closedSubgroupProfiniteGrp
      (profiniteKernelClosedSubgroup projection))
```

它的 `exactSequence`（`:71-76`）只是把 `profiniteKernelExactSequence` 作用在已有 `projection`/`projection_surjective` 上，不能反向构造数据。

它要求两个 `OrbicurveEtaleFundamentalGroup` 证书和一个 `OrbicurveScalarExtension`；后者本身也是 structure（`OrbicurvePullback.lean:84-92`），同样没有构造器。因此缺失是分层的，不是单一字段。

`SourceInitialThetaData` 中所有 `OrbicurveFundamentalGroupData` 出现（共 33 处）都是：结构定义、字段类型、变量假设，或字段投影。`SignQuotientOrbicurveData`（`:544-583`）、`TypeOneLTorsionStackRealization`（`:2621`）、`ThetaRootStackRealization`（`:5239`）等只是把该类型作为字段/参数。

### 2.3 `GaloisCategory`

`#check GaloisCategory` 的结果是：

```text
CategoryTheory.GaloisCategory.{u₁, u₂} (C : Type u₁) [Category.{u₂, u₁} C] : Prop
```

它是 `Prop` 类。快照中确实有别的 `GaloisCategory` inhabitant/实例，例如：

- `SourceContinuousAnabelioid.lean:283-285`：`continuousAction_galoisCategory : GaloisCategory (ContAction FintypeCat.{u} G)`，这是实际构造（先有 `continuousAction_preGaloisCategory` 和 `continuousAction_fiberFunctor`）。
- `SourceCombinatorialUniversalCover.lean:5385-5389`、`SourceGluedIsolatedGaloisLevelSystem.lean:40-42`：`local instance ... : GaloisCategory (...).Cover`，但它们只是从 anabelioid 结构字段投影，不是对 `OrbicurveFiniteEtaleCover` 的构造。
- `SourceGluedAnabelioid.lean:1955` 是 `PreGaloisCategory`，不是 `GaloisCategory`。

在审计的四个文件中，`GaloisCategory` 只出现在 `Orbicurve.lean:766`（`EtaleFundamentalGroup` 字段）和 `:859-861`（`OrbicurveEtaleFundamentalGroup` 字段），以及 `SourceInitialThetaData.lean:239` 的字段访问。**没有 `GaloisCategory (OrbicurveFiniteEtaleCover X)` 的实例/证明。**

## 3. `coverCategory` 与 identity/composition coherence

### 3.1 没有 `Category`，也没有 `CategoryStruct`

- `OrbicurveFiniteEtaleCover`（`Orbicurve.lean:518-523`）只有 `source`、`map`、`finiteEtale` 三个字段。
- `OrbicurveFiniteEtaleCoverMap`（`:526-534`）只有 `map` 和 `commutes`：

```lean
structure OrbicurveFiniteEtaleCoverMap
    {F : Type u} [Field F]
    {X : HyperbolicOrbicurve F}
    (source target : OrbicurveFiniteEtaleCover X) where
  map : source.source.Hom target.source
  commutes :
    Iso
      (Pseudofunctor.StrongTrans.vcomp map target.map)
      source.map
```

没有 `id`、`comp`、`assoc`、`id_comp`、`comp_id`。四个文件里 grep `CategoryStruct`、`id_comp`、`comp_id`、`assoc` 都没有 cover 相关的构造（只有 Mathlib 内部的 `Category.assoc` 用法）。

### 3.2 证书字段不是构造

`OrbicurveEtaleFundamentalGroup` 的 `coverMorphism_id`（`:894-899`）和 `coverMorphism_comp`（`:900-907`）确实在陈述 identity/composition 的 coherence：

```lean
coverMorphism_id :
  ∀ (cover : OrbicurveFiniteEtaleCover X),
    Iso (coverMorphism (𝟙 cover))
      (Pseudofunctor.StrongTrans.id cover.source.fiber)
coverMorphism_comp :
  ∀ {first second third} (f : first ⟶ second) (g : second ⟶ third),
    Iso (coverMorphism (f ≫ g))
      (Pseudofunctor.StrongTrans.vcomp (coverMorphism f) (coverMorphism g))
```

但它们是 `OrbicurveEtaleFundamentalGroup` 的字段，属于待填证书；快照没有给出 `coverMorphism`、`coverMorphism_over`、`coverMorphism_bijective` 的项，也没有给出 `Category` 的 `id`/`comp`。因此不能把这些字段当成已构造的 coherence。

### 3.3 可用的通用 bicategory 操作

`Pseudofunctor.StrongTrans` 有 `id`、`vcomp`、`whiskerLeft/Right`、`associator`、`leftUnitor/rightUnitor`（Mathlib `FunctorBicategory/Pseudo.lean`）。它们可以作为未来构造 cover category 的原料，但还需要：

1. 选定严格化方案：把 `OrbicurveFiniteEtaleCoverMap` 的 `commutes` 2-同构商掉，或证明它是 subsingleton/使用 proof-irrelevant 包装；
2. 证明 `id_comp`、`comp_id`、`assoc`，这些在 2-同构意义下成立，但未必是结构相等；
3. 证明 `coverMorphism` 与 `coverMorphism_id/comp` 的兼容。

这些都不在快照中。

### 3.4 本地相邻证据（不是快照）

本地已有两个直接针对该 gap 的包，结论与快照审计一致但更进一步：

- `tmp/sheaf/xif/paper/S405OrbicurveCoverCategoryActual.lean:21-27` 用 `Pseudofunctor.StrongTrans.leftUnitor` 构造了 `OrbicurveFiniteEtaleCover.idMap : OrbicurveFiniteEtaleCoverMap A A`。这证明 **over-map 层的 identity 可以写出来**；但它的类型仍是 `OrbicurveFiniteEtaleCoverMap`（Type 1），不是 `Category.{0,1}` 的 `id`。该文件把 `CategoryStruct` 和三条律显式记为 `OrbicurveCoverCategoryGap`（`:40-47`），没有伪造 Category。
- `tmp/sheaf/xif/paper/S1549OrbicurveCoverCategoryProofActual.lean:37-45` 记录了更强的 obstruction：S1522/S1529 要的是 `Category.{0,1} (OrbicurveFiniteEtaleCover X)`，其 Hom family 必须在 Type 0；实际 `OrbicurveFiniteEtaleCoverMap A B : Type 1`。因此不能把 over-map 类型直接当 Hom，首缺结构是 `S1549SmallHomFirstMissing`：

```lean
structure S1549SmallHomFirstMissing where
  Hom : S1549Cover l → S1549Cover l → Type
  homEquiv : ∀ A B, Hom A B ≃ S1549CoverMap A B
```

`coord/reports/S1549-cover-category-obstruction.md` 记录该文件 `EXIT=0`、无 `Category` inhabitant、无 fake Category。也就是说，即使补上 identity/composition 的 coherence，还要先解决 small Hom carrier + equivalence 的 universe 问题；S405/S1549 都是本地包，不是 snapshot 1fa 的内容。本审计未重新编译这两个文件，但其 olean 存在，报告记录为 checked。

## 4. 已构造的相邻内容（不是 inhabitant）

| 文件 | 实际内容 | 是否包含目标 inhabitant |
|---|---|---|
| `Orbicurve.lean` | stack/有限 étale cover 类型、sign action、profinite 基本群 exact sequence API；`EtaleFundamentalGroup`/`OrbicurveEtaleFundamentalGroup` 的字段类型。 | 否；只有结构、投影和通用引理。 |
| `OrbicurvePullback.lean` | 标量扩张 `EtaleStackScalarExtension`、`OrbicurveScalarExtension`、morphism/有限 étale 扩张、`resultCover`、2-笛卡尔方形接口。 | 否；`resultCover` 只把已有有限 étale 证书重新打包成 cover 对象，不构造 category 或 group data。 |
| `EtaleThetaCovers.lean` | `GroupExactSequence`、`ArithmeticThetaQuotientData`、`ArithmeticEllipticQuotientData`、`CuspidalThetaSequence`、`TypeOneLTorsionQuotient`、`InversionEigenspaceSplitting`、`ThetaRootSplittingData` 等群论接口和定理。 | 否；完全不依赖 `Orbicurve`/`GaloisCategory`。 |
| `SourceInitialThetaData.lean` | 334 个声明；把 `OrbicurveFundamentalGroupData` 作为大量结构的字段/参数，并派生 local/global source-theta 接口。 | 否；没有 `def` 构造 `OrbicurveFundamentalGroupData`，也没有 `OrbicurveEtaleFundamentalGroup`。 |

`SourceInitialThetaData` 的 `SourceInitialThetaCore`（`:5670-5783`）是一个超大的条件结构：`globalLTorsionCover`、`globalLTorsionStack`、`epsilon`、`finiteLocalCores`、`finiteLocalLTorsionCovers`、`badLocalStandard` 等全是字段；没有 `def` 或 `instance` 构造它。`grep 'def .*SourceInitialThetaCore'` 为 0。

## 5. 可移植声明与准确依赖

本节只列与 S1522/S1529 或移植入口相关的声明；四个文件的声明总数分别为 80、334、44、14（`Orbicurve`、`SourceInitialThetaData`、`EtaleThetaCovers`、`OrbicurvePullback`），完整名单可由源码 `grep` 复现。

### 5.1 Tier A：`Orbicurve.lean` 相对本地新增的三条 profinite 引理

本地 `Iut/Foundations/Orbicurve.lean` 与快照 1fa 的差异只有 4 个 hunk（从本地到快照约 110 insertions / 4 deletions），其中三条是新声明：

| 声明 | 快照行 | 作用 | 依赖（均在本文件内） |
|---|---:|---|---|
| `profiniteClosedSubgroupEmbedding` | `:1063-1093` | 把 `ProfiniteEmbedding` 限制到两个闭子群 | `ProfiniteEmbedding`、`closedSubgroupProfiniteGrp`、`ProfiniteGrp.ofHom`、`continuous_subtype_val` |
| `profiniteKernelEmbeddingOfSquare` | `:1099-1126` | 由交换方形诱导闭核之间的嵌入 | 上一条、`profiniteKernelClosedSubgroup` |
| `profiniteKernelExactSequenceEmbedding` | `:1289-1319` | 由交换方形构造 exact sequence embedding | 上两条、`profiniteKernelExactSequence`、`ProfiniteFundamentalExactSequenceEmbedding` |

另两处是证明/属性差异：`geometricFiberMap`（`:807-841`）的证明从 `component.toNatTrans ≫ rightUnitor.inv` 改成 `simpa using component.toNatTrans`；`HyperbolicOrbicurve.Hom.TwoCell.id/comp`（`:474-483`）去掉了 `noncomputable`。

这三条是本审计中最直接可移植的 delta：不新增文件依赖，补进本地 `Orbicurve.lean` 即可（4.32.2 下需要重新编译验证）。

### 5.2 Tier B：`EtaleThetaQuotient.lean` + `EtaleThetaCovers.lean`

- `EtaleThetaQuotient.lean` 1106 行、126 个声明；只 import Mathlib（`Group.TypeTags`、`ZMod`、`Commutator`、`QuotientGroup`、`ProfiniteGrp.Basic`、`Group.Extension` 等），不依赖 `Orbicurve`。它提供 `ModLThetaQuotient`、`modLThetaProjection(_surjective)`、`ModLEllipticAbelianization`、`modLThetaToElliptic`、`ModLThetaCenter`、`LagrangianQuotient`、`ProfiniteLagrangianQuotient`、`LTorsionLabel`、`lTorsionProfiniteGroup`、`NonzeroLabel`、`SignLabel`、`toSignLabel` 等。
- `EtaleThetaCovers.lean` 679 行、44 个声明；依赖 `Iut.Foundations.EtaleThetaQuotient` + `Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion`。它是纯群论层，不 import `Orbicurve`。

| 声明 | 行 | 依赖/作用 |
|---|---:|---|
| `profiniteTateGroup` | `:37-39` | `ProfiniteGrp.ProfiniteCompletion.completion`、`GrpCat.of`、`LiftedIntegerTateGroup` |
| `profiniteTateReduction` | `:57-62` | `ProfiniteCompletion.lift`、`integerTateReduction`、`lTorsionProfiniteGroup` |
| `TateFactorizedLagrangian` | `:87-95` | `profiniteTateGroup`、`profiniteTateReduction`、`ProfiniteLagrangianQuotient` |
| `GroupExactSequence` | `:98-105` | 群同态、`range = ker`；`projection_comp_inclusion` `:114-120` |
| `ArithmeticThetaQuotientData` | `:135-154` | `GroupExactSequence`、`ModLThetaQuotient`、`modLThetaProjection`、`modLThetaProjection_surjective` |
| `ArithmeticEllipticQuotientData` | `:189-211` | `ModLEllipticAbelianization`、`modLThetaToElliptic`、`ArithmeticThetaQuotientData` |
| `ArithmeticEllipticConjugationAction` | `:218-232` | `PiEll` 对 `ModLEllipticAbelianization` 的共轭作用 |
| `CuspidalThetaSequence` | `:239-260` | `ModLThetaCenter`、`GroupExactSequence`、`intoArithmetic` |
| `TypeOneLTorsionQuotient` | `:291-308` | `LagrangianQuotient`、`ArithmeticEllipticQuotientData`、`CuspidalThetaSequence` |
| `InversionEigenspaceSplitting` | `:372-405` | `ArithmeticEllipticConjugationAction`、`ModLEllipticAbelianization`、`LTorsionLabel`、`ModLThetaCenter` |
| `ThetaRootSplittingData` | `:517-546` | `InversionEigenspaceSplitting`、`CuspidalThetaSequence`、`galoisSection` |
| `CuspidalSignStructure` | `:632-650` | `CuspTheta` 上的对合、固定 theta center、在 Galois 商上平凡 |
| `SignCompatibleThetaRootSplitting` | `:656-677` | 上述 `root` 与 `sign` 的兼容 |

这个 Tier 可以在不碰 orbicurve 的情况下独立移植；它不会填 S1522/S1529，但可作为 `SourceInitialThetaData` 的群论依赖。

### 5.3 Tier C：`OrbicurvePullback.lean`

327 行、14 个声明；只依赖 `Iut.Foundations.Orbicurve` 和 `Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete`。

| 声明 | 行 | 作用/依赖 |
|---|---:|---|
| `SchemeOverField.restrictScalars` | `:28-32` | `Over.map (Spec.map ...)`；依赖 `Algebra F K` |
| `SchemeOverField.restrictScalarsPseudofunctor` | `:35-39` | `Functor.op.toPseudofunctor`；依赖 `LocallyDiscrete` |
| `EtaleStackScalarExtension` | `:48-57` | `result : EtaleStackOverField K` + `fiberEquivalence` |
| `OrbicurveGeometryScalarExtension` | `:66-81` | 目标 stack 等式 + genus/stackyOrders/punctures 保持 |
| `OrbicurveScalarExtension` | `:84-92` | `result` + `stackExtension` + `geometryExtension`；无构造器 |
| `OrbicurveScalarExtension.signature_preserved` | `:101-107` | 由三个保持字段推 signature 相等 |
| `OrbicurveScalarExtension.fiberEquivalence` | `:110-118` | 把 stack equivalence 搬到 `extension.result` |
| `OrbicurveMorphismScalarExtension` | `:131-172` | `result`、`restrictedMap`、`comparison` 2-同构 |
| `OrbicurveFiniteEtaleMorphismScalarExtension` | `:182-193` | `resultFiniteEtale` 证书 |
| `...resultCover` | `:209-216` | 仅把已有证书打包成 `OrbicurveFiniteEtaleCover targetExtension.result`；不是 category/group data |
| `OrbicurveSquare` | `:221-231` | 2-交换方形，字段是四个 `Hom` + `commutes` |
| `OrbicurveSquare.Cone` / `ConeMorphism` | `:241-263` | 伪锥及其 2-胞腔 |
| `OrbicurveSquare.TwoPullbackWitness` | `:275-324` | 双范畴 pullback 的 lift/liftToX/liftToY/liftTwoCell/twoCell_ext |

这些是 `SourceInitialThetaData` 的几何依赖，但全是条件接口；`resultCover` 是唯一实际产生 cover 对象的地方，仍需输入的有限 étale 证书。

### 5.4 Tier D：`SourceInitialThetaData.lean`

5970 行、334 个声明；import 快照 `EtaleThetaCovers`、`InitialThetaData`、`Orbicurve`、`OrbicurvePullback`、`SourceAnabelioid`、`SourceTateCurve` 和 4 个 Mathlib 模块。

本地当前缺失的文件（`D:\lean\Iut\Foundations` 下不存在）：`EtaleThetaQuotient.lean`、`EtaleThetaCovers.lean`、`InitialThetaData.lean`、`SourceTateCurve.lean`、`OrbicurvePullback.lean`、`SourceInitialThetaData.lean`。其中 `EtaleThetaQuotient`/`InitialThetaData`/`SourceTateCurve` 只依赖 Mathlib，移植成本主要在体量和 4.30→4.32 兼容。

| 文件 | 直接 import | 本地状态 |
|---|---|---|
| `Orbicurve.lean` | 13 个 Mathlib 模块 | 有旧版；需加 Tier A 三条引理 |
| `EtaleThetaQuotient.lean` | 7 个 Mathlib 模块 | 缺 |
| `EtaleThetaCovers.lean` | `EtaleThetaQuotient` + `ProfiniteGrp.Completion` | 缺 |
| `OrbicurvePullback.lean` | `Orbicurve` + `Functor.LocallyDiscrete` | 缺 |
| `InitialThetaData.lean` | Mathlib only | 缺 |
| `SourceTateCurve.lean` | 2 个 Mathlib 模块 | 缺 |
| `SourceInitialThetaData.lean` | 6 个 Iut 文件 + 4 个 Mathlib 模块 | 缺 |

| 声明 | 行 | 作用/依赖 |
|---|---:|---|
| `OrbicurveFundamentalGroupData` | `:47-62` | 目标 group data；依赖两个 `OrbicurveEtaleFundamentalGroup`、`OrbicurveScalarExtension`、`profiniteKernelClosedSubgroup` |
| `...exactSequence` | `:71-76` | 由 `projection`/`projection_surjective` 派生；依赖 `profiniteKernelExactSequence` |
| `OrbicurveFundamentalGroupScalarExtension` | `:89-120` | local-to-global pullback；依赖 `SourcePointedAnabelioidHom`、两份 group data、`ProfiniteEmbedding` |
| `...toExactSequenceEmbedding` | `:157-169` | 打包 geometric/arithmetic embedding + 两个 square |
| `OrbicurveFiniteEtaleCover.arithmeticOpenSubgroup` | `:233-256` | 由 `coverCategory`/`galoisCategory`/`fiberFunctor`/`action`/`isFundamentalGroup` 派生 stabilizer；正好消耗缺失证书 |
| `...geometricOpenSubgroup` | `:259-270` | 用 exact sequence inclusion comap |
| `OrbicurveFiniteEtaleFundamentalGroupIdentification` | `:282-302` | source/target group data + cover 的 fiber stabilizer 同构 |
| `OrbicurveCuspidalDecompositionData` | `:398-409` | `OrbicurveBoundaryCusp` + 闭分解子群 + restricted surjectivity |
| `SignQuotientOrbicurveData` | `:544-583` | 字段含 `xFundamentalGroups`/`cFundamentalGroups`；只是消费者 |
| `SourceThetaKCoreData` | `:1452-1459` | 标量扩张的 X_K/C_K；字段含 `orbicurveExtension` 等 |
| `SourceThetaFiniteLocalCoreData` / `SourceThetaInfiniteLocalCoreData` | `:1967-2000` / `:2119-2152` | 局部 core；均以 group data 为字段/参数 |
| `GlobalLTorsionCoverInput` | `:2398-2483` | 全局 l-torsion cover 输入；字段含 `piTheta`/`piEll`/`arithmeticTheta`/`lagrangian`/`thetaRoot` 等，并以 `orbicurves.xFundamentalGroups` 为参数 |
| `TypeOneLTorsionStackRealization` | `:2621-2756` | 条件 stack realization；`xFundamentalGroups`/`cFundamentalGroups` 字段 |
| `SourceInitialThetaCore` | `:5670-5783` | 超大条件结构；没有构造器 |

结论：`SourceInitialThetaData` 是**条件框架**，不是 group data 或 Galois category 的构造。`review-1fa6387f.json` 也把 `SourceInitialThetaData.lean` 列在 `conditionalFrameworks`，并明确 `decision: no bulk production import yet`。

### 5.5 工具链与移植约束

- 快照 Lean 4.30.0，本地 Lean 4.32.2；不能直接整文件覆盖。
- 本地已有 `vendor/promachina/patches/4.32.2/Orbicurve.patch`，但它对应的是上一快照 `0d52e0fd5b53` 到本地的两处旧差异（`TwoCell.id/comp` 的 `noncomputable`、`geometricFiberMap` 的 rightUnitor 写法），不包含 1fa 新增的三条 profinite 引理；需要新增 patch。
- 本地 `SourceAnabelioid.lean`/`GaloisImage.lean`/`GaloisComplement.lean` 是已打 4.32.2 patch 的版本，与快照 1fa 有少量证明/兼容差异（`SourceAnabelioid` 11 行差异、`GaloisImage` 6/8、`GaloisComplement` 5/45）；未在 4.32.2 下重新编译这些目标文件。
- 本审计未运行本地 4.32.2 移植构建，未生成新 `.olean` 到本地库；可移植性判断基于源码依赖和快照 4.30.0 的 olean 检查。

## 6. S1522/S1529 的准确判定

### 6.1 S1522

本地 `S1522OrbicurveEtalePiActual.lean:34-39` 的首缺类型是：

```lean
structure S1522GaloisCategoryFirstMissing where
  coverCategory : Category (Iut.OrbicurveFiniteEtaleCover (S1522Orbicurve l))
  galoisCategory :
    letI := coverCategory;
    @GaloisCategory (Iut.OrbicurveFiniteEtaleCover (S1522Orbicurve l)) coverCategory
```

它要求 `coverCategory` 和 `galoisCategory` 两个 inhabitant。快照 1fa 两者都没有。

完整 `S1522EtalePiRequired l G` 是 `OrbicurveEtaleFundamentalGroup (S1522Orbicurve l) G`；它至少要求 16 个字段，其中 `baseScheme`/`basePoint`/`fiber`/`coverMorphism`/`fiberIdentification`/`action`/`isFundamentalGroup` 等均无供给。

更下游的 `S1522GroupDataRequired l` 是 `OrbicurveFundamentalGroupData (S1419Orbicurve l) (AbsoluteGaloisProfinite (S1348K l))`，又要求两份 `OrbicurveEtaleFundamentalGroup` 和一个 `OrbicurveScalarExtension`。所以即使强行补上 category，S1522 仍缺 group data；二者都不是快照能提供的。

### 6.2 S1529

本地 `S1529OrbicurveGaloisCategoryActual.lean:31-32` 的首缺字段是：

```lean
structure S1529CoverCategoryFirstMissing (l : PrimeGeFive) where
  coverCategory : Category.{0, 1} (S1529Cover l)
```

其后 `S1529SourceG2`（`:35-37`）、`S1529OtherInputs`（`:40-48`）、`S1529GaloisCategoryRemaining`（`:76-83`）和条件构造 `S1529GaloisCategory`（`:86-91`）、`S1529S1522FirstMissing`（`:94-99`）都已写好；缺的只是前提 inhabitant。

快照没有 `Category.{0,1} (OrbicurveFiniteEtaleCover ...)` 实例，也没有 `S1529SourceG2`/`OtherInputs`/fiber functor 的构造。因此 S1529 仍是一个**条件归约**，不能从快照直接实例化。

### 6.3 能否补？

**不能从快照 1fa 补。** 需要的新构造按依赖顺序至少包括：

1. `Category (OrbicurveFiniteEtaleCover X)`：先解决 `Category.{0,1}` 的 Hom universe 问题（S1549：small Hom carrier + equivalence），再定义 `id`/`comp` 并证明单位律/结合律；`commutes` 是 2-同构数据，还需严格化/商化方案。
2. `PreGaloisCategory`（对这个 cover 范畴）：terminal、pullbacks、finite coproducts、finite-group quotients、mono direct summand；这些对象和 colimit 证书在快照中都没有。
3. `GaloisCategory`（对这个 cover 范畴）：还需要 fiber functor（`FiberFunctor`）和 `IsFundamentalGroup` 数据；`OrbicurveEtaleFundamentalGroup` 的对应字段目前只是类型。
4. 对 `OrbicurveFundamentalGroupData` 还要：arithmetic group、surjective projection、`OrbicurveScalarExtension F (AlgebraicClosure F) X`、以及几何侧的第二个 `OrbicurveEtaleFundamentalGroup`。

这是一个新的构造包，不是一个可用 `exact` 或 `inferInstance` 填的洞；S1522/S1529 不能因 snapshot 1fa 的移植而关闭。

## 7. 建议的下一步

1. **不要把 S1522/S1529 标为已补或可补。** 保持 open；S1538/S1522/S1529 的 first-missing 记录对 snapshot 1fa 仍准确。
2. 若要吸收 snapshot 1fa，先做 Tier A（三条 profinite 引理 + 两处小改）到本地 `Iut/Foundations/Orbicurve.lean`，再做 Tier B（`EtaleThetaQuotient` + `EtaleThetaCovers`，纯 Mathlib/群论），Tier C 次之。
3. `SourceInitialThetaData` 只在确有 downstream source-theta 消费者时移植；它不会填 S1522/S1529 的首缺字段，且体量大、工具链需 4.32.2 适配。
4. 若要真正推进 S1522/S1529，新建一个明确的构造包：先做 small Hom carrier + equivalence（S1549 的 first missing），再做 `Category` + coherence（可用 bicategory 的 `associator`/`unitor`，但必须处理 2-同构严格化），再做 `PreGaloisCategory`/`GaloisCategory`；在该包通过 `statement_compiles` + `proof_body_checked` 前，不把任何 `OrbicurveEtaleFundamentalGroup` 当作已构造。

## 8. 验收状态与复现

| 项目 | 状态 |
|---|---|
| 源码/行号审计 | 完成（四个目标文件 + 相关调用点） |
| 快照 olean 导入 | 完成（Lean 4.30.0，`Iut.Foundations.SourceInitialThetaData`） |
| `#check` / `#print axioms` / 类型类探针 | 完成 |
| 快照全树 grep | 完成 |
| 本地 4.32.2 移植构建 | 未运行 |
| `statement_compiles` / `proof_body_checked` / `kernel_closed` / `target_accepted` | 均未运行；本报告是只读审计，不是移植验收 |
| 本地 S405/S1549 | 未重新编译；引用其已有 olean 和 `coord/reports/S1549-cover-category-obstruction.md` |
| comparator / Project build / 独立审查 | 未运行 |

复现命令（快照 olean 已存在于 `.lake/build/lib/lean`）：

```powershell
# 1) 设置快照 LEAN_PATH（由 lake env 读出，省略号处为快照绝对路径）
$env:LEAN_PATH='<snapshot>\.lake\packages\...\lib\lean;...;<snapshot>\.lake\build\lib\lean;<elan>\lib\lean'
# 2) 运行探针（临时文件在 D:\lean\tmp，不写入快照）
lean D:\lean\tmp\audit_s1540_probe.lean
lean D:\lean\tmp\audit_s1540_scan.lean
lean D:\lean\tmp\audit_s1540_result.lean
lean D:\lean\tmp\audit_s1540_axioms.lean
```

文件指纹（SHA256）：

| 文件 | SHA256 |
|---|---|
| `Orbicurve.lean` | `B794AB60F0C4781F26CFC98CE5F8E92A55D98C4FD6086F231BBC26CF5A28933F` |
| `SourceInitialThetaData.lean` | `388B4716402369FDA29ED63EEBA3B453617598DCE53570B3C42ED1E4AFBC40B0` |
| `EtaleThetaCovers.lean` | `5E76BBE5721AA0D77260DAE453C51506392936025FDD91B0B4F31CEDDE0AC9CE` |
| `OrbicurvePullback.lean` | `7B4536C3F7083B65391DD788A290A69D7AAFE61A711029ACBDD2B823A3DB6269` |

相关本地证据：`tmp/sheaf/xif/paper/S1359OrbifoldPiActual.lean`（`:54-62` 明确“tree contains no inhabitant of OrbicurveEtaleFundamentalGroup”）、`tmp/sheaf/xif/paper/S1490OrbicurveFundamentalGroupActual.lean`（`:20-22`、`:197-258` 把目标精确归约到 first missing certificate）、`coord/reports/S1522-orbicurve-etale-pi.md`、`coord/reports/S1529-orbicurve-galois-category.md`、`coord/reports/S1538-orbicurve-cover-category.md`。另见本地相邻（非快照）证据 `tmp/sheaf/xif/paper/S405OrbicurveCoverCategoryActual.lean`、`tmp/sheaf/xif/paper/S1549OrbicurveCoverCategoryProofActual.lean`、`coord/reports/S1549-cover-category-obstruction.md`；它们记录 small Hom/universe obstruction，进一步支持“不能直接补”。本报告对 snapshot 1fa 的结论与这些本地记录一致。