# S2069：curve étale fundamental group 仓库内 prior-research inventory

日期：2026-11-02。性质：**只读盘点 + tmp 探针**；不写大证明，不改生产源码，无新 `axiom`/`sorry`。
工作目录：`D:/lean`。报告路径按任务指定：`coord/reports/S2069-curve-pi1-inventory.md`。

---

## 0. 结论摘要（先给可执行结论）

1. **已经有真几何对象**：`puncturedEllipticCurveScheme K`（`Spec K[X,Y]/(Y²−X³+X)`）、`FiniteEtaleCover S`、几何 fiber 函子 `geometricFiberFunctor Ω x : FiniteEtaleCover X ⥤ Type u`、`curveEtaleFundamentalGroup := Aut (geometricFiberFunctor Ω x)`、`CurvePiOneData` 接口。全部是 actual 定义，不是 card。
2. **`PreGaloisCategory` 只差一个字段**：cover 范畴的 G1（终对象、pullback）、G2（有限余积）、G3（直和项）已经**证明**；唯一缺的是 `hasQuotientsByFiniteGroups`。本轮探针 `tmp/s2069/Probe5.lean` 已用「其余四字段 + 该字段作假设」**成功构造出 `PreGaloisCategory` 实例**（exit 0）。
3. **`Aut F` 的 profinite 证书是免费的**：Mathlib 已给任意 `F : C ⥤ FintypeCat` 的 `Aut F` 装上紧 Hausdorff、全不连通、拓扑群结构，因此 `ProfiniteGrp.of (Aut F)` 直接可用（探针已验证）；`PreGaloisCategory.IsFundamentalGroup F (Aut F)` 是现成 instance（只需 `[GaloisCategory C] [FiberFunctor F]`）。
4. **真正缺的只有两块**：(a) `FiberFunctor` 证书本身（几何 fiber 的**有限性** + 保有限极限/余极限/满射/反映同构）；(b) **曲线 → 全 Galois 范畴/算术投影** 的几何定理（含 `π₁(X) ↠ G_K` 的满射性、`π₁^geo` 的识别）。现存 card 一个都没有 inhabitant。
5. **两处必须修的语义缺陷**（不是数学缺口，是接口写坏了）：
   - `CurveEtaleFundamentalGroupCard`（Example36CurveScheme.lean:294-314）**没有任何字段绑定到某条曲线**：它只有 `coverCategory : Type u`，既没有 `S : Scheme`，也没有与 `FiniteEtaleCover (curveScheme K)` 的同构；文档却说它「是二 punctured 曲线的卡」。用任意 `B(G)` 即可「满足」它，因此它**不能**充当曲线 π₁ 的目标接口。
   - `PuncturedCurveGeometricPiCard.geometricConnectedness`（Example36FreeProfinitePi.lean:382）的类型经 `#print` 核实是 `CategoryTheory.IsConnected ↥(curveScheme K)`，即把 `Scheme` 的**特殊化预序**当成范畴看时的连通性，**不是** `ConnectedSpace`，更不是几何基变更 `X ×_K K̄` 的连通性。
6. **vendor/promachina 的 Tate/stable curve 条目**：`M1M3PaperLedger.lean` 第 759/773/783 行的说法在**冻结快照里有源码**（`SourceBadLocalStableReduction.lean` 等），但这些文件**不在当前 active 的 `Iut/` 树里**（`LeanFormal` 依赖的是根 `Iut/`）；而且即便在那里，constituent tame cover categories 仍是**输入**（`SourceTateNodalTameRealization`），不是由 scheme 构造。所以「曲线 → 覆盖范畴」这个函子在最先进快照里也不存在。

---

## 1. 本轮证据等级

| 记号 | 含义 | 本报告中的用法 |
|---|---|---|
| R | 只读源码（含行号），未编译 | 所有「文件里有此声明」的陈述 |
| O | `.lake/build/lib/lean/...olean` 存在（有构建记录，非本轮重编译） | 关键模块的存量绿色 |
| P | 本轮 tmp 探针 `lake env lean` 通过（exit 0） | 第 1 节末尾五个探针 |
| — | 未运行 | 全库 sorry/axiom 扫描、全 Project 构建、comparator |

存量 olean（抽查，均存在）：

    LeanFormal/IUT/Foundations/Geometry/CurveEtaleFundamentalGroup.olean        2026-10-19
    LeanFormal/IUT/IUTII/Frobenioid/Example36CurveScheme.olean                  2026-10-30
    LeanFormal/IUT/IUTII/Frobenioid/Example36CurveGaloisCategory.olean          2026-10-31
    LeanFormal/IUT/IUTII/Frobenioid/Example36EllipticCurveSourcePiCard.olean    2026-10-31
    LeanFormal/IUT/IUTII/Frobenioid/Example36EtalePiOneKernelRealization.olean  2026-10-30
    Iut/Foundations/SourceAnabelioid.olean                                      2026-08-11

**未做**：全库 `sorry`/`axiom` 扫描；`#print axioms`；Project 构建；源语义（IUT 原文）逐条核对。下面凡涉及「已证明」均指「源码中该定理体存在且模块有 olean」，不等于本轮 `kernel_closed` 验收。

本轮探针（`tmp/s2069/`，均 exit 0，除注明外）：

| 探针 | 内容 | 结果 |
|---|---|---|
| `Probe.lean` | `#print PuncturedCurveGeometricPiCard.geometricConnectedness` | 字段类型 = `CategoryTheory.IsConnected ↥(curveScheme K)`（预序范畴） |
| `Probe2.lean` | `pp.all` 展开同上；`#synth Category ↥(curveScheme ℚ)` | 实例来自 `Scheme.instPreorderCarrierCarrierCommRingCat` |
| `Probe3.lean` | `ProfiniteGrp.of (Aut F)`；`IsFundamentalGroup F (Aut F)` | 两者均可合成（后者需 `[GaloisCategory C]`） |
| `Probe4.lean` | 两套 `FiniteEtaleCover` 的定义相等性 + 跨定义搬运 `HasPullbacks` | 两条 `rfl` 均通过；`finiteEtaleCoverHasPullbacks S` 可直接用作 `Geometry.FiniteEtaleCover S` 的实例 |
| `Probe5.lean` | 以 G2 为唯一假设构造 `PreGaloisCategory (FiniteEtaleCover S)` | 通过 |
| `Probe3.lean` 初次 | 未 import `ProfiniteGrp.Basic`；`IsFundamentalGroup` 误以为只需 `PreGaloisCategory` | exit 1，记录为「`Aut F` 的 `IsFundamentalGroup` 需要 `GaloisCategory` 而非仅 `PreGaloisCategory`」 |

---

## 2. 文件 / 声明映射表

### 2.1 生产几何基础

| 文件 | 声明 | 行 | 内容 | 状态 |
|---|---|---|---|---|
| `LeanFormal/IUT/Foundations/Geometry/CurveEtaleFundamentalGroup.lean` | `puncturedEllipticEquation` | 58 | `Y² − X³ + X` | R/O |
| 同上 | `puncturedEllipticCoordinateRing` | 63 | `K[X,Y]/(eq)` | R/O |
| 同上 | `puncturedEllipticCurveScheme` | 68 | `Spec` 上述环 | R/O |
| 同上 | `puncturedEllipticCurveStructureMorphism` | 73 | 到 `Spec K` | R/O |
| 同上 | `finiteEtaleCoverProperty` | 83 | `Etale ∧ IsFinite` | R/O |
| 同上 | `FiniteEtaleCover X` | 87 | `Over X` 的 full subcategory，`Type (u+1)` | R/O（与 §2.2 定义 defeq，见 Probe4） |
| 同上 | `finiteEtaleCoverForget` / `finiteEtaleCoverScheme` / `finiteEtaleCoverStructure` | 95/100/104 | 遗忘与结构映射 | R/O |
| 同上 | `geometricFiberObject Ω x Y` | 112 | `{s : Spec Ω ⟶ Y // s ≫ f = x}` | R/O |
| 同上 | `geometricFiberMap` | 119 | postcomposition | R/O |
| 同上 | `geometricFiberFunctor Ω x : FiniteEtaleCover X ⥤ Type u` | 127 | **Type 值**，非 `FintypeCat` | R/O |
| 同上 | `curveEtaleFundamentalGroup Ω x := Aut (geometricFiberFunctor Ω x)` | 139 | 普通群，无 profinite | R/O |
| 同上 | `CurvePiOneData` | 155 | `Pi G piToGalois piToGalois_surjective comparison geometricKernel geometricKernel_eq` | R/O |
| 同上 | `CurvePiOneData.geometricKernel_eq_bot_iff` | 175 | 核平凡 ↔ 投影单射 | R/O |
| `…/Geometry/CurveEtaleFundamentalGroupExt.lean` | `puncturedEllipticOriginPoint` | 62 | 原点几何点（任意 `K → Ω`） | R/O |
| 同上 | `puncturedEllipticOriginFiberFunctor` / `…FundamentalGroup` | 68/74 | 上述特化 | R/O |
| `…/Geometry/SplitTateCurve.lean` | `splitTateWeierstrassCurve` 等 | 50+ | 语义上「项目真正的 concrete 模型是 `y²+xy=x³+5`，`y²=x³−x` 只是 generic test curve」 | R/O |

### 2.2 Galois 范畴基础（Example36 线）

| 文件 | 声明 | 行 | 内容 | 状态 |
|---|---|---|---|---|
| `…/Frobenioid/Example36EtaleCoverFoundations.lean` | `IsFiniteEtaleHom` / `FiniteEtaleCover S` | 64/69 | 第二套 `FiniteEtaleCover`（`Type (u+1)`） | R/O |
| 同上 | `etale_structureMap` / `finite_structureMap` / `mk` | 86/90/103 | 基础投影 | R/O |
| 同上 | `FiniteEtaleCover.pullback (g)` | 122 | 基变换函子（需 `HasPullbacksAlong g`） | R/O |
| 同上 | `FiniteGaloisSetCategory` + `GaloisCategory` + `IsFundamentalGroup` 实例 | 277-297 | `Action FintypeCat G_K` 的现成 Galois 结构 | R/O |
| 同上 | `FieldGaloisCorrespondence` | 330 | 域侧对应卡（`equivalence` + `specEssentialSurjectivity`） | 卡，无 inhabitant |
| `…/Example36CurveEtaleCovers.lean` | `curveAffineEtaleCovers` / `curveTwoPuncturedEtaleCovers` | 71/75 | 曲线/二 punctured 覆盖范畴 | R/O |
| 同上 | `terminalCover` / `curveCoordinateAlgebraCover` | 87/179 | 终覆盖、由有限 étale 代数造覆盖 | R/O |
| 同上 | `SchemeGaloisConnectednessCard (S)` | 199-216 | **绑定到 `S` 的卡**：`GaloisCategory (FiniteEtaleCover S)`、`fiber`、`FiberFunctor`、`fundamentalGroup`、`action`、`isFundamentalGroup`、`geometricPiOne`、`geometricConnectedness` | 卡，无 inhabitant |
| `…/Example36CurveGaloisCategory.lean` | `finiteEtaleCover_terminalCover_isTerminal` | 103 | G1 终对象（任意 `S`） | R/O |
| 同上 | `finiteEtaleCoverHasPullbacks` | 278 | G1 pullback（任意 `S`） | R/O |
| 同上 | `finiteEtaleCover_hasFiniteCoproducts` | 500 | G2 有限余积（任意 `S`） | R/O |
| 同上 | `finiteEtaleCover_monoInducesIsoOnDirectSummand` | 770 | G3 直和项 | R/O |
| 同上 | `CurvePreGaloisCategoryRemainingFields` | 330 | 唯一剩余字段 = `hasQuotientsByFiniteGroups` | 卡，无 inhabitant |
| `…/Example36CurveConnectedness.lean` | `CurveOncePuncturedGeometricConnectedness` | 278 | **定义为 `IrreducibleSpace X ∧ ConnectedSpace X`**（不是几何基变更） | R/O |
| `…/Example36CurveScheme.lean` | `CurveProjectiveClosureCard` | 268 | 射影闭包卡（Mathlib 无 `Proj`） | 卡 |
| 同上 | `CurveEtaleFundamentalGroupCard (K)` | 294-314 | `coverCategory/fiber/fundamentalGroup/action/isFundamentalGroup/geometricPiOne/geometricConnectedness` | 卡，**不绑定任何 curve** |
| 同上 | `CurveProjectiveClosureCardRealized` / `…GroupCardRealized` | 285/318 | `Nonempty card` | 未证 |

### 2.3 源 Pi / Tate / kernel 实现

| 文件 | 声明 | 行 | 内容 | 状态 |
|---|---|---|---|---|
| `…/Example36EllipticCurveSourcePiCard.lean` | `OncePuncturedEllipticCurve` / `sourceOncePuncturedEllipticCurve` | 195/201 | `(curve, isElliptic, puncture)` over `ℚ` | R/O |
| 同上 | `SourceCurvePiData X` | 211-252 | `sourceAnabelioid`、`piOne`、`arithmeticProjection`、满射、`geometricKernel`、`proTwoCompletion`、mod-2/4 层、`notSplitProductModel` | 卡，无 inhabitant |
| 同上 | `SourceFullTateModuleData` | 265-280 | `T_l`、`proTwoTateModule`、`fullTateModule`、component 嵌入 | 卡 |
| 同上 | `SourceCurvePiCard` / `FiniteLevelProductModelIsNotSourceCurve` | 293/302 | 顶层义务 + 非等同 | 卡 |
| 同上 | `IsFiniteAbelianProTwoLayer` 及层定理 | 137-161 | E[2]、E[4] 的有限交换 pro-2 事实 | 已证（R/O） |
| `…/Example36EtalePiOneKernelRealization.lean` | `localAbsoluteGaloisProfinite p` | 206 | `Gal(Q̄_p/Q_p)` 作为 `ProfiniteGrp` | R/O |
| 同上 | `reducedGeometricKernelModel := Z/2` | 221 | 参数化模型，**明确不是曲线的 π₁^geo** | R/O |
| 同上 | `prodFstKerMulEquiv` | 256 | 乘积第一投影核 ≃ 第二因子 | R/O |
| 同上 | `localTotalAnabelioid` / `localGeometricAnabelioid` / `localAnabelioidMorphism` | 295-307 | `B(Gal × Z/2)`、`B(Gal)`、pointed morphism | R/O |
| 同上 | `localAnabelioidDPrimeStrip` | 396 | 地点索引 `DPrimeStrip` | R/O |
| 同上 | `…_geometric_ne_bot` / `…_geometric_card` (=2) / `…_geometricMulEquiv` | 467/447/432 | **非平凡几何核的 actual 实现** | R/O |
| 同上 | `semidirectDPrimeStrip` 等（§9） | 592-752 | 半直积形 exact sequence、`G`-模核、affine action、torsor | R/O |
| 同上 | `anabelioidDPrimeStripOf`（§10） | 794 | pointed anabelioid → `DPrimeStrip Unit` | R/O |
| `…/Example36FreeProfinitePi.lean` | `freeProfiniteGroupTwo` | 96 | `FreeGroup (Fin 2)` 的 profinite completion | R/O |
| 同上 | `…_homEquiv`、`…_nontrivial`、`…_not_commutative` | 102/275/287 | 泛性质 + 非平凡 + 非交换（用 `S₃` 商） | R/O |
| 同上 | `freeProfinitePiGeometricAnabelioid := B(Π_geo)` | 313 | 候选 anabelioid（组为自由 profinite） | R/O |
| 同上 | `PuncturedCurveGeometricPiCard` | 348-382 | 绑到 `curveScheme K` 的卡：`baseSchemeIso`、`geometricBaseChange`、`galoisData : SchemeGaloisConnectednessCard`、fiber、`geometricAut`、`geometricPiOne`、`freeProfiniteIso`、`geometricConnectedness` | 卡，无 inhabitant；且 `geometricConnectedness` **型错**（见 §0.5） |

### 2.4 anabelioid API（可复用证书机器）

| 文件 | 声明 | 行 | 说明 |
|---|---|---|---|
| `Iut/Foundations/Orbicurve.lean` | `structure EtaleFundamentalGroup` | 763-783 | `Cover : Type (u+1)`、`Category.{u}`、`GaloisCategory`、`fiber : Cover ⥤ FintypeCat`、`FiberFunctor`、`group : ProfiniteGrp`、`action`、`IsFundamentalGroup` |
| `Iut/Foundations/SourceContinuousAnabelioid.lean` | `continuousActionEtaleFundamentalGroup G = B(G)` | 431 | 从已给 `G` 造 anabelioid |
| `Iut/Foundations/SourceAnabelioid.lean` | `SourcePointedAnabelioidHom` | 79-96 | pullback + 保有限极限/余极限 + `fiberIso` |
| 同上 | `certifiedFundamentalGroupEquiv` | 224 | `G ≃ₜ* Aut fiber`（需要证书） |
| 同上 | `fundamentalGroupHom` / `continuous_fiberAutHom` | 269/212 | **pointed morphism ⇒ 连续群同态** |
| 同上 | `fundamentalGroupHom_eq_conjugate` | 542 | 2-iso ⇒ 内共轭歧义（论文 Prop 1.1.4） |
| `Iut/Foundations/SourceGluedTotalAnabelioid.lean` | `SourceSemiGraphOfAnabelioids.totalAnabelioid` | 55+ | 半图 of anabelioids 的**总 Galois 范畴 + fiber functor**（组由 `Aut fiber` 派生） |
| `Iut/Foundations/SourceTateStableGraph.lean` | `sourceTateStableDualGraph` / `…CompactSemiGraph` | 37/48 | 只有组合半图（一顶点、一 node、一 marked open edge） |
| `Iut/Foundations/SourceTateStableBoundary.lean` | `SourceTateStableBoundary` | 16-44 | 稳定约化边界（曲线、图、切线多项式） |

### 2.5 Mathlib 侧证书 API（版本 `v4.32.2`）

| 文件 | 声明 | 行 | 说明 |
|---|---|---|---|
| `Mathlib/CategoryTheory/Galois/Basic.lean` | `class PreGaloisCategory` | 66 | 5 字段：terminal / pullbacks / finite coproducts / quotients by finite groups / mono ⇒ direct summand |
| 同上 | `class FiberFunctor` | 83 | 6 字段：terminal / pullbacks / finite coproducts / epis / quotients / reflects isos |
| 同上 | `class IsConnected` | 102 | 对象级连通（非初始 + 无真子对象） |
| 同上 | `class GaloisCategory` | 420 | `PreGaloisCategory` + `∃ fiber functor` |
| `…/Galois/IsFundamentalgroup.lean` | `class IsFundamentalGroup` | 231 | `IsNaturalSMul` + Galois 对象传递 + `ContinuousSMul` + 单射性 |
| 同上 | `instance : IsFundamentalGroup F (Aut F)` | 251 | **只需 `[GaloisCategory C] [FiberFunctor F]`** |
| 同上 | `toAutMulEquiv` / `toAutHomeo` | 270/281 | `G ≃* Aut F`、`G ≃ₜ Aut F` |
| `…/Galois/Topology.lean` | `autEmbedding`、`CompactSpace`、`T2Space`、`TotallyDisconnectedSpace`、`IsTopologicalGroup` | 43-125 | `Aut F` 天然是 profinite 空间（对任意 `F : C ⥤ FintypeCat`） |
| `…/Galois/Examples.lean` | `Action FintypeCat G` 的 Galois 结构 | — | 现成模型（项目已用） |

---

## 3. 三张清单：可直接填 / 需证书 / 真缺

### 3.1 可直接由 `FiniteEtaleCover + fiber functor` 填（不依赖曲线几何的新定理）

| 目标字段 / 声明 | 填法 | 依据 |
|---|---|---|
| `CurvePiOneData.geometricKernel` | 直接取 `D.piToGalois.hom.toMonoidHom.ker` | 定义即投影核（CurveEtaleFundamentalGroup.lean:168-170） |
| `CurvePiOneData.geometricKernel_eq` | `rfl` | 同上 |
| `…geometricKernel_eq_bot_iff` | 已证 | 同上 175 |
| `CurveEtaleFundamentalGroupCard.action` | `Aut F` 逐纤维作用 | 现成：`MulAction (Aut F) (F.obj X)` |
| `…fundamentalGroup` | `ProfiniteGrp.of (Aut F')`（`F'` 为 `FintypeCat` 值版本） | Probe3；Mathlib Topology.lean |
| `…isFundamentalGroup` | `inferInstance` | IsFundamentalgroup.lean:251（**但前提是已有 `GaloisCategory` + `FiberFunctor`**） |
| `SchemeGaloisConnectednessCard.geometricPiOne` | 可填 `ProfiniteGrp.of (Aut F_geo)` **作为模型** | 同上；语义上仍不等于已证的 `π₁^geo` |
| `SourceCurvePiData.sourceAnabelioid` | 可填 `⟨Cover, …, Aut F, action, instance⟩`（`EtaleFundamentalGroup` 结构） | Orbicurve.lean:763 |
| `…proTwoCompletion` / `modTwoLayer` 等**形状** | 可先取 `freeProfiniteGroupTwo` 的商/`ZMod 2` 层作候选 | 但 `SourceCurvePiData` 的 `piOne` 未定，不能先填 |
| `localAnabelioidDPrimeStrip` 全部 | **已经 actual** | Example36EtalePiOneKernelRealization.lean:396-481 |
| `PreGaloisCategory` 的 4 个字段 | 生产文件中已有定理，可直接搬运 | Probe4 证明两套定义 defeq；Probe5 组装成功 |

### 3.2 需要证书（`PreGaloisCategory` / `FiberFunctor` / `IsFundamentalGroup` / `ProfiniteGrp`）才能填

| 需要的东西 | 证书内容 | 现状 |
|---|---|---|
| `GaloisCategory (FiniteEtaleCover X)` | `PreGaloisCategory` + `∃ F, FiberFunctor F` | G2 缺；`FiberFunctor` 缺 |
| `FiberFunctor (geometricFiberFunctorFintype Ω x)` | 6 条保持性 + 反映同构 | 全部缺；且函子当前是 `Type` 值 |
| `IsFundamentalGroup F (Aut F)` | Mathlib instance | **免费**，但依赖上两行 |
| `π₁(X) ⟶ G_K` 的 `ProfiniteGrp.Hom` | 连续群同态 | 可由 `continuous_mapAut_whiskeringLeft`（SourceAnabelioid.lean:38）+ fiber iso 造出，**尚未有人对曲线写过** |
| `G ≅ Gal(K̄/K)` | 域侧 `FieldGaloisCorrespondence`（或 `FiberAutomorphismSurjectivityCard`） | 已证 `G_K ↪ Aut F`（单射）、缺满射（Example36FiberAutomorphism.lean:153-206） |
| `SourceCurvePiData.arithmeticProjection_surjective` | 几何连通 ⇒ 满射 | 缺（见 §3.3 M4） |

### 3.3 真缺（genuinely missing，按依赖顺序）

| 编号 | 缺口 | 精确陈述（Lean 级） | 现有最好碎片 |
|---|---|---|---|
| **M1** | 有限群商（G2） | `∀ (G : Type u) [Group G] [Finite G], HasColimitsOfShape (SingleObj G) (FiniteEtaleCover S)` | 仿射基座：`quotientCoverOfDiagram`、`actionCoconeOfDiagram`（AffineBaseFiniteEtaleQuotients.lean:178/258）；cocone 的全性质被归约到 gluing-diagram 的 `IsColimit` 假设（GlobalQuotientActionCoconeIsColimit.lean:89-104）。**全库无无条件实例/定理**（grep `HasColimitsOfShape (SingleObj G)` 只得 10 处，全是 card 或条件式）；残余义务有三个**重复**的具名 Prop：`CurvePreGaloisCategoryRemainingFields.hasQuotientsByFiniteGroups`、`GlobalQuotientCoconeResidual`（在 GlobalQuotientUniq.lean:120 与 GlobalQuotientUniversalProperty.lean:81 **各定义了一份**），三者陈述相同、互不相连 |
| **M2** | 几何 fiber 有限 | `Finite (geometricFiberObject Ω x Y)`（`Ω` 可分闭） | 无。可用料：`IsFinite` extends `IsAffineHom`（Mathlib Finite.lean:39）；`CommAlgCat.FiniteEtale.equivOfIsSepClosed`；`Scheme.Hom.finite_preimage` |
| **M3** | `FiberFunctor` 六条 | 保 terminal/pullback/有限余积/epi/有限群商，反映同构 | 无。项目已有 `finiteEtaleCover_hom_etale`、`…_finite`（CurveGaloisCategory.lean:141/149）可作为「覆盖间态射仍是有限 étale」的输入 |
| **M4** | 算术投影满射 | `Function.Surjective (π₁(X) → G_K)`（几何连通性定理） | 无陈述、无证明。项目只有 `ConnectedSpace (curveScheme K)`（K-模型）与 `IrreducibleSpace` |
| **M5** | 几何基变更连通性 | `ConnectedSpace (X ×_{Spec K} Spec K̄)` | 无。`PuncturedCurveGeometricPiCard` 里只有 `geometricBaseChange : Scheme` + `…Iso : geometricBaseChange ≅ curveScheme K`（把「基变更」直接写成原曲线，等于**没做**基变更） |
| **M6** | `π₁^geo` 的识别（自由 profinite 秩 2） | `Nonempty (π₁^geo ≅ freeProfiniteGroupTwo)` | `freeProfiniteGroupTwo` + 泛性质 + 非交换已证；识别完全缺（FreeProfinitePi.lean:74-79 自认） |
| **M7** | 射影（proper）模型 | `CurveProjectiveClosureCard` | Mathlib 无 `Proj`；只有仿射图表。**proper curve 的 π₁ 在本仓库目前不可陈述** |
| **M8** | 曲线 → anabelioid 函子 | `FiniteEtaleCover X ⥤ EtaleFundamentalGroup`（或等价地 `curve ↦ B(π₁)`） | 全库无。`B(G)` 只能从**已给** `G` 造（SourceContinuousAnabelioid.lean:431） |

---

## 4. 最短 construction path（一条，按可验证里程碑）

**总判断**：最短路径**不是**先做几何基变更或 `π₁^geo`，而是先把 `FiniteEtaleCover (curveScheme K)` 做成 `GaloisCategory`，因为一旦有 `FiberFunctor`，`Aut F` 的 `IsFundamentalGroup` 与 `ProfiniteGrp` 证书都是**免费**的（§3.1），`CurvePiOneData` 的 7 个字段里 4 个立刻可填。

### Step S1（最小、几乎纯 bookkeeping）：把 fiber functor 搬到 `FintypeCat`

目标（建议文件 `…/Geometry/CurveGeometricFiberFintype.lean`）：

    noncomputable def geometricFiberFunctorFintype
        {X : Scheme.{u}} (Ω : Type u) [Field Ω]
        (x : Spec (CommRingCat.of Ω) ⟶ X) :
        FiniteEtaleCover X ⥤ FintypeCat.{u}

    theorem geometricFiberFunctorFintype_comp_incl :
        geometricFiberFunctorFintype Ω x ⋙ FintypeCat.incl =
          geometricFiberFunctor Ω x

    noncomputable def curveEtaleFundamentalGroupProfinite :
        ProfiniteGrp.{u+1} :=
      ProfiniteGrp.of (Aut (geometricFiberFunctorFintype Ω x))

    theorem curveEtaleFundamentalGroup_autEquiv :
        Aut (geometricFiberFunctorFintype Ω x) ≃ₜ*
          Aut (geometricFiberFunctor Ω x)

复用：`PreGaloisCategory.autEquivAutWhiskerRight`（`FintypeCat.incl` 是 `Full`+`Faithful`，见 `Mathlib/CategoryTheory/FintypeCat.lean:56-59`）。
**这一步把现有 `curveEtaleFundamentalGroup` 升级成 profinite 而不改其定义**，是本路径的关键技巧。
风险：低（只需 `Functor.ext` + `FintypeCat.comp_apply`）。

### Step S2（唯一的新数学入口）：G2 —— 有限群商

目标：`instance finiteEtaleCover_hasQuotientsByFiniteGroups (S) : ∀ G, …`
最短子路线（曲线是仿射 `Spec R`，所以**所有**覆盖都是仿射）：

1. 覆盖 `Z : FiniteEtaleCover (Spec R)` ⇒ `IsAffineHom Z.structureMap` ⇒ `Z.carrier` 仿射，`Γ(Z,⊤)` 有限 étale `R`-代数（`finiteEtaleCoverSections_etale/_finite`，AffineBaseFiniteEtaleQuotients.lean:27/43）。
2. 有限群 `G` 作用在 `Γ(Z,⊤)` 上（`coverSectionsMulSemiringAction`，已存在）。
3. 取不变量子代数 `Γ(Z,⊤)^G`，用 `ConstantRankFixedPoints.fixedPointSubalgebra_finiteEtale_of_local`（已存在）证其有限 étale，得商覆盖 `Spec (Γ^G) → Spec R`（`affineQuotientCoverGeneral`，已存在）。
4. **唯一未闭合点**：`SingleObj G ⥤ FiniteEtaleCover (Spec R)` 的 colimiting 性质。现有 `CoconeUniversal` 与 `IsColimit` 的等价已证（GlobalQuotientActionCoconeIsColimit.lean:48），但 `GluingCoconeReduction.glueIsColimit` 仍是假设字段（:89）。需把 gluing diagram 的 `IsColimit` 真做出来。
风险：**中高**（这是本路径最重的一步，但已有 90% 的周边）。

> 若只想尽快跑通 end-to-end 声明链：可先把 S2 作为**具名 sorry 定理**（SHEAF 允许），下游全部保持未闭合并登记，而不是造 card。

### Step S3：`FiberFunctor` 证书（M2 + M3）

目标：`instance geometricFiberFunctorFintype_fiberFunctor : PreGaloisCategory.FiberFunctor (geometricFiberFunctorFintype Ω x)`，其中 `Ω` 取可分闭（`SeparableClosure K` 或 `AlgebraicClosure K`）。

子目标：
- `Fintype (geometricFiberObject Ω x Y)`（M2）。推荐路线：把 lift 集等同于 `(pullback f x).Hom (Spec Ω) …` 的截面集；覆盖 `Y ×_X Spec Ω` 有限 étale over `Spec Ω` ⇒ 仿射 `Spec A`，`A` 有限 étale `Ω`-代数 ⇒ `A ≃ Ω^n`（`equivOfIsSepClosed`）⇒ 截面数 `n`。
- 保 terminal / pullback / 有限余积：三处都是「纤维的纤维 = 纤维」的集合双射，直接构造 equiv。
- 保 epi：覆盖间 epi 在有限 étale 情形等价于底层满射（需要一条引理），再证满射 ⇒ 纤维上满射。
- 反映同构：若 `f_Ω` 双射，则 `f` 的度数为 1；有限 étale + 度 1 ⇒ iso（需要「连通基上有限 étale 的纤维基数常值」这一条）。
风险：中；这是 SGA1 的核心，但不需要新概念。

### Step S4：`GaloisCategory` 与 `Aut` 打包

    instance curveGaloisCategory : GaloisCategory (FiniteEtaleCover (curveScheme K))
    instance curveFiberFunctor : PreGaloisCategory.FiberFunctor (geometricFiberFunctorFintype …)
    instance curveIsFundamentalGroup :
        PreGaloisCategory.IsFundamentalGroup (geometricFiberFunctorFintype …)
          (Aut (geometricFiberFunctorFintype …)) := inferInstance
    def curvePiOneProfinite : ProfiniteGrp := ProfiniteGrp.of (Aut …)

此时 `CurvePiOneData` 可填：`Pi := curvePiOneProfinite`，`G := …`，`geometricKernel := ker`（`rfl`），`comparison := (curveEtaleFundamentalGroup_autEquiv).toEquiv`。
`SchemeGaloisConnectednessCard` 亦可填（除 `geometricPiOne` 的语义外）。

### Step S5：算术投影（`Pi ⟶ G`）

对 `g := curveSchemeStructureMap K`：`FiniteEtaleCover.pullback g : FiniteEtaleCover (Spec K) ⥤ FiniteEtaleCover (curveScheme K)`（已存在，EtaleCoverFoundations.lean:122）。
再证自然同构 `(geometricFiberFunctorFintype Ω x) ∘ (pullback g) ≅ geometricFiberFunctorFintype Ω (x ≫ g)`（纤维积的万有性质，直接构造）。
于是 `Aut F_X →* Aut F_{Spec K}`（precomposition + `continuous_mapAut_whiskeringLeft`，SourceAnabelioid.lean:38），即 `ProfiniteGrp.Hom`。
**满射性（M4）仍是真定理**，不能由这套机器自动得到；建议单独立 DAG 节点（几何连通性 ⇒ 满射）。

### Step S6（可选、最后）：识别 `G ≅ G_K` 与 `π₁^geo`

依赖既有 `FieldGaloisCorrespondence K`（card）与新的 M5/M6。**不建议**作为第一里程碑。

---

## 5. 建议 Lean 文件骨架（stage 2 陈述，可直接放进 `tmp/sheaf/s2069/`）

`S1FintypeFiber.lean`：

    import LeanFormal.IUT.IUTII.Frobenioid.Example36CurveGaloisCategory
    import LeanFormal.IUT.Foundations.Geometry.CurveEtaleFundamentalGroup
    import Mathlib.CategoryTheory.Galois.IsFundamentalgroup
    import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
    import Mathlib.CategoryTheory.Galois.Topology

    noncomputable section
    open CategoryTheory AlgebraicGeometry

    namespace LeanFormal.IUT.Foundations.Geometry

    universe u
    variable {X : Scheme.{u}} (Ω : Type u) [Field Ω]
      (x : Spec (CommRingCat.of Ω) ⟶ X)

    /-- 几何点处几何 fiber 的有限性（M2）：可分闭 Ω 下每个有限 étale 覆盖的 lift 集有限。 -/
    theorem geometricFiberObject_finite [IsSepClosed Ω] (Y : FiniteEtaleCover X) :
        Finite (geometricFiberObject Ω x Y) := by
      sorry

    /-- FintypeCat 值几何 fiber 函子（对象层面与 geometricFiberFunctor 相同）。 -/
    def geometricFiberFunctorFintype [IsSepClosed Ω] :
        FiniteEtaleCover X ⥤ FintypeCat.{u} where
      obj Y := FintypeCat.of (geometricFiberObject Ω x Y)
      map f := FintypeCat.homMk (geometricFiberMap f)
      map_id Y := by sorry
      map_comp f g := by sorry

    /-- 与既有（Type 值）函子的定义关系。 -/
    theorem geometricFiberFunctorFintype_comp_incl [IsSepClosed Ω] :
        geometricFiberFunctorFintype Ω x ⋙ FintypeCat.incl =
          geometricFiberFunctor Ω x := by
      sorry

    /-- 既有 curveEtaleFundamentalGroup 的 profinite 化（不改其定义）。 -/
    noncomputable def curveEtaleFundamentalGroupProfinite [IsSepClosed Ω] :
        ProfiniteGrp.{u+1} :=
      ProfiniteGrp.of (Aut (geometricFiberFunctorFintype Ω x))

    theorem curveEtaleFundamentalGroup_autEquiv [IsSepClosed Ω] :
        Aut (geometricFiberFunctorFintype Ω x) ≃ₜ*
          Aut (geometricFiberFunctor Ω x) := by
      sorry

    end LeanFormal.IUT.Foundations.Geometry

`S2PreGalois.lean`（G2 唯一假设 → 完整 `PreGaloisCategory`，**本轮的组装已在 `Probe5` 验证可行**）：

    import LeanFormal.IUT.IUTII.Frobenioid.Example36CurveGaloisCategory

    open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

    namespace LeanFormal.IUT.IUTII.Frobenioid.Example36

    /-- G2：有限群商（M1，唯一剩余字段）。 -/
    theorem finiteEtaleCover_hasQuotientsByFiniteGroups (S : Scheme.{u}) :
        ∀ (G : Type u) [Group G] [Finite G],
          HasColimitsOfShape (SingleObj G) (FiniteEtaleCover S) := by
      sorry

    noncomputable instance finiteEtaleCover_preGaloisCategory (S : Scheme.{u}) :
        PreGaloisCategory (FiniteEtaleCover S) where
      hasTerminal := (finiteEtaleCover_terminalCover_isTerminal S).hasTerminal
      hasPullbacks := finiteEtaleCoverHasPullbacks S
      hasFiniteCoproducts := finiteEtaleCover_hasFiniteCoproducts (S := S)
      hasQuotientsByFiniteGroups := fun G _ _ =>
        finiteEtaleCover_hasQuotientsByFiniteGroups S G
      monoInducesIsoOnDirectSummand :=
        finiteEtaleCover_monoInducesIsoOnDirectSummand

    end …

`S3CurveGalois.lean`：

    /-- 曲线覆盖范畴的 fiber functor 证书（M3）。 -/
    instance curve_geometricFiberFunctor [IsSepClosed Ω] :
        PreGaloisCategory.FiberFunctor (geometricFiberFunctorFintype (X := curveScheme K) Ω x) := by
      sorry

    /-- 于是曲线覆盖范畴是 Galois 范畴，Aut 是 certified π₁。 -/
    instance curve_galoisCategory (K : Type u) [Field K] [IsSepClosed Ω] :
        GaloisCategory (FiniteEtaleCover (curveScheme K)) :=
      ⟨_, ⟨inferInstance⟩⟩

    instance curve_isFundamentalGroup [IsSepClosed Ω] :
        PreGaloisCategory.IsFundamentalGroup
          (geometricFiberFunctorFintype (X := curveScheme K) Ω x)
          (Aut (geometricFiberFunctorFintype (X := curveScheme K) Ω x)) :=
      inferInstance

    /-- CurvePiOneData 的可填版本（geometricKernel 用 rfl）。 -/
    noncomputable def curvePiOneDataOfGalois [IsSepClosed Ω]
        (hsurj : Function.Surjective (piToGaloisCandidate …)) :
        CurvePiOneData (X := curveScheme K) Ω x := …

---

## 6. 语义 / 工程风险（必须先处理，否则会「假完成」）

1. **`CurveEtaleFundamentalGroupCard` 无几何绑定**（Example36CurveScheme.lean:294-314）。它只有 `coverCategory : Type u`，没有 `S`、没有 `≅ FiniteEtaleCover (curveScheme K)`，且 `Type u` 与 `FiniteEtaleCover S : Type (u+1)` **连宇宙都对不上**。结论：**不要**把它当作源 Pi 的目标；若要保留，必须先加 `base : Scheme` + `coverCategoryIso : coverCategory ≅ FiniteEtaleCover base` 字段，否则任何 `B(G)` 都能满足它。
2. **`geometricConnectedness` 型错**（Example36FreeProfinitePi.lean:382）。实际类型 = `CategoryTheory.IsConnected ↥(curveScheme K)`，即特殊化预序作为范畴的连通性。它与 `ConnectedSpace`、与 `X ×_K K̄` 连通都不同。项目另有一处定义 `CurveOncePuncturedGeometricConnectedness := IrreducibleSpace X ∧ ConnectedSpace X`（Example36CurveConnectedness.lean:278），也**只是 K-模型**的连通性。二者都不能替代「几何连通」。
3. **两套 `FiniteEtaleCover`**：`Geometry.FiniteEtaleCover`（fiber functor 用它）与 `EtaleCoverFoundations.FiniteEtaleCover`（所有 Galois 字段定理用它）。本轮 Probe4 证明二者 **definitionally equal**（两条 `rfl` 通过），且 `finiteEtaleCoverHasPullbacks` 可直接用于前者。→ 好消息：不需要移植 780 行；坏消息：目前**没有任何桥文件/注释**说明这一点，容易重复劳动。建议加一条永久的 `example`/`theorem FiniteEtaleCover_eq` 记录 defeq。
4. **`curveEtaleFundamentalGroup` 定义在 `Type` 值函子上**，因此：`Group` 实例有、profinite 结构没有、`IsFundamentalGroup` 不能直接套。必须先做 S1。
5. **proper vs punctured**：`curveScheme K = E \ {O}`（仿射）是源；`curveTwoPuncturedScheme K = E\{O,P}` 是额外对象（Example36CurveScheme.lean:238-259）。射影闭包 `CurveProjectiveClosureCard` 无 inhabitant（Mathlib 无 `Proj`）。因此「proper curve 的 π₁ = prod_l T_l(E)」在本仓库**连陈述对象都还没有**；`SourceCurvePiCard` 的 docstring 只是文献说明，不是形式化定理。
6. **vendor 快照与 active `Iut/` 版本不一致**：`vendor/promachina/snapshots/1fa6387f…` 有 `SourceBadLocalStableReduction.lean`，根 `Iut/` 没有；且同一文件 `SourceAnabelioid.lean` 在两处 sha256 不同（root `f45d287e…`，vendor `0a94538c…`）。→ 想复用 ledger 里宣称的 Tate 稳定约化构造，必须先做版本合并，不能直接 copy。
7. **`SourceCurvePiData` 的 `notSplitProductModel`** 是「否定性字段」，若将来真造出 `sourceAnabelioid`，这条会变成需要**证明**的实质命题（现在只是卡的字段）。别把它当装饰。

---

## 7. 未运行 / 未验证（诚实边界）

- 未运行：全 Project 构建；`#print axioms`；全库 `sorry`/`admit` 扫描；comparator；独立语义审查。
- 未做：IUT 原文（I/II §3-6、III Example 3.6）逐条页码核对；本报告的「源锚点」全部沿用现有文件 docstring。
- 未验证：`Probe.lean`–`Probe5.lean` 的 `kernel_closed`（只验证了 elaboration 成功）。
- 未证明：本报告 §5 骨架里的所有 `sorry`（它们是**陈述**，不是完成）。

## 8. 一个可执行下一步

> 取 `S1FintypeFiber.lean`：先只证 `geometricFiberObject_finite`（M2）与 `geometricFiberFunctorFintype_comp_incl`。这一步不依赖 G2，可独立完成，完成后 `curveEtaleFundamentalGroup` 立刻拥有 profinite 结构，`CurvePiOneData` 的 `Pi`/`comparison` 两个字段就有真对象可填。
