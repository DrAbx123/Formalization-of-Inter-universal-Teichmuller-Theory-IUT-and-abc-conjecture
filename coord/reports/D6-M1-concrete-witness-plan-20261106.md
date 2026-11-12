# D6-M1：把 `X.finiteEtale.baseChange` 暴露为 S2512/S2514 concrete witness —— 最小改动评估

> 日期：2026-11-06（Asia/Shanghai）
> 性质：**只读分析**。本文件不写任何 Lean、不运行任何构建、不修改任何源码。
> 版本说明：本稿取代同日 03:53 的短稿（已备份为 `D6-M1-concrete-witness-plan-20261106.prev-short-draft.md`）。短稿的有效部分（S2622 的 identity 情形、import-cycle 警告、paper-level wrapper 选项）已并入本稿；短稿把 M1 设为 `cancelRight/cancelWitness` 的路线，本稿 §1.4/§5 论证其**同-apex 版本对一般 cover 不可实例化**。
> 证据基准：附录 A 的 SHA256（2026-11-06 03:55 前后采样）。标 [进行中/未验证] 的文件可能已被并行任务改写。
> 术语：已实现/编译 = 工作区存在 .olean 且源码已核对；仅类型 = 有 def ... : Type 但无 inhabitant；拟新增 = 本文建议但尚未创建。

---

## 0. 结论摘要（TL;DR）

1. **"暴露字段"本身不需要任何新字段。** `X.finiteEtale.baseChange` 已经是结构字段的投影（Iut/Foundations/Orbicurve.lean:344 的 baseChange；EtaleStackFiniteEtaleMorphism 只是它的 abbrev，:360）。缺的不是可访问性，而是该字段**没有携带** S2512/S2514 见证额外满足的 coherence。

2. **S2512/S2514 的 "concreteness" 在树里已有精确名字。** 它们的弱记录（EtaleStackBaseChangePresentation + TwoPullbackWitness）之外，还满足：
   - S1852ConeEssSurj（满 2-万有性质，S1852CoherentCoverActual.lean:166），打包为 StrongEtaleStackBaseChangePresentation（:220）与 StrongEtaleStackFiniteEtaleMorphism（:237）；
   - 等价地，S2558LiftUnique / S2559HasLiftUnique（S2558ConcreteWitnessPlanActual.lean:44 / S2559ConcreteWitnessRefinementPlanActual.lean:35）。
   二者在"同一 square + 同一 witness"上等价（本文 §2.2 的 N0 桥接引理），但树里**没有**这个桥接。

3. **该性质不能从抽象 baseChange 推出。** S1850 的 doubled presentation 是同一个 identity 映射的合法弱 presentation，却不满足满 2-万有性质，于是：
   - S1852NotFirstMissing（S1852CoherentCoverActual.lean:212）；
   - S2100NotGPresentationConeEssSurj（S2100GPresentationConeEssSurjActual.lean:116）；
   - S2281NotAllCoversStrong（S2281ActualCoverStrongActual.lean:34）。
   因此"把抽象 baseChange 暴露成 concrete witness"只能以**谓词假设**（或把 cover 限制到具体构造的类）实现，不能靠展开定义。

4. **树里已经有这个谓词**：S1866StrongCoverOf Y := ∃ M : StrongEtaleStackFiniteEtaleMorphism Y.map, M.toWeak = Y.finiteEtale（S1866ApexCoherenceActual.lean:130），并已证明等价于"每个 recorded base change 都满足 S1852ConeEssSurj"（:134）。它**对 terminal cover 成立**（:169，经 S1854StrongOfS1762），**对一般 cover 不成立**（S2281）。

5. **S2618-S2623 的 M1（同 apex 右消去）是错误的 M1。** M1CancellationGoal（S2618M1CancellationGoal.lean:21）要求从 Qx.commutes : Iso (Qx.toSource;(m;y)) (Qx.projection;(ptY;y)) 得到 Iso (Qx.toSource;m) (Qx.projection;ptY)。这是 S2090PostcompCancellation（S2090StackCancellationObstructionActual.lean:39）的特例；S2090 明文记录它在一般 stack 态射下为假。几何上 X ×_Z T → X ×_Y T 只是单态射。S2622（**已编译**）把这条路线的正例精确化为：需要 2-同构 m;y ≅ m 与 ptY;y ≅ ptY；只有 y = 𝟙 时由 right unitor 提供（S2622:280/304，S2624:21）。一般 cover 没有这两个 2-同构。**正确的 M1 是 S2096 的 vertex unpasting**（S2096UnpastingStatement，S2096StackMorphismActual.lean:424）。

6. **最小改动方案**（不改 Orbicurve.lean，不改 S2512/S2514，不改 S2619/S2620 的接口）：
   - **N0** 桥接引理 S2558LiftUnique ↔ S1852ConeEssSurj（约 20-30 行）；
   - **N1** cospan 级 strong 假设（S1866StrongCoverOf 的逐 cover 形式，约 30-40 行）；
   - **N2** 在 Py 的 S1852ConeEssSurj 下证明 vertex unpasting（约 150-250 行，本方案的核心新数学）；
   - **N3** 条件式装配回 S2096BaseChangePresentationField → S2092 → S2087 → S2086CospanGMapFiniteEtale（约 80-150 行）。
   - 预计 **0 处核心结构字段改动**、约 300-450 行新文件；D6(c) 最终**条件**于所用 covers 的 S1866StrongCoverOf。

7. **唯一硬风险**：vertex unpasting 的 liftTwoCell 部分可能不止需要"满 2-万有性质"，而需要 comparison twist（S2118/S2120/S2125 记录的精确 API）。若如此，N1 的谓词必须加入 S2120FirstMissing（S2120PresentationTwistActual.lean:354），且 S2512/S2514 实例是否满足它**尚未验证**。S2125 已证明 strong field 在 recorded lift 上退化为 Nonempty (Iso l l)，不能约束 comparison 2-胞（S2125PresentationCoherentActual.lean 文件头）。

---

## 1. 对象与现状

### 1.1 定义链（Iut/Foundations/Orbicurve.lean，SHA 见附录 A）

```lean
structure EtaleStackBaseChangePresentation            -- :310
    (map : source.Hom target) (testScheme) (point) where
  pullbackScheme : SchemeOverField F
  projection : pullbackScheme ⟶ testScheme
  projectionMap : SchemeRepresentableMap projection
  toSource : StrongTrans (schemeRepresentableEtalePseudofunctor F pullbackScheme) source.fiber
  commutes : Iso (vcomp toSource map) (vcomp projectionMap.transformation point)
  isPullback : (mk toSource projectionMap.transformation map point commutes).TwoPullbackWitness

structure EtaleStackRepresentableMorphismProperty       -- :339
    (property : ∀ {S T : Scheme.{u}}, (S ⟶ T) → Prop) (map) where
  baseChange : ∀ (testScheme) (point), EtaleStackBaseChangePresentation map testScheme point
  hasProperty : ∀ (testScheme) (point), property (baseChange testScheme point).projection.left

abbrev EtaleStackFiniteEtaleMorphism map :=             -- :360
  EtaleStackRepresentableMorphismProperty (fun f => IsFinite f ∧ Etale f) map

structure OrbicurveFiniteEtaleCover X where             -- :518
  source : EtaleStackOverField F
  map : source.Hom X.stack
  finiteEtale : EtaleStackFiniteEtaleMorphism map

structure OrbicurveFiniteEtaleCoverMap source target where  -- :526
  map : source.source.Hom target.source
  commutes : Iso (vcomp map target.map) source.map
```

TwoPullbackWitness（:254）字段：lift、liftToX、liftToY、liftTwoCell、liftTwoCell_toX、liftTwoCell_toY、twoCell_ext。**没有** lift 唯一性，**没有** comparison 与锥 commutes 的相容方程（这正是 §0 第 2 条与第 7 条的全部内容）。

关键结构事实（本文反复使用）：**任何 presentation 的 apex 都是 representable stack** —— pullbackScheme 是 scheme，toSource 的定义域是 schemeRepresentableEtalePseudofunctor F pullbackScheme。所以"apex 上 2-胞是 subsingleton"对一切 presentation 无条件成立（S2512 的 S2512Modification_subsingleton，S2512StackOpenImmersionUB.lean:179，对任意域 F；S1726 专用版 S1897:261）。**但** S2125 同时证明：也正因如此，S1852ConeEssSurj 在 recorded lift 上退化为 subsingleton 命题，**无法**用来比较两个 comparison 2-胞。

### 1.2 "concrete witness" 的等级

| 等级 | 内容 | 树中的名字 | 是否由 baseChange 蕴含 |
|---|---|---|---|
| W0 | 弱记录：6 字段 presentation + 7 字段 witness | EtaleStackBaseChangePresentation（Orbicurve:310） | 是（定义） |
| W1 | lift 唯一性：同锥的任意两个 lift 2-同构 | S2558LiftUnique（S2558:44）、S2559HasLiftUnique（S2559:35） | **否**（S1850/S2100/S2281） |
| W2 | 满 2-万有：锥比较在 1-胞上本质满 | S1852ConeEssSurj（S1852:166）；打包 StrongEtaleStackBaseChangePresentation（S1852:220） | **否**（同上） |
| W3（更强，可能有需要） | comparison twist / cone-category ES + 2-胞满 | S2120PresentationLiftConeMor ∧ S2120PresentationTwoCellFull = S2120FirstMissing（S2120:325/342/354） | **否** |

W1 与 W2 等价（本文 §2.2 N0）。W3 严格强于 W2（S2120 文件头：W2 不给 twist）。S2512/S2514 的见证满足 W1/W2；S2512 是否满足 W3 尚未验证。

### 1.3 已记录的反例/障碍/工具（全部已编译）

| 事实 | 声明 | 文件:行 | 用途 |
|---|---|---|---|
| doubled presentation 是合法弱 presentation | S1850Doubled / S1850DoubledFiniteEtale / S1850DoubledCover | S1850:363/370 | 证明弱记录不能确定 presentation |
| doubled 不满足满 2-万有 | S1852Doubled_not_coneEssSurj | S1852:542 | W2 非普遍 |
| doubled 不 strong | S1852Doubled_not_strong | S1852:559 | W2 不可由弱记录导出 |
| 全部 cover 都 strong 为假 | S2281NotAllCoversStrong | S2281:34 | 必须用假设 |
| 任意弱 presentation 的 W2 为假 | S2100NotGPresentationConeEssSurj | S2100:116 | 不能对 baseChange 全称量化 W2 |
| 后复合不可右消去 | S2090PostcompCancellation（仅类型，"false in general"） | S2090:39 | S2619 路线的不可行性 |
| W2 在 recorded lift 上退化 | S2125 文件头与 S2125PresentationStrongFieldAtLift_* | S2125 | liftTwoCell 需要 W3 的风险 |
| **两条 base 腿的 2-同构可搬运 witness** | **S2622IsoWitness** | **S2622:217** | M1-a 的正例工具；也用于任何"同 apex、换基腿"的 transport |
| y = 𝟙 的 M1 witness 与 presentation | m1RightCancellationWitnessId / rightCancellationId / presentationOfId | S2622:272/280/304 | identity 正例；一般 y 未得 |
| y = 𝟙 的 RightCancellation（重复实现） | idRightCancellation | S2624:21 | 与 S2622 的 rightCancellationId 等价；并行重复 |

### 1.4 两个必须区分的 "M1"

| 版本 | 精确陈述 | 位置 | 判定 |
|---|---|---|---|
| **M1-a：同 apex 右消去** | ∀ Qx, Iso (Qx.toSource;m) (Qx.projection;ptY)（commutes 由 Qx.commutes 右消去得到） | M1CancellationGoal，S2618:21；RightCancellation，S2619:25；M1RightCancellationWitness，S2620:26 | **不可用于一般 cover**。S2090 记录为假；几何上 X ×_Z T 到 X ×_Y T 是单态射。S2622 的恒等情形证明需要 2-同构 m;y ≅ m 与 ptY;y ≅ ptY（S2622:265-266 用 rightUnitor），一般 y 没有。S2624 只是 S2622:280 的重复。**唯一正例是 y = 𝟙（terminal cover）**。 |
| **M1-b：vertex unpasting** | 给定 y 的 presentation Py（point ptY;y）与 m;y 的 presentation Px（同 point），顶点方块 mk Px.toSource (Yoneda vertexMap) m Py.toSource 是 two-pullback | S2096UnpastingStatement，S2096:424 | **几何上正确**（B = X ×_Z T = X ×_Y (Y ×_Z T) = X ×_Y Py），未证明。vertex 图的 lift 只需 Py 的 W1/W2；liftTwoCell 可能需 W3。这是 M1 的正确目标。 |

补充（本文分析，未验证）：M1-a 的 **witness 部分**（给定 commutes）其实是形式可证的 —— 两个方块的 apex、toX、toY 完全相同，只用 whisker 把锥搬到 pasted 方块再用 Qx.isPullback 即可，唯一非定义性的步骤是一个 associator coherence（与 S2071ConeMorphismBottom 同型）。S2622 走了更强的"两条 base 腿同构"路线（identity 专用）。但无论哪种，**commutes 本身**（即 Iso (toSource;m) (projection;ptY)）对一般 cover 不存在，所以 M1-a 不能成为 D6 路线。

### 1.5 与同日早前短稿的关系（保留其有效部分）

早前短稿（03:53，备份见 §0 版本说明）的结论是：最小改动 = 新增 wrapper

```
structure D6CoverWithCancellation (cover : OrbicurveFiniteEtaleCover X) where
  cancelRight : RightCancellation cover.map
  cancelWitness : M1RightCancellationWitness cover.map
```

并喂给 S2621/S2623。本文的更正：
- **有效**：import-cycle 警告（Iut 基础层不能 import paper 层 S2619/S2620）正确；paper-level wrapper、不动 Orbicurve.lean 的方向正确；S2622 的 identity 情形确实闭合（S2622 已编译）。
- **不成立**：该 wrapper 的 cancelRight : RightCancellation cover.map 对一般 cover **不可实例化**（S2090；S2622 只在 y = 𝟙 给出正例）。因此以它为假设得到的 S2623 下游定理对真实 D6 covers 是**空洞**的；且它把"目标"改成了论文没有的右消去公理。
- **替代**：本稿 §2 的 E7（S1866StrongCoverOf）是"同一批 baseChange 项的 strong 化"假设，有 terminal 正例、有 S2281 反例说明不可全称，且直接对应 S2512/S2514 的 concreteness；M1-b 在它之下有真实的几何内容。

---

## 2. (1) 需要新增/暴露的字段清单

> 结论先行：**没有需要新增到核心结构的字段**。需要"暴露"的是两个已有结构/谓词的使用面，加上 4-5 个拟新增的引理/定理。若强行在核心结构加字段，成本见 §2.3。

### 2.1 已存在、应直接复用的结构/字段（E 表）

| ID | 文件 | 结构/定义 | 字段/名称 | 精确类型（摘要） | 状态 |
|---|---|---|---|---|---|
| E1 | Orbicurve.lean | EtaleStackBaseChangePresentation | pullbackScheme / projection / projectionMap / toSource / commutes / isPullback | 见 §1.1 | 已实现 |
| E2 | Orbicurve.lean | TwoPullbackWitness | lift / liftToX / liftToY / liftTwoCell / liftTwoCell_toX / liftTwoCell_toY / twoCell_ext | 见 §1.1 | 已实现（弱） |
| E3 | S1852CoherentCoverActual.lean:166 | S1852ConeEssSurj P | （单个 Prop） | ∀ W c f, Nonempty (Iso (f;toX) c.toX) → Nonempty (Iso (f;toY) c.toY) → Nonempty (Iso f (P.isPullback.lift W c)) | 已实现/编译 |
| E4 | S1852CoherentCoverActual.lean:220 | StrongEtaleStackBaseChangePresentation map T point | toWeak : E1；coneEssSurj : E3 toWeak | — | 已实现/编译 |
| E5 | S1852CoherentCoverActual.lean:237 | StrongEtaleStackFiniteEtaleMorphism map | baseChange : ∀ T point, E4；hasProperty : ∀ T point, IsFinite … ∧ Etale … | — | 已实现/编译 |
| E6 | S1852CoherentCoverActual.lean:276 | StrongCover X | source / map / finiteEtale : E5 | — | 已实现/编译 |
| E7 | S1866ApexCoherenceActual.lean:130 | S1866StrongCoverOf Y | （单个 Prop） | ∃ M : E5 Y.map, M.toWeak = Y.finiteEtale；等价 ∀ T q, E3 (Y.finiteEtale.baseChange T q)（:134） | 已实现/编译 |
| E8 | S2558ConcreteWitnessPlanActual.lean:34/44 | S2558LiftOfCone / S2558LiftUnique | toX / toY / （Prop） | Iso (L;toX) c.toX、Iso (L;toY) c.toY；任意两 lift 2-同构 | 已实现/编译 |
| E9 | S2559ConcreteWitnessRefinementPlanActual.lean:35 | S2559HasLiftUnique hf | （单个 Prop） | 逐点 E8 | 已实现/编译 |
| E10 | S2103StrongAssemblyActual.lean:40 | S2103StrongCospanGMapFiniteEtale | （Type 1） | ∀ A B C f g, E5 g.map | 已实现/编译 |
| E11 | S2120PresentationTwistActual.lean:325/342/354 | S2120PresentationLiftConeMor / S2120PresentationTwoCellFull / S2120FirstMissing | （Props） | 见原文 | 已实现/编译（无 inhabitant） |
| E12 | S2622M1ConcreteWitnessActual.lean:217 | S2622IsoWitness | （def，非字段） | 两条 base 腿换成 2-同构的腿后，witness 保持不变地搬运（apex、toX、toY 不动） | 已实现/编译 |
| E13 | S2622M1ConcreteWitnessActual.lean:272/280/304 | m1RightCancellationWitnessId / rightCancellationId / presentationOfId | （defs） | y = 𝟙 的 M1 witness / RightCancellation / presentation | 已实现/编译（仅 identity） |
| E14 | S2624RightCancellationIdActual.lean:21 | idRightCancellation | （def） | 与 E13 的 rightCancellationId 同义（重复） | 已实现/编译 |

**E7 是本文的核心发现**：树里已经存在"把 X.finiteEtale.baseChange 暴露为 strong/concrete 且保持同一批 baseChange 项"的精确谓词，而且已有 terminal cover 的正例与一般 cover 的反例。**不要**再造一个同义谓词。

### 2.2 需要新增的声明（N 表，均不改核心结构）

| ID | 拟新增文件 | 名称 | 精确形状（拟） | 作用 | 行数估计 |
|---|---|---|---|---|---|
| N0 | tmp/sheaf/xif/paper/S2625LiftUniqueConeEssSurjActual.lean | coneEssSurj_iff_liftUnique | S1852ConeEssSurj P ↔ S2558LiftUnique (S1852WeakSquare P) P.isPullback（两个方向） | 把 S2561/S2562/S2622 的 W1 实例接入 S1852/S1866 的 W2 世界；否则 S2561 的结论无法直接喂给 E7/S2103 | ~30 |
| N1 | tmp/sheaf/xif/paper/S2626D6StrongCospanActual.lean | D6StrongCospan | ∀ (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C), S1866StrongCoverOf C（或逐 cover 的 D6StrongCover C） | M1-b 只需 **y-cover** 的 W2；这是"concrete witness"在 D6 的假设形式 | ~30 |
| N2 | tmp/sheaf/xif/paper/S2627D6VertexUnpastingActual.lean | d6VertexWitness_of_coneEssSurj | 给定 Py : E1、Px : E1、S1852ConeEssSurj Py（及可选 S2120FirstMissing），产出 S2096VertexSquare … .TwoPullbackWitness；打包为 S2096UnpastingStatement 的逐 datum 形式 | **M1-b 的实现**：真正的 unpasting | ~150-250 |
| N3 | tmp/sheaf/xif/paper/S2628D6FiniteEtaleConditionalActual.lean | d6BaseChangePresentationField_of_strong | D6StrongCospan → S2096BaseChangePresentationField（或 corrected BaseChangePresentationFieldWithHypotheses），复用 M2（S2617）与点 transport | 把 N2 接到 S2092/S2087/S2086；保持条件式 | ~80-150 |
| N4 | tmp/sheaf/xif/paper/S2629SchemeStrongFiniteEtaleActual.lean | schemeStrongFiniteEtale | (f : A ⟶ B) → [IsFinite f.left] → [Etale f.left] → E5 (S1742StrongTransOfHom f)，用 S2512Witness + S2561ConeEssSurj | 把 S2512 concrete witness 暴露成可复用的 strong finite-etale 构造器（S1726 与任意域） | ~200-300 |
| N5（可选，scope 改变） | tmp/sheaf/xif/paper/S2630ConcreteD6CoverActual.lean | ConcreteCover | model : SchemeOverField F、sourceIso : Iso (y model) source.fiber、baseModel、baseStackEq、mapModel : model ⟶ baseModel、isFinite、isEtale，并 toCover : OrbicurveFiniteEtaleCover X | 把 D6(c) 限制到 scheme 级 covers，用 S2091 直接消去，完全绕开 M1 | ~150-250 |

**N2 的关键依赖（本文分析，未经 Lean 验证）**：给定 vertex 方块的一个锥 (a, b, φ : a;m ≅ b;Py.toSource)，
- 把 φ 沿 y whisker 并配合 Py.commutes，得到 Px 方块的锥；Px.isPullback 给出 Q : W → Px，并有 Q;Px.toSource ≅ a、Q;Px.projectionMap ≅ b;Py.projectionMap；
- 对 Py 的方块，b 与 Q;vertexMap 是同一个锥的两个 lift（前者 refl，后者由 S2096VertexMap_comp 与 φ 得到），故 S1852ConeEssSurj Py 给出 Q;vertexMap ≅ b；
- 于是 lift := Q、liftToX := Px.liftToX、liftToY := 上述同构。
- liftTwoCell：用 Px.liftTwoCell 作用于搬运后的 cone morphism；liftTwoCell_toX 直接继承，liftTwoCell_toY 需要比较两个 2-胞在 vertexMap 下的像 —— 这一步可能需要 W3（twist），**这是唯一不确定的环节**。

### 2.3 不推荐：改动核心结构字段

| 方案 | 影响面（实测） | 后果 |
|---|---|---|
| 给 EtaleStackBaseChangePresentation 加 coneEssSurj/liftUnique 字段 | 永久文件中 EtaleStackBaseChangePresentation 出现 **252 次 / 102 个文件**；isPullback := 字面构造 **47 处** | 每个字面构造都要补证明；S1850 的 doubled presentation **不可能**满足新字段（S1852Doubled_not_strong），于是 S1850 整个反例文件失效，S2100/S2281 的论证基础被改动 —— 超出"最小改动" |
| 给 TwoPullbackWitness 加 liftUnique | S2557 已实测：59 个字面构造 / 33 个文件（S2557LiftUniquenessScopeActual.lean 文件头） | 同上；且 S2557 已给出非破坏性 mixin S2557WitnessWithLiftUniqueness（:32）作为正确替代 |
| 给 OrbicurveFiniteEtaleCover 加 strong : E5 map 字段 | OrbicurveFiniteEtaleCover 在 100+ 文件、1000+ 处出现 | cover 类型收缩为 strong covers；S1728Cover 的 category 定理全部要重证；且 S1728Cover 的目标语义被改变（需要用户批准） |
| 新增 wrapper D6CoverWithCancellation（早前短稿方案） | 新增 1 文件 | 字段内容对一般 cover 不可实例化（见 §1.5）；只能作接口，不能作 D6 路线 |

**S2557 的结论（本文重申）**：任何新强制性字段都会破坏每个字面构造，且每个站点需要真正的唯一性证明，不是机械补全。因此 E7 + N0-N3 的谓词路线是唯一符合"最小改动"的路线。

---

## 3. (2) 每个字段/声明的消费者与依赖

### 3.1 依赖图

```text
[E1 weak presentation] --(同一批项)--> [E4 strong presentation] --逐点--> [E5 strong finite-etale]
        |                                   ^
        |                                   | E3 = S1852ConeEssSurj
        |                                   |
        +--> [E2 weak witness] --> [E8 S2558LiftUnique] --N0--> [E3]
                                        ^
                                        |
                              [E9 S2559HasLiftUnique]
                                        ^
                                        |
                     S2561S2517HasLiftUnique (S2512 具体 cover，已编译)
                     S2562HasLiftUnique_identityStack (S2514 模式，[进行中])
                     S2622/S2624 (仅 y = 𝟙)

[E7 S1866StrongCoverOf Y] <--iff--> 逐点 [E3]          (S1866:134)
        |
        | (terminal 正例 S1866:169；一般 cover 反例 S2281:34)
        v
[N1 D6StrongCospan] --N2--> [S2096UnpastingStatement] --S2096VertexPresentation--> E1 at (Py 的 point)
        |                                                                  |
        |                                              S2096VertexProjection_isFiniteEtale (S2096:394)
        |                                                                  v
        |                                                   [S2096BaseChangeStatement = M2，S2617 已闭合]
        |                                                                  v
        +--------------------------N3--------------------------> [S2096BaseChangePresentationField]
                                                                           v
                                                              [S2092MorphismOfFiniteEtaleStacks]
                                                                           v
                                                              [S2087GMapFiniteEtaleField]
                                                                           v
                                                              [S2086CospanGMapFiniteEtale]
                                                                           v (+ S2086BaseChangePullback)
                                                              [S2086D6FiniteEtaleOfInputs] = D6(c)
```

### 3.2 消费者表

| 字段/声明 | 直接消费者（文件:行） | 间接消费者 | 缺失时后果 |
|---|---|---|---|
| E1 EtaleStackBaseChangePresentation | 所有 presentation 构造：S2512:624、S2514:126、S2058:223、S2616:47、S2617:24、S1850:363 等 | 整个 D6 链 | 已有，无需改 |
| E2 TwoPullbackWitness | S2512:485、S2514:87、S1850:363、S2071、S2616、S2622:217 等 | 同上 | 已有，弱点即本文主题 |
| E3 S1852ConeEssSurj | S1852:231（作为 E4 字段）、S1866:134/140、S2100:145、S2103、S2110 | S2086 链（经 S2103） | 无 E3 则 strong 路线整体不可用 |
| E4 StrongEtaleStackBaseChangePresentation | S2100:134（S2100StrongGPresentationInput）、S2103:52、S2109、S2110:280 | S2086 链 | 同上 |
| E5 StrongEtaleStackFiniteEtaleMorphism | S2103:41、S2109:40、S2110:261/266、S2284:43、S2290:42 | D6(c) 的 strong 输入 | 同上 |
| E7 S1866StrongCoverOf | S1866:154/169；S2281:34（否定） | 本文 N1；S1866 的 pullback/coproduct 义务 | 无正例则假设空洞；有反例说明**不能全称** |
| E8/E9 S2558LiftUnique/S2559HasLiftUnique | S2555/S2554/S2553/S2541/S2549/S2552；S2562（[进行中]）；S2561:164 | 抽取链；本文 N0/N2 | 不影响 D6 的其它部分 |
| E10 S2103StrongCospanGMapFiniteEtale | S2103:56、S2109、S2110:261/274、S2284:43、S2287:52、S2290:49 | D6(c) strong 版 | 作为假设保留 |
| E11 S2120FirstMissing | S2120:360、S2123、S2125 | 若 N2 的 liftTwoCell 需要 twist | 未验证；见 §5.3 R3 |
| E12 S2622IsoWitness | S2622:264（cancelWitnessId）；可复用于任何同-apex 换基腿 | M1-a 的正例族 | 已有；不解决一般 cover（见 §1.4） |
| E13/E14 identity 正例 | S2622:304（presentationOfId）；S2624:21 | 仅 terminal cover 的 D6 路径 | 仅 identity |

### 3.3 关键"依赖"事实

1. **E7 ⇒ E3 逐点**（S1866:134，已证）：Strong ... .coneEssSurj 在 M.toWeak = Y.finiteEtale 下就是 Y.finiteEtale.baseChange T q 的 E3。
2. **E3 ⇔ E8**（N0，未实现）：本文给出证明草图；约 20-30 行。
3. **E9 的实例 → E3 的实例** 依赖 N0；目前 S2561 只到 E8，S2562 只到 E9，二者都**没有**接到 E3/S1866。这是"暴露"链上最便宜也最关键的一环。
4. **E10 与 E7 不同**：E10 是"每个 g.map 有一个 strong 结构"（与 cover 的 weak 数据**无关**，S2287 明确审计）；E7 是"该 cover 的 weak 数据**本身**可 strong 化"（保持同一批项）。D6 的 strong 路线用 E10；M1-b 需要的是 **y-cover 的 E7/E3**。
5. **E12 只搬基腿**：S2622IsoWitness 要求 eX : x ≅ x'、eY : xi ≅ xi'；M1-a 需要 x = m;y、x' = m，故必须有 m;y ≅ m（identity 才由 rightUnitor 给出）。这精确解释了为什么 S2622/S2624 只能处理 y = 𝟙。

---

## 4. (3) 能否复用 S2512Witness / S2514IdWitness

### 4.1 S2512Witness（S2512StackOpenImmersionUB.lean:485）

**类型（存活于 section Generic，{F : Type} [Field F]，对任意域成立）**：

```lean
S2512Witness (hpb : IsPullback pX.left pY.left (S2512BaseF sq).left (S2512BaseG sq).left)
  (hX : sq.toX = S1742StrongTransOfHom pX) (hY : sq.toY = S1742StrongTransOfHom pY) :
  sq.TwoPullbackWitness
```

**适用条件（必须逐条满足）**：
1. 四个角都是 representable stack S2512YS S = schemeRepresentableEtalePseudofunctor F S（S2512StackOpenImmersionUB.lean:117）；
2. sq.toX、sq.toY **两条出 apex 的腿**是某个 scheme 态射的 2-Yoneda 像（hX/hY）；
3. hpb 是对应 scheme 方块的 IsPullback。
   基腿 xToBase/yToBase **可以任意**（M1 的 m、ptY 不必是 Yoneda 像）。

**能否用于 M1-b 的顶点方块？**
- 顶点方块：apex Px（representable ✓）、toX = Px.toSource（**任意** stack 态射，不是 Yoneda 像 ✗）、toY = Yoneda(vertexMap)（✓）、基腿 m（任意 ✓）、Py.toSource（任意 ✓）。
- 因为 toX 不是 Yoneda 像，**S2512Witness 不能直接套到 M1-b 的顶点方块**。它需要的 hX 恰是缺失的那条信息（Px.toSource 是任意 strong transformation，来自 cover 的 finiteEtale 数据）。
- 但 S2512Witness 的 **强性质**可用于 Py 或任何 S2512 式 presentation：S2561ConeEssSurj（S2561:100，**已编译**）证明 S2512Witness 满足 S1852ConeEssSurj；S2561S2512LiftUnique（S2561:132）给出 E8。

**能否用于具体 covers？** 能，且树里已经做了：S2517InvObj C（S2517InvObjActual:46）的 finiteEtale.baseChange 就是 S2517RepBaseChange（S2517StackPresentationActual:40），其 isPullback := S2512Witness …（:62）；S2561S2517HasLiftUnique（S2561:164）证明它的 E9。这就是"D6 cover 的 X.finiteEtale.baseChange 已被暴露为 S2512 concrete witness"的已实现范例 —— 但它只覆盖 S2482Orbicurve 上由 FiniteEtaleCover S2482AffineScheme 构造的具体 covers，不覆盖 S1726Orbicurve 的任意 cover，也不覆盖抽象 cover。

### 4.2 S2514IdWitness（S2514IdentityFiniteEtaleActual.lean:87）

**类型**：(T : SchemeOverField F) (q : y(T) ⟶ S2482Orbicurve.stack.fiber) → (mk q (id) (id) q (S2514IdCommutes T q)).TwoPullbackWitness。lift = cone.toY；liftTwoCell = morphism.toY；三条 coherence 靠"到 representable stack 的 2-胞是 subsingleton"消去。

**适用条件**：**只适用于** map = id、point = 同一个 q、apex = T 的 identity-point 方块。S2514IdBaseChange（:126）与 S2514IdentityFiniteEtale（:140）是它的打包。

**能否复用？**
- 对 **identity cover / terminal cover**：能，且已有 S1726 版本 —— S1762IdBaseChange（S1762CoverLimitsActual.lean:209，S1762K = S1726K、S1762X = S1726Orbicurve）与 S1852IdStrongBc（S1852:369，W2）/ S1852IdStrong（S1852:380，E5）；S1854StrongOfS1762（S1854:322）把它接到 terminal cover，S1866StrongCoverOf_terminal（S1866:169）给出 E7。对 S2482：S2514IdentityFiniteEtale + S2562HasLiftUnique_identityStack（S2562:180；源码 20:00 已改写，19:53 的 olean 已过期，**[未验证]**）。
- 对 **任意 cover**：不能。S2514 的证明用到 S2482Orbicurve.stack 的 representability（S2514Modification_subsingleton_representable，S2514:38）；一般 cover 的 map 不是 identity，方块形状不对。

### 4.3 为什么"直接展开 X.finiteEtale.baseChange"不可行

1. **定义上不可约**：X.finiteEtale.baseChange T q 是 OrbicurveFiniteEtaleCover.finiteEtale 字段的投影，其值是一个**任意项**；没有方程把它与 S2512Witness/S2514IdWitness 联系起来。
2. **弱记录不足以推出 strong**：S1850 的 doubled cover 与 terminal cover **同 source、同 map**（S1850SameSource/S1850SameMap，S1850:381/384），但前者不 strong（S1852Doubled_not_strong）。所以任何从弱记录到 strong 的推导都会把 doubled cover 也变 strong，矛盾。
3. **全称形式被反驳**：S2100NotGPresentationConeEssSurj、S1852NotFirstMissing、S2281NotAllCoversStrong。
4. **点 transport 缺失**：即使把某个具体 witness 搬到另一个点，S2058 只 transport map，不 transport point（S2096 文件头明确列为第三项缺失）。

### 4.4 可复用的引理清单（不用重写）

| 引理 | 位置 | 在本文方案中的用途 |
|---|---|---|
| S2512Modification_subsingleton | S2512:179（任意域 F） | 一切 representable apex 上的 2-胞消去；N2 的 liftTwoCell 比较 |
| S2512Val / S2512Val_def | S2512:127/133 | 计算 toSource/projection 的 scheme 值 |
| S2512Val_vcomp / S2512Val_strongTransOfHom | S2512:155/145 | 把复合与 Yoneda 像化为 scheme 复合 |
| S2512Val_isoOfValEq | S2512:195 | 由逐点值相等组装 2-同构（N2 的 liftToY） |
| S2561ConeEssSurj / S2561S2512LiftUnique | S2561:100/132（**已编译**） | N4 的 W2；S2512 concrete cover 的 E3/E8 |
| S2514IdWitness / S1762IdBaseChange / S1852IdStrongBc | S2514:87 / S1762:209 / S1852:369 | identity/terminal 实例；N1 的非空性 |
| S1854StrongOfS1762 | S1854:322 | terminal cover 的 E5（保持同一批弱项） |
| S1866StrongCoverOf_iff_baseChange | S1866:134 | E7 ↔ 逐点 E3；N1 的核心转换 |
| S2517RepBaseChange / S2561S2517HasLiftUnique | S2517StackPresentationActual:40 / S2561:164 | 具体 cover 的 S2512 暴露范例（S2482） |
| S2622IsoWitness | S2622:217 | 同-apex 换两条基腿的 witness transport；可用于把 M1-a 的形式部分一次做完 |
| S2091_scheme_finiteEtale_cancel_special | S2091 | N5 的 scheme 级消去（绕开 M1） |

### 4.5 结论表

| 见证 | 能复用给 M1-b？ | 能复用给具体 cover 的 finiteEtale？ | 关键理由 |
|---|---|---|---|
| S2512Witness | **否**（顶点方块 toX 不是 Yoneda 像） | **能**（S2517InvObj 已是范例） | 要求两条出 apex 的腿都是 Yoneda 像 |
| S2514IdWitness | 仅 identity/terminal 情形 | 仅 identity cover | 只覆盖 map = id |
| S2512Witness 的**强性质**（S2561ConeEssSurj） | **能**，作为 Py 的 E3 | **能** | 与见证形状无关，只与"apex representable + 腿是 Yoneda 像"有关 |
| S2514IdWitness 的**强性质**（right unitor 论证） | 仅 Py 为 identity 情形 | 仅 identity | 同上 |
| S2622IsoWitness | 仅当两条基腿有 2-同构（identity） | 仅 identity | 需要 m;y ≅ m、ptY;y ≅ ptY |

---

## 5. (4) 最小改动顺序与风险

### 5.1 步骤（S0-S5）

**S0（决策，无代码）**：把 M1 的目标从 M1-a 改为 M1-b。具体动作：
- 在 AUDIT_LEDGER.md 追加一条：S2618/S2620 的 M1CancellationGoal 是 S2090PostcompCancellation 的特例，在一般 cover 上不可实例化；S2622/S2624 只覆盖 y = 𝟙；早前短稿的 D6CoverWithCancellation 因同一原因不可作为 D6 路线。
- 不修改 S2618/S2619/S2620/S2621/S2623；保留为接口/历史证据。S2622 的 identity 结果保留为 terminal-cover 正例。
- **验收**：文档改动，不触发构建。

**S1（桥接，N0，约 30 行）**：S2625LiftUniqueConeEssSurjActual.lean
- 定理 coneEssSurj_iff_liftUnique：对 P : EtaleStackBaseChangePresentation map T point，S1852ConeEssSurj P ↔ S2558LiftUnique (S1852WeakSquare P) P.isPullback。
- 证明：→ 方向取 witness 自己的 liftToX/liftToY 作为第二个 S2558LiftOfCone，两次应用 E3 后传递；← 方向把 E3 的 f 与 P.isPullback.lift W c 作为两个 lift。
- **依赖**：E3、E8、S1852WeakSquare（S1852:139）。
- **验收**：编译、olean、#print axioms 只含 trio、目标类型 #check 锁定。
- **风险**：低。唯一细节是 S1852WeakSquare 与 presentation square 的 defeq；S1852:139 的定义就是 mk P.toSource P.projectionMap.transformation map point P.commutes，应与 P.isPullback 的 square 定义一致。

**S2（假设形式，N1，约 30-40 行）**：S2626D6StrongCospanActual.lean
- def D6StrongCover (C : S1728Cover) : Prop := S1866StrongCoverOf C
- def D6StrongCospan : Type 1 := ∀ A B C f g, S1866StrongCoverOf C（M1-b 只需第二个 cover）
- theorem d6StrongTerminal : S1866StrongCoverOf S1762TerminalCover（直接引用 S1866:169）
- theorem d6StrongCospanTerminal : D6StrongCospan（在 B、C 均为 terminal 时）
- 可选：theorem d6StrongOfLiftUnique (h : ∀ C, S2559HasLiftUnique C.finiteEtale) : ∀ C, S1866StrongCoverOf C（用 N0）。
- **验收**：编译；非空性至少由 terminal 实例给出。
- **风险**：低；但注意 S1728Cover 的 covers 是 S1726Orbicurve，而具体 S2512/strong 实例目前多在 S2482Orbicurve（见 S4）。

**S3（核心，N2，约 150-250 行）**：S2627D6VertexUnpastingActual.lean
- 输入：m : X.Hom Y、y : Y.Hom Z、T、ptY、Py : presentation y T (ptY;y)、Px : presentation (m;y) T (ptY;y)、hY : S1852ConeEssSurj Py；可选 hTwist : S2120FirstMissing（若 liftTwoCell 需要）。
- 输出：S2096VertexSquare … .TwoPullbackWitness；打包为 S2096UnpastingStatement 的逐 datum 形式（不修改 S2096 文件，新文件里重新陈述同型）。
- 实现：按 §2.2 的三步构造 lift/liftToX/liftToY；liftTwoCell 用 Px.liftTwoCell + 搬运 cone morphism；liftTwoCell_toX 直接继承；liftTwoCell_toY 先尝试用 S2120 的两个 API，若失败则把 hTwist 加进输入并明确标注。
- **验收**：目标类型 #check 锁定为 S2096:424 的形状；无 sorry；trio axioms。
- **风险**：**高**（§5.3 R3）。这是唯一需要新数学的步骤。

**S4（装配，N3，约 80-150 行）**：S2628D6FiniteEtaleConditionalActual.lean
- 由 N2 得到 EtaleStackBaseChangePresentation m Py.pullbackScheme Py.toSource（经 S2096VertexPresentation，已证）。
- S2096VertexProjection_isFiniteEtale（S2096:394，已证）给出投影 finite/etale。
- 走 S2096 的路线：section s : T → Py.pullbackScheme（构造性，S2096 文件头记录为可构造）、M2（S2617.baseChangeStatement，已闭合）、点 transport（**缺失**，§4.3(4)）。
- 产出 S2096BaseChangePresentationField（S2096:229）或 corrected BaseChangePresentationFieldWithHypotheses（S2620:56）的**条件版**；再经 S2092 → S2087 → S2086。
- **验收**：条件语句编译；hypotheses 明确列出（D6StrongCospan + 可能 hTwist）。
- **风险**：中。点 transport 是已知的第三项缺失；若不做，可以把 N3 的结论表述为"在 Py 点处"并直接喂给 S2086 的某个变体，但那样会改变 S2086 的量化形状（不推荐）。

**S5（可选，N4/N5）**：
- N4：把 S2512 的 concrete witness 暴露成 schemeStrongFiniteEtale (f : A ⟶ B)（E5），用于把具体 covers 实例化到 S1726（S2517 目前只到 S2482）；约 200-300 行，可直接复用 S2512Witness + S2561ConeEssSurj。
- N5：ConcreteCover + S2091 直接消去，得到 concrete covers 上的**无条件** D6(c)，但对象范围收窄；需用户批准。
- **验收**：N4 给出 S1866StrongCoverOf 的具体实例；N5 给出 S2086CospanGMapFiniteEtale 的受限版本。

### 5.2 diff 估算

| 文件 | 改动 | 行数 |
|---|---|---|
| S2625LiftUniqueConeEssSurjActual.lean | 新增 | ~30 |
| S2626D6StrongCospanActual.lean | 新增 | ~30-40 |
| S2627D6VertexUnpastingActual.lean | 新增 | ~150-250 |
| S2628D6FiniteEtaleConditionalActual.lean | 新增 | ~80-150 |
| S2629SchemeStrongFiniteEtaleActual.lean | 新增（可选） | ~200-300 |
| Orbicurve.lean / S2512 / S2514 / S2618-S2623 | **0 改动** | 0 |

### 5.3 风险表

| # | 风险 | 概率 | 影响 | 缓解 |
|---|---|---|---|---|
| R1 | 继续用 M1-a（RightCancellation） | 若沿用 S2621/早前短稿则必然 | 路线不可实例化（S2090；S2622 需要 m;y ≅ m，只有 y = 𝟙 有） | S0 明确弃用；S2619/S2620/S2622/S2624 只作接口与 identity 正例 |
| R2 | S1866StrongCoverOf 对一般 cover 不可证 | 确定（S2281） | D6(c) 只能是条件定理 | N1 的假设形式；写清 scope 改变；需用户批准 |
| R3 | vertex unpasting 的 liftTwoCell 需要 W3（twist） | 中-高 | N2 的假设要加 S2120FirstMissing；S2512/S2514 的 W3 实例未验证 | 先证明 lift/liftToX/liftToY；把 hTwist 作为显式输入；S2120/S2125 已有精确 API |
| R4 | 改核心结构字段 | 若被要求 | 252 处/47 字面（E1）；59 处（E2）；S1850/S2100/S2281 的基础被破坏 | 坚持 E7 + 谓词路线 |
| R5 | 并行任务冲突/重复 | 高 | S2561/S2562/S2621/S2623/S2624 在 03:40-03:55 持续改写；S2622 的 rightCancellationId 与 S2624 的 idRightCancellation 重复 | 在 S1 前重查 olean 与 SHA；S 编号向 queue 预约；只依赖已编译文件；合并重复定义 |
| R6 | 导入过重：S2512 依赖 S2508/S2495cF（UB cusp） | 中 | 编译时间/内存 | 把 S2512 的 Generic 段（1-4 节）抽到轻文件，或 N4 直接 import S2512 并接受成本；不要复制粘贴 |
| R7 | defeq/elaboration：backward.isDefEq.respectTransparency false、presentation square 的定义形状 | 中 | 证明脚本需要 change/show 调整 | 用命名 square（S2562PointSquare 模式）；先 #check 锁定类型 |
| R8 | scope 改变（条件化 D6(c) 或收窄到 concrete covers） | 确定 | 与论文 D6 语义不一致 | 明确写入报告/ledger，需用户指令；不静默改目标 |
| R9 | 公理足迹 | 低 | 只允许 propext/choice/Quot.sound | 每个新定理 #print axioms |
| R10 | 维护：S1852/S1866/S2100/S2281 是 10 月末-11 月初的稳定层；S2556-S2562/S2618-S2624 是 11-05 的新层 | 中 | 新层可能继续变动 | 以已编译的 olean 为依据；报告标注采样时间 |
| R11 | 早前短稿方案的假设空洞 | 若被采纳 | D6 下游定理对真实 covers 无实例 | 本稿 §1.5 明确更正；保留 wrapper 仅作接口 |

### 5.4 建议的下一个可执行任务

> **任务 S2627（或 queue 中下一个可用编号）：d6VertexWitness_of_coneEssSurj**
> - 输入：S2096 的 m、y、T、ptY、Py、Px，以及 hY : S1852ConeEssSurj Py（可选 hTwist : S2120FirstMissing）。
> - 输出：(S2096VertexSquare …).TwoPullbackWitness，类型与 S2096:424 的逐 datum 形状一致。
> - 禁止：sorry、axiom、新假设（除显式的 hY/hTwist）、修改 Orbicurve.lean。
> - 验收：lake env lean exit 0；olean 存在；#print axioms 只含 trio；#check 目标类型；与 S2096:424 的定义做 defeq 对照。
> - 回退：若 liftTwoCell 卡住，提交"lift/liftToX/liftToY + liftTwoCell_toX 已证，liftTwoCell_toY 等价于 S2120 的某个具体 API"的中间报告，并把 hTwist 提升为输入。

---

## 6. 未运行 / 未验证清单（诚实边界）

- 本文**没有**写任何 Lean；**没有**运行 lake build/lake env lean；**没有**创建或修改任何 .lean 文件。
- 本次只新增/改写了报告文件；早前短稿已备份为 D6-M1-concrete-witness-plan-20261106.prev-short-draft.md。
- 标 [进行中/未验证] 的文件：S2562CorrectedEssSurjLiftUniqueActual 在 20:00 被改写为 28231 B（SHA 607B24AC...），而现有 olean 是 19:53 的旧版，**未验证**；S2621/S2623 有 olean 但 19:46-19:48 被重建；S2622（19:51 有 olean）与 S2624（19:53 有 olean）内容有重复。
- S2561S2512LiftUniqueActual 在采样时**有** olean（19:46），源码 8552 B；其 S2561S2517HasLiftUnique 依赖 S2517 层，未逐行核对 S2517 的全部定义。
- "N2 可通过 §2.2 的三步证明"是**分析结论，不是已验证的证明**；liftTwoCell_toY 的 W3 需求未定。
- "M1-a 为假"的依据是 S2090 的文本 + S2622 的显式 unitor 需求；工作区**没有**形式化的 RightCancellation 反例（S2622/S2624 只证了 y = 𝟙 的正例）。
- "S2517InvObj 是 D6 cover 的 S2512 暴露范例"只对 S2482Orbicurve 成立；S1726Orbicurve 的对应构造（N4 的实例化）未做。
- 未核对 S2512/S2514 是否满足 W3（S2120FirstMissing）；这是 §5.3 R3 的开放点。

---

## 附录 A：引用文件 SHA256（采样 2026-11-06 03:55 前后，Asia/Shanghai）

| 文件 | 字节 | SHA256 |
|---|---|---|
| Iut/Foundations/Orbicurve.lean | 44594 | 15D1362D6064AB079B3796B830F991343885D8B33ED4AAB30A8BDEE7DC7F0E1D |
| tmp/sheaf/xif/paper/S1728CoverCategoryActual.lean | 24882 | 255D3A978FBCB7DC818E2E8F6E6D97042A39304973B31CDD0523E5FC0B9198A6 |
| tmp/sheaf/xif/paper/S2096StackMorphismActual.lean | 26948 | EBC0F7E78BFA6D28F032EECA0D233FF4873E281AD3A2202A5D8DF4260D7EEACF |
| tmp/sheaf/xif/paper/S2512StackOpenImmersionUB.lean | 31112 | C9B0315F1EE64EFC52A963F1646E3519B9FE2CC64D5FB9AA81A3E0F326EF87BA |
| tmp/sheaf/xif/paper/S2514IdentityFiniteEtaleActual.lean | 7594 | B480991744ED4768D13B6FE163C1D6B6F6A4339AD0E577A76928E80B38879248 |
| tmp/sheaf/xif/paper/S2618M1CancellationGoal.lean | 1807 | 7AE56270866586EB356752A3A567961F7AB46138D4EC494105A214F076043DF8 |
| tmp/sheaf/xif/paper/S2619RightCancellationActual.lean | 1998 | A37AF5581EC2E8478AE7381A6789105DA50CD86242472E64312503268C5D4870 |
| tmp/sheaf/xif/paper/S2620M1CoherenceFields.lean | 3417 | FC3A65F7A5B7A3F3E7D9EDCB09F65E5D10C8E6656CC0D9B160F3376ACCFE8942 |
| tmp/sheaf/xif/paper/S2621FieldWithHypothesesActual.lean | 1807 | DB9135D56CDE42CC73EA9AAFC597444BC1496541A9E0C816DDB336FADDCDC08A |
| tmp/sheaf/xif/paper/S2622M1ConcreteWitnessActual.lean | 16469 | 9158CCF701816062B3E42FC09AA169611517829654725859F5076FB28B9B9367 |
| tmp/sheaf/xif/paper/S2623DownstreamActual.lean | 3553 | 8C0290AADB103B436A7AECB23C8F16DD7898735A6A018BE30B0DBA75B3837E72 |
| tmp/sheaf/xif/paper/S2624RightCancellationIdActual.lean | 992 | D3BBAF7229BDEBA4D1E1060D8735CDE6E8006EB8E7C787F8B89C01BB87E1BFDB |
| tmp/sheaf/xif/paper/S2556LiftUniquenessInterfaceActual.lean | 2689 | 60F91E53BE009D815E8BB74696CC1F5385BD97343116108FD7785FE8BDA48E18 |
| tmp/sheaf/xif/paper/S2557LiftUniquenessScopeActual.lean | 3240 | 322833D147CB60FC064889126A2D499A938C605F0EC510C42916B91DE4171ED1 |
| tmp/sheaf/xif/paper/S2558ConcreteWitnessPlanActual.lean | 3326 | AA2F1AF31EDE70617AD717C8E5D91FF69DB02C6A462E2F483D301B26D3E6F4C4 |
| tmp/sheaf/xif/paper/S2559ConcreteWitnessRefinementPlanActual.lean | 3105 | 8C5AD1E9176803C440A212BD87E5DFE795FA699362F19B9F9984FA59A3CCBAAF |
| tmp/sheaf/xif/paper/S2561S2512LiftUniqueActual.lean | 8552 | CC00FFA9797F05841B7785140733964A5307C44A2F02E504D5674593DE47FD18 |
| tmp/sheaf/xif/paper/S2562CorrectedEssSurjLiftUniqueActual.lean（进行中；20:00 改写，olean 过期） | 28231 | 607B24ACDF67974218C12B47DBFA47BCCBB3A49D0576D916AA1F76FB86ABD135 |
| tmp/sheaf/xif/paper/S1850RefuteS1756Actual.lean | 25528 | A5F1117C640FE87B4F2AEF30CEC8DF9031D99F9663060F75F47D1211819A6AC7 |
| tmp/sheaf/xif/paper/S1852CoherentCoverActual.lean | 31153 | 50D415E1DA8D3D46F8808DD48806E6F283A170ECC29D7C43C51821131F3FB429 |
| tmp/sheaf/xif/paper/S1854CoherentCategoryActual.lean | 34994 | 76395C8EFFBB6EE5A8BAF40ABBA915A7033D9A5B99B68CC494B0AF1A8F81F234 |
| tmp/sheaf/xif/paper/S1866ApexCoherenceActual.lean | 29796 | A5D060F31D6FE79C2809C88F3C113FA9D6FBD9813C19A265F6D981F3C9C7A367 |
| tmp/sheaf/xif/paper/S2090StackCancellationObstructionActual.lean | 1798 | EE941E1A65CF4E954CB067F537EBB6179CD89D406DF1C526F04538E4AF2BF9F4 |
| tmp/sheaf/xif/paper/S2092FiniteEtaleStackMorphismActual.lean | 1934 | 81F796480355A5DB529BD6B62425EF1E86C13826D171CEF002A498890985A5FC |
| tmp/sheaf/xif/paper/S2100GPresentationConeEssSurjActual.lean | 8123 | 2430B4291799ED75EED278FE75C9CC24C4DBA2705B32A1CCEE209481D1DA7246 |
| tmp/sheaf/xif/paper/S2103StrongAssemblyActual.lean | 3359 | 9DED2F8516BE0CAE07C0DD7F401ED970CD786C948EB83AE24CFA2283479BE926 |
| tmp/sheaf/xif/paper/S2110StrongTwoFullInputsActual.lean | 17375 | F69A74C70FD86C1E60A8654507225CB23E0B0D46F93BD7F95CDE73FE0B2DA2EE |
| tmp/sheaf/xif/paper/S2118PastedComparisonTwistActual.lean | 19467 | A410CAE1BDC864B35FF66D658E4EB2B0B6F4354AFFBC7CB321F28684449E7D87 |
| tmp/sheaf/xif/paper/S2120PresentationTwistActual.lean | 23743 | 2A778E5B4B45F77218E6D4118AE628D08D6EA88748223BA52064BF8442148D36 |
| tmp/sheaf/xif/paper/S2281ActualCoverStrongActual.lean | 1904 | 0490CE6770095BCC6D3CBB8819CDB183F26ACEE9DE131C5C05FE9A52F212A34F |
| tmp/sheaf/xif/paper/S2284S2086QuantifierActual.lean | 1920 | 0B37AB289B4394BCF093BBBCAED228908A90F574D922F0CD00AE4DFC0FBECBCF |
| tmp/sheaf/xif/paper/S2287StrongCospanRefuteActual.lean | 2420 | CAB251B21945F0F39A26CEA1D345643CA3B971180A272956681302483B0EFE95 |
| tmp/sheaf/xif/paper/S2290StrongCospanActual.lean | 2399 | 82003E4B13384C46E87B736168E987B60A95E028B966336C7C8CFB82D5F3BAFF |
| tmp/sheaf/xif/paper/S2097BaseChangeButterflyActual.lean | 15096 | C0CAFD0B10EA393D629CBC7F97082A9DA8052215F01347CB6F098BA9898AA4BE |
| tmp/sheaf/xif/paper/S1762CoverLimitsActual.lean | 15933 | 7FB5845B6BE92BA26B3A81E14151F693F593A2B3DAD44F822460B07137EB2A97 |
| tmp/sheaf/xif/paper/S2058D6FiniteEtaleActual.lean | 26510 | 9A4288B46EE98C8FCB285AFE2F3121EFCC8F2744AC0C182E0B19D68DD28AB1B8 |
| tmp/sheaf/xif/paper/S2086ToAAssemblyActual.lean | 13665 | 21025F73EBBDB0C65808B1BD97946A33757BD61607F3AC88B66897B6448BBD32 |
| tmp/sheaf/xif/paper/S2087ToAObstructionActual.lean | 1859 | 8C1384A940B531D05EE5A0D1FBCC93BB79E3EB4907135F2D9E2DAB634392C33A |
| coord/reports/D6-M1-concrete-witness-plan-20261106.prev-short-draft.md | 4565 | 03:53 短稿的原样备份（内容见该文件） |

## 附录 B：关键类型原文（节选）

**E3/E4/E5（S1852）**

```lean
def S1852ConeEssSurj (P : EtaleStackBaseChangePresentation map testScheme point) : Prop :=
  ∀ (W) (c : (S1852WeakSquare P).Cone W) (f : StrongTrans W (y P.pullbackScheme)),
    Nonempty (Iso (vcomp f (S1852WeakSquare P).toX) c.toX) →
    Nonempty (Iso (vcomp f (S1852WeakSquare P).toY) c.toY) →
      Nonempty (Iso f (P.isPullback.lift W c))

structure StrongEtaleStackBaseChangePresentation map testScheme point where
  toWeak : EtaleStackBaseChangePresentation map testScheme point
  coneEssSurj : S1852ConeEssSurj toWeak

structure StrongEtaleStackFiniteEtaleMorphism map where
  baseChange : ∀ testScheme point, StrongEtaleStackBaseChangePresentation map testScheme point
  hasProperty : ∀ testScheme point,
    IsFinite ((baseChange testScheme point).toWeak.projection.left) ∧
      Etale ((baseChange testScheme point).toWeak.projection.left)
```

**E7（S1866）**

```lean
def S1866StrongCoverOf (Y : S1728Cover) : Prop :=
  ∃ M : StrongEtaleStackFiniteEtaleMorphism Y.map, M.toWeak = Y.finiteEtale

theorem S1866StrongCoverOf_iff_baseChange (Y : S1728Cover) :
    S1866StrongCoverOf Y ↔
      ∀ (T) (q : y T ⟶ S1726Orbicurve.stack.fiber),
        S1852ConeEssSurj (Y.finiteEtale.baseChange T q)
```

**E8/E9（S2558/S2559）**

```lean
structure S2558LiftOfCone (sq) {W} (c : sq.Cone W) (L : StrongTrans W P) where
  toX : Iso (vcomp L sq.toX) c.toX
  toY : Iso (vcomp L sq.toY) c.toY

def S2558LiftUnique (sq) (w : sq.TwoPullbackWitness) : Prop :=
  ∀ (W) (c : sq.Cone W) (L1 L2), S2558LiftOfCone sq c L1 → S2558LiftOfCone sq c L2 →
    Nonempty (L1 ≅ L2)

def S2559HasLiftUnique (hf : EtaleStackFiniteEtaleMorphism map) : Prop :=
  ∀ (T) (q), let P := hf.baseChange T q
    let sq := EtalePseudofunctorSquare.mk P.toSource P.projectionMap.transformation map q P.commutes
    S2558LiftUnique sq P.isPullback
```

**E12（S2622，两条基腿的 transport）**

```lean
def S2622IsoWitness (toX : P ⟶ X) (toY : P ⟶ Y)
    {x x' : X ⟶ Z} (eX : Iso x x') {xi xi' : Y ⟶ Z} (eY : Iso xi xi')
    (c : Iso (vcomp toX x) (vcomp toY xi))
    (c' : Iso (vcomp toX x') (vcomp toY xi'))
    (w : (mk toX toY x xi c).TwoPullbackWitness) :
    (mk toX toY x' xi' c').TwoPullbackWitness
```

**S2618/S2620（M1-a，本文不建议作为 D6 路线）**

```lean
def M1CancellationGoal : Type 1 :=
  ∀ {X Y Z} (m : X.Hom Y) (y : Y.Hom Z) (T) (ptY : y T ⟶ Y.fiber)
    (Qx : EtaleStackBaseChangePresentation (vcomp m y) T (vcomp ptY y)),
    Iso (vcomp Qx.toSource m) (vcomp Qx.projectionMap.transformation ptY)

structure M1RightCancellationWitness {Y Z} (y : Y.Hom Z) : Type 1 where
  cancelWitness : ∀ {X} (m : X.Hom Y) (T) (ptY) (Qx)
    (commutes : Iso (vcomp Qx.toSource m) (vcomp Qx.projectionMap.transformation ptY)),
    (EtalePseudofunctorSquare.mk Qx.toSource Qx.projectionMap.transformation m ptY commutes)
      .TwoPullbackWitness
```

**S2096 vertex 数据（M1-b 的目标形状）**

```lean
def S2096UnpastingStatement : Type 1 :=
  ∀ {X Y Z} (m : X.Hom Y) (y : Y.Hom Z) (T) (ptY) (Py) (Px),
    (S2096VertexSquare (m := m) (y := y) (T := T) (ptY := ptY)
      (Py := Py) (Px := Px)).TwoPullbackWitness

def S2096VertexPresentation
    (h : (S2096VertexSquare …).TwoPullbackWitness) :
    EtaleStackBaseChangePresentation m Py.pullbackScheme Py.toSource :=
  { pullbackScheme := Px.pullbackScheme
    projection := S2096VertexMap …
    projectionMap := { transformation := S1742StrongTransOfHom (S2096VertexMap …), app_eq := … }
    toSource := Px.toSource
    commutes := S2096VertexCommutes …
    isPullback := h }
```
