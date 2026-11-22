# S735 memo: Mathlib 工具调研 —— group cohomology / equivariant / quotient / orbifold / Bredon / torsor
## 对 μ_{2l} root stack、quotient、invariant measure 的可用性判定

Date: 2026-10-30
Status: **research memo only**；无新 Lean 定理、无 fake carrier。
Scope: 只回答"Mathlib 现成工具能否形式化 μ_{2l} root stack/quotient 与 invariant measure"，
以及"能否直接用于 TASK_LEDGER 的 exact gap"。不做构造、不写 sorry 接口。

固定版本（本 memo 全部结论只对该版本负责）：
* Lean: `leanprover/lean4:v4.32.2` (`D:/lean/lean-toolchain`)
* Mathlib: commit `905b95818eb32af7874a58b427f50c1711a5e96c` (2026-07-28, "bump toolchain to v4.32.2")，
  8264 个 `.lean` 文件，路径 `D:/lean/.lake/packages/mathlib/Mathlib`。
* 证据标记：
  - **[C]** = 已用 `lake env lean` 编译过的 `#check` 确认（probe 见 §10）；
  - **[S]** = 只读源码确认（给 file:line），未单独编译。

---

## 0. 六项判定摘要

| 项 | Mathlib 现状 | 对 μ_{2l} root stack / invariant measure | 判定 |
|---|---|---|---|
| Group cohomology | 完整（8 文件），有限循环群有 H^i 计算 | 可算 H^0/H^1/H^2(μ_{2l}, M)；**不是** étale/几何上同调 | **部分可用** |
| Equivariant | 无 equivariant homotopy/cohomology；只有 MulAction/ActionCategory | 只够做"G-集合/action groupoid" | **仅集合层可用** |
| Quotient | orbitRel.Quotient / ActionCategory / QuotientGroup 完整 | 可做 μ_{2l} 的粗商与 action groupoid；**无** stack/GIT 商 | **可用（1-范畴层）** |
| Orbifold | **不存在**（全库 1 条注释） | — | **拒绝** |
| Bredon | **不存在**（0 match） | — | **拒绝** |
| Torsor | `Torsor G P` 类完整（Algebra/Torsor） | 根集 = μ_{2l}-torsor，**直接可用** | **可用** |
| Invariant measure | Haar + fundamental domain + quotient measure 完整 | 唯一性/标量因子/|G| 因子可直接用 | **可用（见 §3 限制）** |
| （附加）Kummer | `FieldTheory/KummerExtension.lean` 完整 | 2l 次根 ↔ Gal ≅ μ_{2l}，次数 = 2l | **可用（域层）** |

一句话：**六项里能真正落到论文对象上的只有 (a) Torsor、(b) invariant measure 的
归一化/唯一性、(c) Kummer 的 2l 次根-伽罗瓦对应；(d) root stack 作为 action groupoid 可以
用 Mathlib 免费重写但不会增加数学内容；(e) orbifold/Bredon/equivariant cohomology/代数栈
在本版本完全不存在，任何依赖它们的路线都是新造，不能算"现成工具"。**

---

## 1. Group cohomology

文件（全在 `Mathlib/RepresentationTheory/Homological/`）：
* `GroupCohomology/Basic.lean`, `LowDegree.lean`, `FiniteCyclic.lean`,
  `Hilbert90.lean`, `Shapiro.lean`, `LongExactSequence.lean`, `Functoriality.lean`
* `GroupHomology/*`, `TateCohomology/Basic.lean`, `ContCohomology/*`
* 表示论基础：`Mathlib/Algebra/Category/ModuleCat/` 的 `Rep k G`

核心声明（[C] 除注明外）：
* `groupCohomology : (A : Rep k G) → ℕ → ModuleCat k`
  （`Basic.lean`；非齐次上链 `inhomogeneousCochains` 的上同调）
* `groupCohomology.H0Iso : groupCohomology.H0 A ≅ ModuleCat.of k ↥A.ρ.invariants`
* `groupCohomologyIso : groupCohomology A n ≅ homology (P.complex.linearYonedaObj k A) n`
* 有限循环群（**需要 `[CommGroup G] [Fintype G]`**）：
  - `Rep.FiniteCyclicGroup.groupCohomologyIsoEven`：
    `Even i → NeZero i → groupCohomology A i ≅ (normHomCompSub A g).homology`
  - `Rep.FiniteCyclicGroup.groupCohomologyIsoOdd`：`Odd i → ... (subCompNormHom A g).homology`
  - `Rep.FiniteCyclicGroup.groupCohomologyIso₀`：`H⁰ ≅ ker(ρ(g) − 1)`
  - 生成元条件：`(g : G) → (∀ x, x ∈ Subgroup.zpowers g)`
  - 生成元来源 [C]：`IsCyclic.exists_generator : ∃ g, ∀ x, x ∈ Subgroup.zpowers g`；
    `IsCyclic.commGroup` 可把 `IsCyclic` 群提升为 `CommGroup`（FiniteCyclic 要求）
* Hilbert 90（[C]）：
  - `groupCohomology.H1ofAutOnUnitsUnique : [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] → Unique ↑(groupCohomology.H1 (Rep.ofAlgebraAutOnUnits K L))`
  - `groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units`（Noether 形式）
  - `groupCohomology.exists_div_of_norm_eq_one : [IsGalois] [IsCyclic Gal] →
    (generator) → Algebra.norm K x = 1 → ∃ y, y / g y = x`
* 低次：`groupCohomology.IsMulCocycle₁/₂`, `IsMulCoboundary₁/₂`, `cocycles₁`, `coboundaries₁`

**群论侧供给（μ_{2l} 真能当 `G` 用）** —— `Mathlib/RingTheory/RootsOfUnity/`
* `instance : Finite (rootsOfUnity k R)`（`Basic.lean:245`，[S]）
* `instance rootsOfUnity.isCyclic : IsCyclic (rootsOfUnity k R)`（`Basic.lean:249`，[S]）
  —— **无条件**成立（不要求域含本原根），因为有限域乘法群的子群循环。
* `card_rootsOfUnity : Nat.card (rootsOfUnity k R) ≤ k`（`Basic.lean:252`，[S]）
* `rootsOfUnity.monoidHom_mulEquiv_rootsOfUnity (G) [CommGroup G] [IsCyclic G]`
  （`Basic.lean:330`，[S]）
* `class HasEnoughRootsOfUnity (M) [CommMonoid M] (n : ℕ)`（`EnoughRootsOfUnity.lean:27`，[S]）
  字段 `prim : ∃ m, IsPrimitiveRoot m n`、`cyc : IsCyclic (rootsOfUnity n M)`；
  派生 `exists_primitiveRoot`、`rootsOfUnity_isCyclic`、`finite_rootsOfUnity`。
  这是把"基域含 μ_n"作为**类**写下来的现成办法，比每次带 `(primitiveRoots n K).Nonempty` 干净。
* **摩擦点**：`Rep.FiniteCyclicGroup.*` 要求 `[Fintype G]`，而 `rootsOfUnity` 给的是
  `Finite`。需要 `Fintype.ofFinite`/`letI` 桥接（非computable），不是障碍但要记一笔。

**适用性（可做）**
1. μ_{2l} 是有限循环群（`IsCyclic` + `Fintype`），所以
   `groupCohomologyIsoEven 2` 可把 H²(μ_{2l}, M) 算成 `ker(N) / im(ρ(g) − 1)`。
   取 `M = ℤ` 平凡表示即得 **H²(μ_n, ℤ) ≅ ℤ/n**，这正是 μ_n-torsor 的 Kummer 类所在。
   这是能"诚实地"写出 root torsor 分类类的地方。
2. `H¹(Aut_K(L), L^×) = 0`（Hilbert90）可用于说明"域上 2l 次根一旦存在就唯一到 μ_{2l}"。

**拒绝**
* 不是 étale cohomology：没有 `H¹(X_ét, μ_n)`，因为 **Mathlib 没有 μ_n 群概形**
  （`AlgebraicGeometry` 全库 0 处 `rootsOfUnity`），也没有把 `rootsOfUnity n K` 变成
  概形层。要做只能自造，属新工作。
* 不是 Bredon / equivariant cohomology（见 §4/§5）。
* 不能分类 gerbe：`Rep k G` 的 H² 只给群上同调，不给"μ_n-gerbe"的几何类。

---

## 2. Equivariant / Quotient

**Equivariant**：全库无 `*Equivariant*.lean`；"equivariant" 只作为 `MulActionHom`
（记号 `→ₑ[φ]`，`Mathlib/GroupTheory/GroupAction/Hom.lean`、`Transitive.lean`）出现，
外加 `Algebra/MonoidAlgebra` 的 `equivariantOfLinearOfComm`。
**没有** equivariant 层/上同调、Borel 构造 EG×_G X、orbit category、Mackey functor。→ 拒绝。

**Quotient 与 action groupoid**（这一块反而很完整）[C]：
* `MulAction.orbitRel (G) (α) : Setoid α`；`MulAction.orbitRel.Quotient G α : Type`
* `MulAction.mem_orbit_iff`, `MulAction.orbitRel_apply`
* `MulAction.orbitEquivQuotientStabilizer`：`orbit G b ≃ G ⧸ stabilizer G b`
* `MulAction.IsPretransitive M α : Prop`（传递性）
* 自由性：**没有** `MulAction.IsFree` [C 失败]；用 `IsCancelSMul G P` [C]（"cancel smul"），
  这也是 `Topology/Covering/Quotient.lean` 里 "fiber is a G-torsor" 用的谓词。
* `CategoryTheory.ActionCategory (M) (X) [MulAction M X]`（`CategoryTheory/Action.lean:48`）[C]：
  - `ActionCategory.objEquiv M X : X ≃ ActionCategory M X`
  - `ActionCategory.hom_as_subtype p q : (p ⟶ q) = { m : M // m • p.back = q.back }`
  - `instance : Groupoid (ActionCategory G X)`（同文件 **:137**，G 为 Group）
  - `ActionCategory.stabilizerIsoEnd`：`stabilizerSubmonoid M x ≃* End ⟨(), x⟩`
  - `ActionCategory.endMulEquivSubgroup : End (... G ⧸ H ...) ≃* H`

**对现有代码的直接含义（重要）**
* `tmp/sheaf/xif/paper/S355OrbifoldRootStackCandidateActual.lean` 已经**正确复用了**
  `MulAction.orbitRel.Quotient`（这就是它的 `RootStackCandidate`），无需改。
* `S356RootStackActionGroupoidActual.lean` **手写了** `rootStackCategory` + `rootStackGroupoid`
  （91 行里 35–52 行），而 `CategoryTheory.ActionCategory (rootsOfUnity n (AC T b)) (CandidateRoots T b)`
  自带 `Groupoid` 实例、`hom_as_subtype`、`stabilizerIsoEnd`。这是**重复实现**，
  可无损替换（数学内容完全不变，只减少自造代码并拿到 stabilizer≃自同构群 的现成定理）。
  注意 `ActionCategory` 是 `Type`（小范畴），与 `RootStackActionGroupoidData.obj : Type` 兼容。

**拒绝**
* 没有 scheme/stack 的商、没有 GIT 商、没有 `[X/G]` 作为栈对象。
* `CategoryTheory.Sites.Descent.IsStack` 只对 `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` 讲 1-范畴下降
  （`Mathlib/CategoryTheory/Sites/Descent/IsStack.lean:49`）[S]，**不是**代数栈/根栈理论；
  没有 2-范畴的栈、没有根栈构造、没有 `Bμ_n`。

---

## 3. Invariant measure（本任务里最有实际产出的一块）

**Haar 本体**（`Mathlib/MeasureTheory/Group/Measure.lean`）[C]：
* `MeasureTheory.Measure.IsHaarMeasure {G} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  (μ : Measure G) : Prop` extends `IsFiniteMeasureOnCompacts`, `IsMulLeftInvariant`,
  `IsOpenPosMeasure`（**:775**）
* `MeasureTheory.Measure.IsHaarMeasure.smul : c ≠ 0 → c ≠ ⊤ → (c • μ).IsHaarMeasure`
* `MeasureTheory.Measure.haarMeasure_unique`（对 `[SecondCountableTopology G]` + PositiveCompacts）
* `MeasureTheory.Measure.haarScalarFactor : NNReal`；`isMulLeftInvariant_eq_smul`
  （`μ' = μ'.haarScalarFactor μ • μ`，需 `[LocallyCompactSpace G] [SecondCountableTopology G]`）
* `MeasureTheory.Measure.measure_isHaarMeasure_eq_smul_of_isEverywherePos`（开集/处处正集上的唯一性）
* `MeasureTheory.Measure.isHaarMeasure_eq_of_isProbabilityMeasure`（概率归一化后唯一）
* 左不变作用的搬运（`MeasureTheory/Group/Action.lean`，**[S]**，namespace 为 `MeasureTheory`）：
  `MeasureTheory.measure_smul (:102)`、`MeasureTheory.measure_preimage_smul (:97)`，
  条件 `[SMulInvariantMeasure G α μ]`。
  → `LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/HaarTranslateInterface.lean`
  自证的 `measure_image_mul_translate` 就是 `MeasureTheory.measure_smul` 的特例
  （群在自身上的左乘），可用现成引理替换掉 15 行自造证明。

**商测度 / |G| 因子**（`Mathlib/MeasureTheory/Group/FundamentalDomain.lean`）[C]：
* `MeasureTheory.IsFundamentalDomain (G) (s : Set α) (μ)`
* `MeasureTheory.HasFundamentalDomain`, `MeasureTheory.covolume`
* **`MeasureTheory.IsFundamentalDomain.measure_eq_card_smul_of_smul_ae_eq_self`**
  ```
  [Group G] [MulAction G α] [MeasurableSpace α] {s : Set α} {μ : Measure α}
  [MeasurableConstSMul G α] [SMulInvariantMeasure G α μ] [Countable G] [Finite G]
  (h : IsFundamentalDomain G s μ) (t : Set α) (ht : ∀ g : G, g • t =ᵐ[μ] t) :
    μ t = Nat.card G • μ (t ∩ s)
  ```
  → 这是**唯一**把 "2l" 从群论搬到测度的现成定理：若 hull 在 μ_{2l} 下 a.e. 不变，
  则 `μ hull = 2l * μ (hull ∩ 基本域)`，即商掉 μ_{2l} 后体积除以 2l。
* `MeasureTheory.QuotientMeasureEqMeasurePreimage ν μ`（`μ = (ν.restrict t).map π`），
  `QuotientMeasureEqMeasurePreimage.unique`，`IsFundamentalDomain.quotientMeasure_eq`，
  `IsFundamentalDomain.quotientMeasureEqMeasurePreimage`
* `IsFundamentalDomain.QuotientMeasureEqMeasurePreimage_HaarMeasure`（**注意：无 `MeasureTheory.` 前缀**，
  `Haar/Quotient.lean:262`，Lean 按字面前缀建名）[C]
* `IsFundamentalDomain.QuotientMeasureEqMeasurePreimage_smulHaarMeasure` [C]
* `MeasureTheory.QuotientMeasureEqMeasurePreimage.haarMeasure_quotient` [C]
  （需 `Γ.Normal`、`ν.IsMulRightInvariant`、`[PolishSpace G]`、`[HasFundamentalDomain Γ.op G ν]`、
  `[IsFiniteMeasure μ]`）—— 即 **G/Γ 上的商 Haar**，对我们的 setting 是 `K_v^× / μ_{2l}`，
  **不是** paper 的"根 torsor 商"。

**适用性 / 限制（必须写清楚）**
* 可用：Haar 的**唯一性/标量因子**（`haarScalarFactor`）可以把 S663 的"归一化约定"
  `s663Scale` 升级成"任意两个 Haar 型 log-volume 相差一个 `haarScalarFactor`"的定理；
  这对 paper-faithful 的"log-volume 与选择无关"是有内容的（但需加法版，见下）。
* 可用：`measure_eq_card_smul_of_smul_ae_eq_self` 给出 2l 因子 —— **前提是 a.e. 不变性**。
* **不可用/不要 fake**：
  - 加法版 Haar（项目用的是 `Measure.IsAddHaarMeasure`，见
    `S663ActualAverageNormalizedHaarActual.lean:35`）要 `to_additive` 孪生名
    （`addHaarMeasure_unique` 等），本 memo **没有逐个 `#check`**，用前必须验名。
  - 全代数闭包上没有 Haar（与 ledger 的 `RootThetaProductHaarGap` 一致），
    所以 invariant measure 只能活在"有限个 `rootNormedExtension` 的乘积"上
    （`PaperRootExtensionProductHaarActual.rootExtensionProductHaar := Measure.pi ...`）。
  - `QuotientMeasureEqMeasurePreimage.*` 全部是 `G ⧸ Γ` 型商；**没有**"对 torsor 的自由作用取商"
    并给出测度的定理；torsor 商要用 fundamental domain 那一套自己做。
  - 本版本**没有**"有限群作用的平均测度仍不变"的现成引理（S694 的 1/l* 平均仍要自证），
    也没有"不变测度在齐性空间上唯一"的现成定理。

---

## 4. Orbifold —— 不存在

* 全 Mathlib 8264 个文件里 `orbifold` 只出现 **1 次**，且在注释里：
  `Mathlib/Geometry/Diffeology/Basic.lean:125`：
  > `https://github.com/peabrainiac/lean-orbifolds and just needs to be upstreamed. However, some TODOs`
* 该仓库现已改名/演进为 `peabrainiac/lean-catdg`（"Categorical differential geometry in Lean"）。
  它有 `CatDG/Diffeology/LocallyModelled.lean`（diffeological orbifolds），但 README 明说：
  > "Orbifolds will have to wait until there is enough material on higher category theory in mathlib
  >  to treat them properly"
  即：**连该项目自己都认为 orbifold-as-stack 做不了**，现有的是 diffeology 局部模型意义下的 orbifold。
* 结论：**拒绝**。μ_{2l} root stack 在 Mathlib 里唯一可用的模型就是 §2 的 action groupoid
  （`ActionCategory`）+ 粗商（`MulAction.orbitRel.Quotient`），不能声称是 orbifold/栈。
  这与 S346 的现状一致：`OrbifoldStructuralSheafCarrierSpec` 的 `structuralSheafCondition`
  只能是 `Prop`，没有 `O^tri` 的载体。

## 5. Bredon —— 不存在

* 全库 `Bredon` **0 match**。
* 相关基础设施也全无：无 orbit category、无 Mackey functor、无 `EG`/`BG`、
  无 equivariant homology/cohomology（`Mathlib/AlgebraicTopology/` 只有 singular/simplicial/
  model category/Dold-Kan 等）。
* 结论：**拒绝**，且不要把它写进任何路线图（它不是"工作量"问题，是"对象不存在"）。

---

## 6. Torsor —— 可用，而且直接对上根集

文件：`Mathlib/Algebra/Torsor/Defs.lean`
* `class Torsor (G : outParam Type*) (P : Type*) [Group G] extends MulAction G P, SDiv G P`
  字段：`[nonempty : Nonempty P]`、`sdiv_smul' : ∀ p₁ p₂, (p₁ /ₛ p₂) • p₂ = p₁`、
  `smul_sdiv' : ∀ g p, (g • p) /ₛ p = g`（**:70–75**）
* 引理（**注意：这些是 root namespace，不是 `Torsor.`**）[C]：
  - `sdiv_smul : (p₁ /ₛ p₂) • p₂ = p₁`
  - `smul_sdiv : (g • p) /ₛ p = g`
  - `sdiv_mul_sdiv_cancel : (p₁ /ₛ p₂) * (p₂ /ₛ p₃) = p₁ /ₛ p₃`
  - `Torsor.subsingleton_iff : Subsingleton G ↔ Subsingleton P`
  - `Equiv.smulConst (p : P) : G ≃ P`（namespace 是 `Equiv`，**:214**）
  - `Equiv.constSDiv (p : P) : P ≃ G`（**:230**）
* 拓扑版：`Mathlib/Topology/Algebra/Group/Torsor.lean`
  `class IsTopologicalTorsor`、`Homeomorph.smulConst`、`Homeomorph.constSDiv`
* 覆盖映射版：`Mathlib/Topology/Covering/Quotient.lean`
  `structure IsQuotientCoveringMap` 与
  `noncomputable def fiberEquivGroup (e : f ⁻¹' {x}) : f ⁻¹' {x} ≃ G`
  （注释直译："Fibers of a quotient covering map by a group G is a G-torsor"）。
  这是"纤维 = G-torsor"的现成拓扑定理，但需要 `IsCoveringMap`，对代数根集是多余的拓扑。

**适用性（可直接落到现有文件）**
* `CandidateRoots T b = {r : AC T b // r ^ n = q}` 在 `rootsOfUnity n (AC T b)` 下
  **就是**一个 `Torsor`：需要给出 `SDiv`（`p₁ /ₛ p₂ := ⟨p₁.1 / p₂.1, _⟩`，用 n 次幂为 1 证明），
  然后 `Equiv.smulConst` 直接给出 `μ_n ≃ CandidateRoots`（不用 `Classical.choose`），
  `sdiv_mul_sdiv_cancel` 给 cocycle 相容性，`Torsor.subsingleton_iff` 给 S355 已有的
  `Subsingleton (RootStackCandidate)`（另一条路线）。
* 项目里 `LeanFormal/IUT/IUTII/Frobenioid/Example36TorsorTheory.lean` 的 `GTorsor`
  （229 行，free+transitive+nonempty）是 Mathlib `Torsor` 的**重复实现**：
  `GTorsor.pointEquiv` = `Equiv.smulConst`，`GTorsor.coordinate` = `(Equiv.smulConst t).symm`，
  `translate_unique` = `smul_right_cancel` 一行的推论。可无损替换/桥接。

**拒绝**
* **没有** topos- theoretic / 代数几何意义下的 G-torsor（无 "G-torsor on a site"、
  无 torsor 的下降、无 `H¹(X, G)` 分类）。

---

## 7. 附加：Kummer 理论（对 q[2l] 最贴身的一块）

文件：`Mathlib/FieldTheory/KummerExtension.lean`（570 行）+ `KummerPolynomial.lean`
（全在 root namespace，无 namespace 包裹；均 [C] 已 `#check`）
* `X_pow_sub_C_eq_prod {ζ : R} (hζ : IsPrimitiveRoot ζ n) (hn : 0 < n) (e : α ^ n = a) :
     X ^ n - C a = ∏ i ∈ range n, (X - C (ζ ^ i * α))`
  → **根集 = μ_n-轨道**的显式分解，直接把 root stack 的对象层写死成 `{ζ^i α}`。
* `X_pow_sub_C_splits_of_isPrimitiveRoot`
* `Polynomial.nthRoots n a : Multiset R`、`Polynomial.mem_nthRoots (0 < n)`、
  `Polynomial.card_nthRoots : (nthRoots n a).card ≤ n`
* `autEquivRootsOfUnity (hζ : (primitiveRoots n K).Nonempty) (hirr) (L) [IsSplittingField K L (X^n - C a)] :
     Gal(L/K) ≃* rootsOfUnity n K`
  → **"根 torsor 的自同构群 = μ_n"** 的现成同构。
* `autEquivZmod : Gal(L/K) ≃* Multiplicative (ZMod n)`
* `isCyclic_of_isSplittingField_X_pow_sub_C`、`finrank_of_isSplittingField_X_pow_sub_C : finrank K L = n`
  → **次数恰为 n = 2l**，正是 ledger 里 `QVFamRootFactorCorrectionActual`（order/(2l)）
  与 `S638PaperThetaNormalizationActual`（classical = 2l * paper）所需的 2l 来源。
* `isSplittingField_X_pow_sub_C_of_root_adjoin_eq_top`、
  `exists_root_adjoin_eq_top_of_isCyclic`（tfae 两个方向）

**限制**：这些定理要求**基域包含 μ_n**（`(primitiveRoots n K).Nonempty`）且
`X^n − a` 不可约；项目的 `AC = AlgebraicClosure K` 里 μ_n 有、但 `X^{2l} − q` 在 AC 上必然分裂，
Galois 侧信息被 AC 抹掉。因此：
* 可用的部分：根集 = μ_{2l}-轨道（`X_pow_sub_C_eq_prod`）、次数 2l、Gal ≅ μ_{2l}（在**局部域 K_v**上，
  若 `X^{2l} − q_v` 不可约）；
* 不可用：跨越到 `AC` 之后再用 Galois 对应（会退化）。

---

## 8. 对 TASK_LEDGER exact gap 的逐条判定

| ledger 的 EXACT gap | 本任务的六项能否直接补 |
|---|---|
| `ConcreteSourceQIdentification` | **否**（与 root stack/测度无关） |
| qPilot → product hull comparison/containment | **否** |
| `rootExtensionProductImageHull = paper λ·O hull`（或 log/measure 等式） | **部分**：测度侧（Haar 唯一性 + |G| 因子）可用；几何等式本身不可用 |
| `PaperXiFSourceLink` 四字段 | **否** |
| paper `StepXIContract` 字段 | **否** |
| S346/S688/S691 的 `O^tri` 载体与 `Units` 映射 | **否**：Mathlib 无 `O^tri`、无 `μ_n` 群概形、无 (*)-结构层单子；S688/S691 的"需要新载体"结论不因 Mathlib 而改变 |

---

## 9. 可执行建议（按风险排序）

* **R1（零数学风险，纯去重）**：把 S356 手写的 `rootStackCategory`/`rootStackGroupoid`
  换成 `CategoryTheory.ActionCategory (rootsOfUnity n (AC T b)) (CandidateRoots T b)`，
  白拿 `Groupoid` 实例 + `hom_as_subtype` + `stabilizerIsoEnd`（`μ_n ≃* 自同构群`）。
  同一份数学，少 30 行自造代码。
* **R2（小工作量，真内容）**：给 `CandidateRoots` 装 `Torsor (rootsOfUnity n (AC T b))` 实例，
  用 `Equiv.smulConst` 替掉 `Classical.choose` 版 `candidateRoot`；
  `sdiv_mul_sdiv_cancel` 给 cocycle 一致性。这是把"根"从"选一个"升级为"torsor"。
* **R3（有条件，别当捷径）**：若（且仅若）能为 hull 证出 `∀ g : μ_{2l}, g • hull =ᵐ hull` 且
  `SMulInvariantMeasure`/`MeasurableConstSMul` 齐备，则用
  `IsFundamentalDomain.measure_eq_card_smul_of_smul_ae_eq_self` 得到
  `μ hull = 2l • μ (hull ∩ s)`，把 S638/S640 里"除以 2l"的约定变成定理。
  **在拿到真实不变性之前不要用**——否则就是 fake 归一化。
* **R4（记录性拒绝）**：orbifold / Bredon / equivariant cohomology / 代数栈 / G-torsor
  在本 Mathlib 版本不存在；写进 AUDIT_LEDGER 作为"不要再调研/不要再排期"的负结果。
  唯一例外：`CategoryTheory.Sites.Descent.IsStack`（1-范畴下降）**不是**根栈工具，别混用。
* **R5（域层，可选用）**：需要"2l 次根的次数/伽罗瓦群"的引理时用
  `finrank_of_isSplittingField_X_pow_sub_C`、`autEquivRootsOfUnity`、`X_pow_sub_C_eq_prod`；
  前提是局部域上 `X^{2l} − q_v` 不可约，且基域含 μ_{2l}。

---

## 10. 证据与未做事项

已做：
* 读 `tmp/sheaf/xif/paper/TASK_LEDGER.md`（147 行）与 S346/S355/S356/S392/S663/
  S688/S691/PaperRootExtensionProductHaarActual 等相关实现。
* 读 `LeanFormal` 的 `HaarTranslateInterface.lean`（176 行）、`Example36TorsorTheory.lean`（229 行）。
* 全库 grep：`orbifold`(1，注释)、`Bredon`(0)、`torsor`(473 处/112 文件，全是 affine/topological 意义)、
  `rootsOfUnity` in `AlgebraicGeometry`(0)、`GroupCohomology` in 项目(0 处使用)。
* 编译 probe（`lake env lean`）：
  - `tmp/sheaf/xif/paper/S735ProbeMathlibRootStackTools.lean` —— 最终版 **exit 0**
    （`#check` 了 §1/§2/§3/§6/§7 的 [C] 名字；中途版本的 unknown-identifier 是试探错误候选名的诊断输出，
    不是项目回归）
  - `tmp/sheaf/xif/paper/S735bProbeMeasureNames.lean` —— exit 1，仅用于确认
    `measure_smul` 等不在 `MeasureTheory.Measure` 下（结论：在 `MeasureTheory` 下，[S]）。

未做（如实标注）：
* 没有写任何新定理、没有把任何 `Torsor`/`ActionCategory` 实例接到项目里（只做调研）。
* 没有 `#check` 加法版 Haar（`addHaarMeasure_unique` 等）；没有验证 `MeasurableConstSMul`
  在 p-adic 乘积上的实例能否合成。
* 没有跑全项目 `lake build`（本任务只新增两个未被任何 lib 引用的 probe 文件）。
