# CHAIN2-G-CANDIDATES — 链二 Step (xii) 约束 G 的仓库候选

日期：2026-11-12；qpilot（A881；A884 状态核；A890 行号修正）。**所有 lana 路径相对根 `Iut/` 树（`D:/lean/Iut/...`）。** **状态：源级已核（文件:行）；候选 lana 文件的 olean 未产**——`Iut/LogLink/Thm311Rest`、`Iut/Concrete/Ind1Invariance`、`Iut/Concrete/LocalConstruct/{ScaleVolume,Prop14}`、`Iut/Tripod/{CyclicBound,CyclicIsogeny}` 的 olean 仍在根 Iut 闭包构建队列中。**不得当 green 引用。**

| candidate | 源文件:行 | olean | 状态 |
|---|---|---|---|
| G1 `rlf_unique` | `Iut/LogLink/Thm311Rest.lean:473`（`:479` `rlf_cocycle`；`:491` `mem_rposOrbit_iff`；`:523` `rlfData`；`:529` `Thm15v.unique`；文档 L78–90） | 未产 | 源级已核；候选 |
| G2 `componentVol_image_algEquiv` | `Iut/Concrete/Ind1Invariance.lean:144`, `:192`, `:110` | 未产 | 源级已核；候选 |
| G3 `componentVol_prod_incl_smul_integral` | `Iut/Concrete/LocalConstruct/ScaleVolume.lean:118`；`Prop14.lean:108` | 未产 | 源级已核；候选 |

## 0. 结论（先给）

**Step (xii) 没有逐字出现于 lana 源码**（在 `Iut/Concrete|Tripod|LogLink|WallEquiv|Cor312|Implication` 全目录 grep `Step (xii)`/`xii`/`rigid` 无命中；ROUTES §14 的 Step (xii) 是论文描述）。**A896 更正：G1/G2/G3 都不是约束候选；旧稿的“最接近 G”判断已废，见 §5。**

## 1. G 候选表（A881 旧稿；A896 已废：G1/G2/G3 不是约束候选，见 §5）

| ID | 候选 G | 精确陈述（源） | 强度 | 对链二位置约束的作用 |
|---|---|---|---|---|
| **G1** | **realified line family 的 equal-product-formula 唯一性（Thm 1.5(v)）** | `Iut/LogLink/Thm311Rest.lean:473 theorem rlf_unique (B B' : ValBPS V bad) (h : B.PF = B'.PF) : Nonempty (Unique (B.Iso B'))`；`rlf_cocycle`（`:479`）；`mem_rposOrbit_iff`（`:491`）；`:523` `def rlfData`；`:529` `Thm15v.unique`；文档 L78–90：“for families of value-group BPSs with **equal product formulas**, the isomorphism between any two members exists and is unique … Θ-links act by positive scaling `1/s` in degree coordinates (`ThetaLinkIso.val_apply`) and on the global realified Frobenioid exactly `ThetaLink.scaling_iff` carries Θ-pilot to q-pilot”。`scaling_iff` 定义在 `Iut/ThetaLink/Link.lean:206`（`Thm311Rest.lean:559` 是 usage `frobScale`）。 | **强刚性**：给定相等乘积公式，成员间同构存在且唯一（不是“差有界”，是“唯一”）。 | 若链二的 𝔥 族（不同全纯结构）都要与 q-pilot 的 realified line/degree 数据一致，则 `rlf_unique` 把“可能像之并”**塌缩为单个区域**（所有成员唯一同构），**A896 已废：这只是唯一同构，不是 G 约束；`RposOrbit` 仅共用正数 c，不限制族/体积。****风险**：不同 𝔥 可能给出不同 PF，则被 G 排除；需证 q-pilot 的实现∈族（§14 链二隐藏条件）。 |
| **G2** | **componentVol 的模型/结构不变性** | `Iut/Concrete/Ind1Invariance.lean:144 theorem componentVol_image_algEquiv (E : Tensor K vQ c ≃ₐ[baseField vQ] Tensor K vQ c') (S) : componentVol vQ c' (E '' S) = componentVol vQ c S`；`:192 theorem IsLeastHull.componentVol_eq ... componentVol vQ c' (b • integralAt vQ c') = componentVol vQ c (a • integralAt vQ c)`；`:110 componentVol_image_linearEquiv`。 | **中等（不变性，不直接给上界）**：体积在保整结构的结构同构/最小壳下不变。 | G 的“整体次数良定义”部分：容器换 𝔥 不改变归一化 log-volume（只要保 integral 结构）；保证链二的 P(v,j) 体积是结构无关的函数，从而“并”有定义。**不单独约束**（不排除大并集）。 |
| **G3** | **componentVol 的精确乘积/标度律（global degree 恒等式）** | `Iut/Concrete/LocalConstruct/ScaleVolume.lean:118 theorem componentVol_prod_incl_smul_integral ... : componentVol (.finite p) c ((∏ j, incl p c j (w j) (h j) (y j)) • integral p c) = -(∑ j, ordp K (w j) (y j)) * R`；`Iut/Concrete/LocalConstruct/Prop14.lean:108 theorem componentVol_prime_pow_smul_integral ... : componentVol (.finite p) c (((p:ℕ):Tensor…)^m • integral p c) = -(m:ℝ)*Real.log p`。 | **强（精确恒等式）**：乘积选择的整体 log-volume = 各位 ord 的加权和（R 为归一化因子）。 | 给 G 提供**显式公式**：一旦 (𝔥_v) 的选择被编码为局部 pilot 乘积，G 的“同一个整体次数”约束 = 该乘积的 ord 和相等/有界；可直接计算并集体积，判定绑定强度。 |
| G4（弱，备选） | 整体高度分解 + 非 graph 部分有界 | `Iut/Tripod/CyclicBound.lean:180 theorem h_eq_heightOn_graph_add … : P.h x = heightOn(IsGraphPlace)+heightOn(¬IsGraphPlace)`；`:239 def CyclicGraphBoundHyp (TK : ℝ) : Prop`；`:253 cyclicBound_of`；`Iut/Tripod/CyclicIsogeny.lean:933 theorem main_bound … : ((ℓ−1)/4)*(P.h x − heightEq 2) ≤ 10 log ℓ + (2 log(32C₀)+6K.c+4 log4)`。 | **弱/假设型**：`CyclicGraphBoundHyp TK` 作为输入，不是已证绑定。 | 链二若只求“G 存在”的例子，可用它作为**条件 G**（非 graph 部分 ≤ TK），但它不约束 𝔥 族的选择；只能作为数值实例，不足以判定链二。 |

## 2. A881 旧稿（A896 已废；仅保留源级记录）

**A881 旧稿（A896 已废，非首选）：G1 = `rlf_unique` + `ThetaLink.scaling_iff`**
- 源（根 `Iut/` 树）：`Iut/LogLink/Thm311Rest.lean:473`（`:479`/`:491`/`:523`/`:529`）、L78–90 文档、`ThetaLink.scaling_iff` 定义在 `Iut/ThetaLink/Link.lean:206`（`Thm311Rest.lean:559` 为 usage）；源级定位已核，olean 待根构建。
- 强度：唯一同构（强），直接实现“成员选择无自由度”的 G；`scaling_iff`（根 `Iut/` 树 `Iut/ThetaLink/Link.lean:206`）**精确刻画**：只有 `c = wallS⁻¹` 的 `ℝ_{>0}` 标度才把 Θ-pilot 对象送到 q-pilot 对象——无连续自由度。
- **A896 已废**：旧稿曾称其为 Step (xii) 型最佳对应；现只保留源级唯一性记录，不再作 G 约束。

**真实候选 2：G2 = `componentVol_image_algEquiv` / `IsLeastHull.componentVol_eq`（体积的模型不变性）**
- 源：`Iut/Concrete/Ind1Invariance.lean:144,192`。强度中等；保证 P(v,j) 体积良定义、与结构选择无关；不单独产生上界。

**真实候选 3：G3 = `componentVol_prod_incl_smul_integral` + `componentVol_prime_pow_smul_integral`（整体次数显式恒等式）**
- 源：`Iut/Concrete/LocalConstruct/ScaleVolume.lean:118`、`Prop14.lean:108`。强度强（精确公式）；给 G 的可计算形式（ord 和），可用于计算并集体积对 𝔥 区间的依赖。

## 3. 对链二的含义 / 需要什么才能判定

- 链二的 G 若要“太强则 q-pilot 不在族里、太弱则并集过大”，最自然的形式化 G 是 **G1（相等 PF ⇒ 唯一同构）**；G2/G3 提供良定义与可计算体积。
- 判定链二所需新内容：**(a)** q-pilot 的 (1,0) 实现属于 𝔥 族（成员资格）；**(b)** 对族内不同 𝔥 的 PF/ord 和的分布计算（G3 给出公式）；**(c)** 若 PF 不等价，G1 不适用 ⇒ G 需换成 G3 型不等式约束（此时“绑定条件”就是新内容）。
- 本文件只做源级候选定位；候选文件 olean 尚未产出（根 Iut 闭包构建中，见 `tmp/iut_root/progress.json`），不宣称已编译。

## 4. 检索记录

- `Step (xii)` / `xii`：lana `Iut/Concrete|Tripod|LogLink|WallEquiv|Cor312|Implication` 无命中（源中只有 `Step (xi)`，`Thm311Rest.lean:621`）。
- `rigid`/`rigidity`：`Iut/Concrete/TorsionFieldGalois.lean:17`（3-torsion rigidity）、`Iut/LogLink/GalKummer.lean:68`、`StripKummer.lean:17`、`Thm311Rest.lean:23,258`（cyclotomic rigidity）——多为局部刚性，非全局次数 G；G1 的 `rlf_unique` 是唯一直接“唯一同构”的全局陈述。
- `componentVol` 检索：`Iut/Concrete/Container.lean:26-31`（归一化：权重 `[k_w:ℚ_v]/[k:ℚ]`，和为 1）、`Ind1Invariance:110,144,192`、`LocalEstimate:73`、`Admissible:99`、`Prop14:108,131,156`、`ScaleVolume:14,52,118`。
## 5. A896 correction (authoritative)

**G1/G2/G3 都不是 Step (xii) 意义下的约束候选，删除 G1 首选。**

- **G1 `rlf_unique`**: 只证明“相等 PF ⇒ 成员间唯一同构”；`RposOrbit` 只是共用正数 c，**不限制族的选择/体积**；`Iut/Wall/Wall.lean:27` 说明 `1/s` 不作用于容器。不能把 `rlf_unique` 当 G。
- **G2 `componentVol_image_algEquiv`**: 只给 `VolShell` 良定义/结构无关；不产生约束/上界。
- **G3 `componentVol_prod_incl_smul_integral`**: 只给精确标度律 `-(sum ord)*R`；是先有 G 后计算体积的工具，不是 G 本身。
- **没有“G 候选”**: 真正的 G 定义/来源仍是未解决数学输入；G1 仅可作 rlf 唯一性输入，不是约束。
- 若后续有新的 G 候选，必须给出明确约束谓词，不能复用这三个定义。
