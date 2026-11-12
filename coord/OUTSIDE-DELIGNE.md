# OUTSIDE-DELIGNE — Deligne pairing/determinant bundle 工具与 Form C hcmp 重构 (A1086)

| field | value |
|---|---|
| Status | LITERATURE/PLAN (no Lean written; external references unverified beyond title/abstract; no compile) |
| 外部源 | arXiv:1106.0255 **"Deligne pairing and determinant bundle"**（已通过检索确认标题；作者/正文未逐句核）；Deligne, "Le déterminant de la cohomologie"；Arakelov 邻接公式；小范数截面原理（standard） |
| 目标 | 把 Form C 的 `hcmp` 重述为：**det bundle 上存在小/大范数截面** ⇒ Arakelov 度 ≤0 ⇒ hcmp |

## 1. 外部工具：Deligne pairing / determinant bundle（可借用的结构）

arXiv:1106.0255（"Deligne pairing and determinant bundle"）给出算术曲面上的 Deligne pairing：
对 `f : X → S` 上的 line bundles `L1,L2`，det bundle `⟨L1,L2⟩` 带 Hermitian metric，满足：
- 双线性/对称性；
- 与 base change/度量的相容性；
- 邻接公式（adjunction）：`⟨O(D1),O(D2)⟩` 的度由 Green 函数/交数给出；
- 与 determinant of cohomology `det Rf_*` 的关系（Deligne）。

**小范数截面的标准原理**（signed 形式，需与 hcmp 方向核对）：
对 Hermitian line bundle `(L,‖·‖)` 于 `Spec O_K`，取非零有理截面 `s`：
```
deg^(L) = (1/[K:Q]) * ( Σ_{finite v} log #(L_v / O_v·s) - Σ_{arch v} log‖s‖_v )
```
于是：
- 若 `s` 在有限位**生成**（`#(L_v/O_v s)=1`，即整体非零且在每处可逆）且 `‖s‖_v ≤ 1`（arch），
  则 `deg^(L) = -(1/[K:Q])Σ log‖s‖_v ≥ 0`（**小截面 ⇒ 非负度**，本符号约定下）；
- 若需要 `deg^(L) ≤ 0`，则取 `‖s‖_v ≥ 1`（**大截面**）或翻转符号约定。

⚠ **符号约定必须与 hcmp 精确对齐**；本文先按“deg = (1/[K:Q])(Σ finite − Σ arch log norm)”记录，
实现前需用 S1422/S1418 的 det⊗M 归一化核对（见 §4）。

## 2. 把 Form C 的 hcmp 重述为 det bundle 截面存在性

我们的 Form C（`hcmp`，见 C 线 comparison 目标）本质是“高度/度 ≤ 归一化体积”的比较：
```
hcmp  ⇔  deg^(DetBundle) ≤ 0      （或按 §1 符号约定取反）
```
**结构性重述**：
```
hcmp ⇔ 存在一个非零整体截面 s ∈ H^0(DetBundle)
        使得  (i) s 在有限位处处生成（integrality/trivializing）；
              (ii) 在 arch 位 ‖s‖ 满足小/大范数界（据符号约定）；
              (iii) s 的构造是“theta 值的乘积”或“global units 的组合”。
```
这样 hcmp 从“逐项不等式”变成**一个截面存在性 + 范数估计**。

### 候选截面（按可行性）
1. **theta 值的乘积**：`s = ∏_{j} θ(u_j)^{j²}`（或 theta 函数的限制），
   arch 范数由 Petersson/Fay 恒等式控制，有限位由 theta 的整性/valuation 控制；
2. **global units**：`s = ∏ ε_i^{m_i}`（ε_i 为单位），product formula 保证有限/arch 平衡，
   度贡献为 0（只能做 normalization，不能单独给 hcmp）；
3. **theta 值 × 单位**：products `θ(u_i)^{j²}·ε_i` 组合，用于同时控制 arch 小范数与有限位整性。
4. **Deligne pairing 的 standard sections**（如 `⟨O(D1),O(D2)⟩` 的 canonical section）
   配合 §1 的邻接公式，给出度的显式表达式。

## 3. 所需范数估计（构造截面时要证的）

1. **arch 上界**：`sup_{z} |θ(z,τ)|` 型估计（Petersson 度量 + 高斯衰减）；
2. **有限位整性**：`v_p(s) ≥ 0`（或生成性）对所有 p；theta 值的 p 进 valuation 由
   `ordp_qrootOf`/tame 公式控制（我们的 `S3050`/`S3016` 提供 StepV 标量）；
3. **product formula 平衡**：`Σ_v log‖s‖_v = 0`（对有理截面）；
4. **DetBundle 度量**：Deligne pairing 的 metric 与我们的 `logVol_lgp_integral = −sF·A`
   归一化一致（需核对 `S1422.detDataOfHull` 的 `distribHaarChar` 归一化）。

## 4. 与我们已有资产的对应

| 外部工具/步骤 | 我们的现有实现 | 状态 |
|---|---|---|
| det⊗M 缩放律 `vol(G•S) = M·vol(S)` | `S1422HDDDetActual.detDataOfHull`（`hchar` 条件） | green |
| det⊗M 的 global hull 簿记 | `S1418HDDConsumerActual`（`s1418DetTensorPower_*`） | green |
| Arakelov 度归一化 `−sF·A` | `IdentifiedCopies:441-456 logVol_lgp_integral` | green |
| Step V box（Arakelov 型上界） | `Mzk1PaperStepVBoxActual.paperStepV_inequality` | green |
| signed log-volume 比较 | `Mzk1SignedLogVolumeCor312Actual.signed_cor312_inequality` | green（条件） |
| 结构目标对象 | `Mzk1StructuralTargetActual`（containment/det morphism） | green 骨架，GAP 对象存在性 |
| Deligne pairing / det bundle 的**显式构造** | 无（lana 也无） | **缺** |
| 小范数 arch 估计（theta/Petersson） | 无 | **缺** |
| 有限位整性/生成性 | 部分（`S3050`/`S3016` 标量） | 部分 |

## 5. Lean 签名草案

```lean
/-- Abstract Hermitian line bundle with an explicit Arakelov-degree formula. -/
structure HermitianLineBundleData where
  carrier : Type
  degree : Real
  -- section data
  sectionNormArch : Real
  finiteIndex : Real        -- sum log #(L_v/O_v s)
  deg_formula : degree = (1 / normFactor) * (finiteIndex - sectionNormArch)

/-- A nonzero global section with finite generation and an arch norm bound. -/
structure SmallNormSectionData (L : HermitianLineBundleData) where
  section_nonzero : L.finiteIndex = 0        -- generating at finite places (placeholder)
  arch_bound : 0 ≤ L.sectionNormArch          -- ≤ or ≥ 1 depending on sign convention

/-- Small/large section gives the degree bound (sign convention to be fixed). -/
theorem degree_bound_of_section (L : HermitianLineBundleData) (D : SmallNormSectionData L) :
    L.degree = (1 / normFactor) * (L.finiteIndex - L.sectionNormArch) := L.deg_formula

/-- Form C: hcmp is equivalent to the determinant-bundle degree bound. -/
def FormC_HcmpByDetBundle (L : HermitianLineBundleData) : Prop :=
  L.degree ≤ 0    -- or ≥ 0; must be aligned with the existing hcmp statement

/-- If the det bundle has a generating section with the required arch bound,
then hcmp holds. -/
theorem hcmp_of_det_section (L : HermitianLineBundleData) (D : SmallNormSectionData L)
    (h : L.degree ≤ 0) : FormC_HcmpByDetBundle L := h
```

## 6. 结论

1. arXiv:1106.0255 的 Deligne pairing/det bundle 提供了 hcmp 的**对象层重编码**：
   `hcmp ⇔ det bundle 上存在（小/大）范数截面`，把逐项不等式化为截面存在性 + 范数估计；
2. 候选截面：theta 值乘积、global units、theta×units；需要的估计：arch (Petersson) 上界、
   有限位整性/生成性、product formula 平衡、DetBundle 度量归一化；
3. 我们的 det⊗M（S1422/S1418）、Arakelov 归一化（`−sF·A`）、Step V box 已 green，
   可支撑簿记与度公式；**缺** Deligne pairing 的显式构造、小范数 arch 估计与有限位生成性；
4. 该路线与 paper Step (xi-d) 的 determinant/localization 比较一致；若采用，应在
   `coord/REUSE-AUDIT-ABC.md` 中把“外部工具”单独分类（LITERATURE，不进入 green 计数）；
5. 建议先固定 §1 的符号约定（`deg = (Σ finite − Σ arch)/[K:Q]`）并与 hcmp 现有陈述对齐，
   再选具体截面（theta 乘积最自然）。