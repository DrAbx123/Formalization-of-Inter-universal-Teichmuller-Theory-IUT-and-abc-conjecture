# THETA-SECTION-PLAN — Deligne 路线的 theta 乘积截面草案 (A1087)

| field | value |
|---|---|
| Status | LITERATURE/PLAN (符号约定固定 + 截面构造草案 + 两个估计拆分；无 Lean、无编译) |
| 前文 | `coord/OUTSIDE-DELIGNE.md`（arXiv:1106.0255 Deligne pairing；deg 公式） |

## 1. 符号约定（固定）

采用与 lead/外部文献一致的 Arakelov 度（`[K:Q]=1` 记，一般情形除以 `[K:Q]`）：
```
deg^(L) := (1/[K:Q]) * ( Σ_{arch v} log‖s‖_v  −  Σ_{finite p} log #(L_p / O_p·s) )
```
则：
- `s` 在有限位**生成**（`#(L_p/O_p s)=1`，即整性/trivializing）且 arch 位 `‖s‖_v ≤ 1`
  ⇒ `deg^(L) ≤ 0`（**小范数截面 ⇒ 度≤0**）✓ 与 lead 一致；
- 若仓库/其他文档的 hcmp 采用相反符号，则定义 `hcmp := (deg^(L) ≤ 0)` 并显式翻转；
  **不再两套符号混用**。

**hcmp 形式**（Form C）：
```
hcmp  :=  deg^(DetBundle) ≤ 0
      ⇔  Σ_arch log‖s‖_v ≤ Σ_fin log#(L_p/O_p s)
```

## 2. theta 乘积截面的精确构造草案

### 2.1 对象
```
E/F 椭圆曲线（我们的 E over F）；固定 ample line bundle O(1) = O([0])。
DetBundle := det Rπ_* O(n[0]) 的 Deligne 配对/ determinant（或 det of localizations，
            与 S1422 det⊗M 的簿记一致：detTensorPower = G•S 型）。
u_j (j=1..nC) : 取模 l 表示/Θ 数据给出的 torsion 点（例如 E[l]-torsion 在 K 上的点），
             u_j 的选择与 paper 的 j∈F_l^* 指标一致。
theta 截面 : ϑ ∈ H^0(O([0])) 的 theta 函数（经典 θ(z,τ)，或 theta 值的 p 进/arch 版本）。
```
### 2.2 截面定义
```
s := (⊗_j ϑ_{j^2}(u_j))  的 Deligne 配对/张量积截面
   ≈  ∏_{j=1..nC} θ(u_j)^{j^2}       （scalar theta 值乘积；精确用张量积/配对表达）
```
- `s ≠ 0`：每个 `θ(u_j)` 在 torsion 点非零（theta 值的经典非零性；需避免 theta divisor），
- 截面所在 detBundle 的度量 = Deligne pairing metric（与 S1422 `distribHaarChar`/`hchar` 对齐）。

### 2.3 有限位 valuation（草案）
```
v_p(s) = Σ_j j^2 * v_p(θ(u_j))
```
- good reduction 位：`θ(u_j)` 为 p 进整数/单位（theta 的整性），`v_p ≥ 0`；
- bad/ramified 位：用 `ordp_qrootOf`（= qOrder/(2l·e_w)）与 tame 展开（VcI:403-435）控制；
- 目标：所有 `v_p(s) ≥ 0`（或强形式：s 在每 p 生成 detBundle）。

## 3. 两个独立估计（分解）

### (a) arch 位 sup-范数界（解析输入，GAP-ARCH-THETA）
**待证陈述**：
```
for all arch places σ,  ‖s‖_σ = ∏_j |θ(u_j)|_σ^{j^2} ≤ 1
（或 ≤ C，C 可由归一化吸收）
```
**所需解析输入**（LITERATURE，未形式化）：
1. theta 函数的 Fourier 展开与 sup 界：`sup_z |θ(z,τ)| ≤ ...`（Im τ 下界）；
2. Petersson 范数公式：`∫_{E(ℂ)} |θ|² dμ` 与 `Im τ` 的关系；
3. Fay 的 theta 恒等式（torsion 点处 θ 值的乘积恒等式）；
4. j-average 的 arch 版本：`Σ_j j²·log|θ(u_j)|` 与 `sF` 型系数的对应；
5. `u_j` 的 arch 位置（torsion 点高度）与控制。
**状态**：标准但非平凡；先写待证陈述 + 解析输入清单，不伪造证明。

### (b) 有限位整性/生成性（可部分用现有 green 标量）
**待证陈述**：
```
for all p, v_p(s) >= 0,  且（强形式）s 生成 detBundle at p
```
**现有工具**：
- `ordp_qrootOf`（= qOrder/(2l·e_w)，Data:327-330）；
- `S3050Unit_eq_log_norm_div`（= **-log‖x‖/(2l)**，A1070 符号修正，green）；
- `S3016StepVQPilot`/`S3029` per-label 仿射（green）；
- tame 展开 `componentVol = Σ(1−1/e)logp`（VcI:403-435，green-by-source）；
- `S1422 detDataOfHull`（`hchar` 归一化）+ `S1418` det⊗M。
**缺口**：`θ(u_j)` 的 p 进整性（theta 值在 bad 位的 valuation）与 `s` 生成性的 p 进论证；
需把 `v_p(θ(u_j))` 与 `qOrder/(2l e_w)` 对齐（GAP-PVAL-THETA）。

## 4. 合成：hcmp 的截面证明模板

```
若 (a) arch: ‖s‖_σ ≤ 1 且 (b) finite: v_p(s) ≥ 0（生成）
则 deg^(DetBundle) = (1/[K:Q])(Σ_arch log‖s‖ − Σ_fin log#) ≤ 0
⇒ hcmp 成立。
```
所需的唯一结构对象：`ThetaSectionData`（detBundle + theta 点族 u_j + s + 两条估计）。

## 5. Lean 签名草案

```lean
/-- Abstract determinant-bundle section data for the theta-product route. -/
structure ThetaSectionData where
  -- det bundle data (abstract)
  Bundle : Type
  degree : Real
  section : Bundle
  section_ne_zero : section ≠ []
  -- theta product representation
  nC : Nat
  u : Fin nC → Type        -- theta points (abstract carrier)
  theta : (j : Fin nC) → u j → Real   -- theta value at u_j
  section_eq_prod : True   -- placeholder: section = ∏_j theta(u_j)^{j^2}
  -- estimates
  arch_bound : Real        -- Σ_arch log‖section‖_σ
  finite_index : Real      -- Σ_p log#(detBundle_p / O_p·section)
  arch_le : arch_bound ≤ 0          -- (a) small arch norm
  finite_ge : 0 ≤ finite_index      -- (b) integrality/generation
  deg_eq : degree = finite_index - arch_bound   -- sign convention of §1

/-- `ThetaSectionData` ⇒ det bundle degree ≤ 0 ⇒ hcmp. -/
theorem hcmp_of_theta_section (D : ThetaSectionData) : D.degree ≤ 0 := by
  rw [D.deg_eq]
  linarith [D.arch_le, D.finite_ge]

/-- Form C hcmp as the det-bundle degree nonpositivity. -/
def FormC_Hcmp (D : ThetaSectionData) : Prop := D.degree ≤ 0
```

## 6. 结论

1. **符号约定固定**：`deg = (Σ_arch log‖s‖ − Σ_fin log#)/[K:Q]`；小范数截面（‖s‖≤1, 有限位生成）
   ⇒ `deg ≤ 0` ⇒ `hcmp`；若 hcmp 反向，则显式取 `-deg` 并记录；
2. **截面构造**：`s = ∏_j θ(u_j)^{j²}`（Deligne pairing 张量积形式），u_j 为模 l 表示的 torsion 点；
3. **两个独立估计**：
   (a) GAP-ARCH-THETA：arch sup/Petersson/Fay 估计（标准解析输入，未形式化）；
   (b) GAP-PVAL-THETA：有限位整性/生成性（可用 `ordp_qrootOf`/S3050/tame 部分，缺 theta valuation 对齐）；
4. Lean 模板 `ThetaSectionData` + `hcmp_of_theta_section`（纯算术，真证）；
5. 下一步：先形式化 (b)（与现有 green 标量接近），(a) 作为 ARCH-THETA-GAP 登记（需 Petersson/Fay 解析输入）。