# FEAS-KLEIN — Klein forms / Siegel units / Faltings delta 的 arch 显式公式 (A1094)

| field | value |
|---|---|
| Status | ANALYSIS (no Lean, no compile); external claims = LITERATURE（已检索确认部分标题/概念） |
| 判定 | **A-候选（最有希望的外部路线）**：Kronecker 极限公式/Siegel 单位 arch 公式是**显式标准公式**，可把 arch 估计化为显式计算；但需 (i) theta→Klein/Siegel 的乘积映射，(ii) 公式形式化，(iii) 显式不等式。当前未形式化 ⇒ 条件性 A，否则 B |

## 1. 现成显式公式（LITERATURE）

### 1.1 Kronecker 极限公式（Kronecker limit formula）
对实解析 Eisenstein 级数 `E(z,s)` 在 `s=1` 的 Laurent 展开：
```
E(z,1+ε) = π/ε + 4π( γ - log 2 - log( √y·|η(z)|² ) ) + O(ε),   y = Im τ
```
⇒ `η(z)` 的 arch 范数**显式**：`-log(√y|η(z)|²)` 可用 `y` 与 `|η|` 表达。
这是**标准定理**（经典），是 Kleinian 显式 arch 度量的基础。

### 1.2 Klein 形式（Klein forms）
对 `(a,b) ∈ (1/N Z)²`，Klein 形式 `𝔨_{(a,b)}(z)` 是 `O(D)` 的显式截面（theta 商/eta 乘幂），
其 arch 范数由 Kronecker 极限公式/theta 变换公式给出**显式表达式**（含 `y`、`N`、`η` 项）。
（标准；具体常数需按定义逐项写出。）

### 1.3 Siegel units 的 arch 范数
Siegel units `g_a`（a ∈ (1/N Z)²）的 arch 范数有显式公式（Kato/Robert 传统；
经典形式含 `η` 乘积与 Eisenstein 项），且 Siegel units 在模曲线上的整性/生成性已知 ⇒
**有限位整性**也有标准结论。

### 1.4 Faltings delta 的 arch 项
`Faltings delta`（δ-invariant）的 arch 项在 Bost–Künnemann/Robert 框架下有显式公式；
模曲线情形可由 `η` 乘积/Green 函数显式计算。
（LITERATURE；本仓无形式化。）

## 2. 与我们的 theta 乘积截面的映射（需要的关键步骤）

我们的截面（A1087/A1088 模板）：
```
s = ∏_{j=1..nC} θ(u_j)^{j^2},     u_j = torsion 点
```
若能证明**乘积映射**：
```
∏_j θ(u_j)^{j^2} = (∏_k 𝔨_{(a_k,b_k)}(z)) · η(z)^{M} · (显式常数)      (MAPPING)
```
其中 `u_j` 对应 `(a_k,b_k)` 的 Kleinian 参数（`θ` 的变换公式给出精确商），
则 arch 范数 = 由 §1 的显式公式给出 ⇒ **arch 估计化为显式表达式**（不再需要新的泛函分析）。
同时 Siegel units 的整性 ⇒ 有限位 `v_p ≥ 0`。

**MAPPING 的证据来源**：theta 变换公式（`θ(z+πτ)` 变换）+ Klein 形式的 theta 商定义 + eta 乘积；
属标准恒等式，但需逐项形式化（q-展开/变换公式）。

## 3. 判定（A/B/C）

| 子命题 | 类型 | 理由 |
|---|---|---|
| arch 范数存在显式公式 | **A 输入（LITERATURE）** | Kronecker 极限/Siegel 单位公式是标准定理 |
| theta 乘积 = Klein/Siegel 乘积 | **需新形式化（MAPPING）** | 标准恒等式，但不在本仓；形式化成本中等 |
| 显式公式 ⇒ 我们的 `arch_le`（≤0 或 ≤常数） | **A 条件** | 若显式表达式在 `y`/`N` 上可证 ≤0（或经归一化吸收） |
| 有限位整性 | **A** | Siegel units 整性/Kato，标准 |
| 合成 hcmp | **A（条件性）** | 全部输入均为标准公式 + 可证恒等式/不等式 |

**结论：Klein/Siegel 路线是 A-候选**（优于 Deligne 路线的 B+新解析输入），
前提是 (i) MAPPING 形式化，(ii) Kronecker/Siegel 显式公式作为 LITERATURE 输入形式化，
(iii) 显式不等式可证。若 MAPPING 或显式不等式不可行，则退回 B。

## 4. 所需映射与估计清单

1. **MAPPING**：`∏_j θ(u_j)^{j²}` → `∏_k 𝔨_{(a_k,b_k)} · η^M`（theta 变换/eta 乘积）；
2. **ARCH-FORMULA**：Kronecker 极限公式的 `η` 项 + Klein 形式的 `y,N` 显式式（LITERATURE）；
3. **ARCH-BOUND**：由显式式证明 `Σ_arch log‖s‖_σ ≤ 0`（或 ≤ C，C 归一化吸收）；
4. **FINITE-INTEGRALITY**：Siegel units 的整性 ⇒ `v_p(s) ≥ 0`（LITERATURE + q-展开）；
5. **NORMALIZATION**：det bundle 度量与 `−sF·A` 归一化一致（A1087 §1 的符号约定）。

## 5. Lean 签名草案

```lean
/-- External (LITERATURE) explicit arch formula input. -/
structure KleinArchFormulaData where
  -- abstract: arch log-norm of a Klein/Siegel product, explicit in y and N
  y : Real
  N : Nat
  archLogNorm : Real
  formula : Prop      -- archLogNorm = explicit expression (Kronecker limit/Siegel unit)

/-- The theta-product section equals a Klein/Siegel product (MAPPING). -/
def ThetaAsKleinProduct (s : Real) (kleinProduct : Real) : Prop := s = kleinProduct

/-- Arch bound from the explicit formula. -/
theorem arch_le_of_klein (F : KleinArchFormulaData)
    (h : F.archLogNorm ≤ 0) : F.archLogNorm ≤ 0 := h

/-- Finite integrality from Siegel units (LITERATURE). -/
structure SiegelIntegralityData where
  finiteIndex : Real
  integral : 0 ≤ finiteIndex

/-- Assemble ThetaSectionData (A1088) from Klein/Siegel inputs. -/
def thetaSectionDataOfKlein (F : KleinArchFormulaData) (I : SiegelIntegralityData)
    (harch : F.archLogNorm ≤ 0) (hmapping : Prop) : ThetaSectionData :=
  { Bundle := Unit, degree := I.finiteIndex - F.archLogNorm,
    section := (), section_nonzero := True, nC := 0, theta := Fin.elim0,
    section_eq_prod := True, arch_bound := F.archLogNorm,
    finite_index := I.finiteIndex, arch_le := harch, finite_ge := I.integral,
    deg_eq := rfl, arch_source := True, finite_source := True }
```

## 6. 结论

1. Kronecker 极限公式 + Klein forms + Siegel units + Faltings delta 提供**显式 arch 公式**
   （标准文献，非新解析输入）⇒ 这是目前最接近 **A** 的外部路线；
2. 关键剩余步骤 = **MAPPING**（theta 乘积 → Klein/Siegel 乘积，标准恒等式但需形式化）
   + 显式不等式的算术化；
3. 与 Deligne 路线（B+新解析输入）相比，Klein/Siegel 路线把 arch 估计替换为**已证公式**，
   因此判定为 **A-候选**；若 MAPPING 完成且显式不等式可证，则升为 A；
4. 有限位整性由 Siegel units 的整性给出（标准），与我们的 `ordp_qrootOf`/tame 可对接；
5. 建议：先形式化 MAPPING（theta 变换/eta 乘积恒等式）作为下一具体任务。