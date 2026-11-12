# G1-FIELD-SPEC — `rlf_unique` / `scaling_iff` 的字段级规格（给 abc 的链二 G1）

日期：2026-11-12；qpilot（A884；A890 行号修正）。**所有 lana 路径相对根 `Iut/` 树（`D:/lean/Iut/...`）。** **源读取的字段/类型规格**；相关文件 olean 部分已编（`Iut/Wall/BPS.lean` 等仍属根闭包待编；本文件不宣称编译）。

## 0. 一句话

链二的 G1 可落成两个**字段级输入**：(i) 一个 **value-group BPS** `B : ValBPS V bad`（其 `PF B ⊆ V →₀ ℝ` 由 `sumMap` 的核定义）；(ii) 一个**精确的 ℝ_{>0} 标度约束** `c = wallS⁻¹`（`scaling_iff`）。输出是：PF 相等 ⇒ 成员间**唯一**同构（`rlf_unique`），以及 Θ-pilot 与 q-pilot 只能在 `1/s` 标度下等同（`isEmpty_iso_thetaPilot_qPilot` 说明不能在同一 global realified Frobenioid 内同构）。

## 1. 输入 A：value-group BPS（`Iut/Wall/BPS.lean:175 structure ValBPS (V : Type) (bad : Finset V)`）

| 字段 | 类型/陈述 | 源 |
|---|---|---|
| `C` | `Type`（一维实向量空间） | `Iut/Wall/BPS.lean:175` |
| `instAddCommGroup` | `AddCommGroup C` | 同上 |
| `instModule` | `Module ℝ C` | 同上 |
| `finrank_eq_one` | `Module.finrank ℝ C = 1` | 同上 |
| `localPilot` | `V → C`（局部 pilot，全部非零） | 同上 |
| `localPilot_ne_zero` | `∀ v, localPilot v ≠ 0` | 同上 |
| `pilot_ne_zero` | `∑ v ∈ bad, localPilot v ≠ 0`（pilot `φ_C` 非零） | 同上 |

**派生定义**：
- `ValBPS.pilot B : B.C := ∑ v ∈ bad, B.localPilot v`（`BPS.lean` `def pilot`）；
- `ValBPS.sumMap B : (V →₀ ℝ) →ₗ[ℝ] B.C := Finsupp.linearCombination ℝ B.localPilot`（`def sumMap`）；
- **`ValBPS.PF B : Submodule ℝ (V →₀ ℝ) := LinearMap.ker B.sumMap`**（`BPS.lean:210 noncomputable def PF`）——这就是链二 G 的核心“product formula”字段。

## 2. 输入 B：同构与唯一性输出（`Iut/Wall/BPS.lean` + `Iut/LogLink/Thm311Rest.lean:473`）

| 对象 | 字段/陈述 | 源 |
|---|---|---|
| `ValBPS.Iso B B'` | `toLinearEquiv : B.C ≃ₗ[ℝ] B'.C`；`map_localPilot : ∀ v, toLinearEquiv (B.localPilot v) = B'.localPilot v` | `BPS.lean` `structure Iso` |
| `ValBPS.nonempty_iso_iff` | `Nonempty (Iso B B') ↔ B.PF = B'.PF` | `BPS.lean`（Lemma 4.1.7） |
| **`rlf_unique`** | `(B B' : ValBPS V bad) (h : B.PF = B'.PF) : Nonempty (Unique (B.Iso B'))` | **`Iut/LogLink/Thm311Rest.lean:473`** |
| `rlf_cocycle` | `e₁₂.trans e₂₃ = e₁₃`（唯一同构的 cocycle 性） | `Iut/LogLink/Thm311Rest.lean:479` |
| `RposOrbit B B'` | `{φ : B.C ≃ₗ B'.C | ∃ c > 0, ∀ v, φ(localPilot v) = c • localPilot' v}` | `Thm311Rest.lean` `def RposOrbit` |
| `RposOrbit` | `Set (B.C ≃ₗ B'.C)`：局部 pilot 送正倍数 | `Iut/LogLink/Thm311Rest.lean:487` |
| `mem_rposOrbit_iff` | `φ ∈ RposOrbit B B' ↔ ∃ c>0, ∀ x, φ x = c • e.toLinearEquiv x`（e 为唯一同构） | `Iut/LogLink/Thm311Rest.lean:491` |
| `rposOrbit_compat` | 两条路径差一个正标量 `r`（Theorem 1.5(v) 兼容性） | `Iut/LogLink/Thm311Rest.lean:506` |

**给 abc 的输出**：对任意两个 `PF` 相等的成员，成员选择无自由度（`Unique (Iso B B')`）；不同 `RposOrbit` 选择只差正标量。⇒ 链二的可能的像之并在 PF 相等的层上**塌缩成单点**。

## 3. 输入 C：全局 realified Frobenioid 的 Θ/q-pilot 与精确标度（`Iut/Frobenioid/Wall.lean`, `Iut/ThetaLink/Link.lean`）

| 对象 | 陈述/定义 | 源 |
|---|---|---|
| `qPilotObj D` | `(pt, div(q-pilot))`（IUT III Def 3.8(i)）；`degreeNorm_qPilotObj`：normalized degree = `|log q| = (qVal D.bpsDegrees).pilot` | `Iut/Frobenioid/Wall.lean`（docstring + defs） |
| `thetaPilotObj D` | `(pt, (1/ℓ*)·Σ_{j=1}^{ℓ*} div(q^{j²}))`；`degreeNorm_thetaPilotObj`：degree = `s·|log q|`，`s = D.wallS`（`(1²+⋯+ℓ*²)/ℓ*`）；等于 `degTheta` | 同上 |
| `GlobalRealified.scale c hc` | `C^⊩` 的 `ℝ_{>0}` 标度；`degree_scale` 乘 degree 以 `c` | `Iut/Frobenioid/Wall.lean`（`namespace GlobalRealified`） |
| `scale_thetaPilotObj` | `scale (1/s)` 把 Θ-pilot 对象**精确**送到 q-pilot 对象 | 同上（docstring） |
| **`scaling_iff`** | `Nonempty ((GlobalRealified.scale c hc).obj (thetaPilotObj D) ≅ qPilotObj D) ↔ c = (D.wallS)⁻¹` | **`Iut/ThetaLink/Link.lean:206`** |
| `isEmpty_iso_thetaPilot_qPilot` | `IsEmpty (thetaPilotObj D ≅ qPilotObj D)`（同一 global realified Frobenioid 内不同构） | `Iut/WallEquiv/Basic.lean:190` |

## 4. 给 abc 的字段级 spec（建议 Lean 结构）

```
structure G1PilotData where
  V : Type
  bad : Finset V
  Bq : ValBPS V bad                 -- q-pilot 的 value-group BPS
  Btheta : ValBPS V bad             -- Θ-pilot 的 value-group BPS
  -- 全局 realified 侧的精确标度：只允许 s = wallS 的倒数
  wallS : ℝ
  hwallS : 0 < wallS
  scaling : Nonempty ((GlobalRealified.scale wallS⁻¹ hwallS_inv).obj (thetaPilotObj D)
      ≅ qPilotObj D)
  -- 链二的 G：任何候选全纯结构 E 的 BPS 必须与 Bq 有相同 PF
  candidate : Type                         -- 候选结构集合
  bpsOf : candidate → ValBPS V bad
  samePF : ∀ e, (bpsOf e).PF = Bq.PF
```

- **输入端字段**：`V`, `bad`, `Bq`, `Btheta`, `wallS`, `scaling`（后者由 `scaling_iff` 唯一化：c 只能是 `wallS⁻¹`）；候选结构 `bpsOf e` 与约束 `samePF`。
- **输出端**（作为 class-B/定理输出）：
  1. `∀ e, Nonempty (Unique ((bpsOf e).Iso Bq))`（`rlf_unique`：成员唯一同构 ⇒ 结构选择无自由度）；
  2. `Nonempty ((GlobalRealified.scale c hc).obj thetaPilotObj ≅ qPilotObj) ↔ c = wallS⁻¹`（`scaling_iff`：无连续自由度）；
  3. `IsEmpty (thetaPilotObj ≅ qPilotObj)`（`isEmpty_iso_thetaPilot_qPilot`：Θ 与 q 在同一容器内不同构，只能 `1/s` 标度等同）。
- **对链二的位置**：G 不是“额外不等式”，而是把 G1 的两个硬约束（PF 相等、标度固定 `wallS⁻¹`）作为输入；若候选 𝔥 的 BPS 不满足 `samePF` 或标度约束，则被 G 排除；若满足，`rlf_unique` 保证并集塌缩。需要补的是 q-pilot(1,0) 在候选族内的成员资格（§14 的隐藏条件）。

## 5. 备注

- `Iut/Wall/BPS.lean`、`Iut/LogLink/Thm311Rest.lean`、`Iut/Frobenioid/Wall.lean`、`Iut/ThetaLink/Link.lean` olean 尚未全部产出（根闭包待编）；字段/陈述均按源文件行读取，未编。
- `wallS` 定义在 `Iut/Frobenioid/Wall.lean`（`D.wallS`）与 `Iut/Wall` 的字母顺序相关；具体定义行见 `Iut/Frobenioid/Wall.lean` 的 `wallS` 字段（`ThetaPmEllNFHT`/`Distinguished` 结构内）。