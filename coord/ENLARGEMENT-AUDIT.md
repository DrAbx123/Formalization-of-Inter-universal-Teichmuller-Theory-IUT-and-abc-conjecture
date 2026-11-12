# ENLARGEMENT-AUDIT — hull enlargement E 与 faithful 桥审计（A1111）

日期：2026-11-13。**Status: READ-ONLY AUDIT；不编译。**
对象：`tmp/sheaf/xif/paper/Mzk1EnlargementActual.lean`（SHA16 `FFBF3CC27C8EDA99`，ole=False）、`Mzk1FaithfulEnlargementActual.lean`（SHA16 `FD001D449D93D4EE`，ole=False）。

## 0. 结论先行

1. `Mzk1EnlargementActual` 的 `E` 是**任意 Real 字段**，没有几何构造/约束；`target_of_enlargement` 的假设 `(sF−1)A−V≤E` 在定义展开后**就是 `0≤M`**；因此该定理是**目标的改写（CIRCULAR）**，不是独立证明；
2. `target_of_growth` 的假设 `(sF−1−c)A≤V` 在 `E=cA` 下同样等价于 `0≤M`；c 自由 ⇒ 也是改写，不是构造；
3. `Mzk1FaithfulEnlargementActual` 把 `E` 定义为 lana `gap`（`faithfulEnlargement_eq_gap`），是**定义/簿记桥**，不是几何 enlargement 的构造；`faithfulGapHullAt` 是 `Σ w_c·ind2Term`，与 lana `gapHullAt` 逐项 rfl；
4. faithful 桥本身**不循环**（没有用目标证 `E=gap`；它用 lana `gap_eq`），但若把 `E=gap` 喂给 `target_of_enlargement`，假设就是 variant ⇒ 循环/空洞；
5. 两文件都未编译；`tmp.external.ported.lana_core.Iut.WallEquiv.Gap.olean` 不存在 ⇒ Faithful 文件 BLOCKED/PENDING。

## 1. Mzk1EnlargementActual 审计

### 1.1 定义

```lean
structure EnlargementData where
  A : Real; V : Real; E : Real; sF : Real
def rhsOf D := D.V + D.E - D.sF * D.A
def MOf D := D.V + D.E - (D.sF - 1) * D.A
```
`E` 没有定义来源、没有 hull/Ind1/Ind2/Ind3 类型、没有正性/界；任意 Real。

### 1.2 `target_of_enlargement` 是否循环

```lean
theorem target_of_enlargement (D)
  (h : (D.sF - 1) * D.A - D.V ≤ D.E) : 0 ≤ MOf D := by
  unfold MOf; linarith
```
展开：`MOf = V + E - (sF−1)A ≥0 ⇔ (sF−1)A − V ≤ E`。**h 与结论逐字等价**；
`linarith` 只是把 h 重排。故该定理是**目标改写**：
* 不是独立非负性证明；
* 不能把 `h` 当作“E 覆盖 deficit”的几何输入；它假设了要证的 variant；
* 由于 E 任意，总可选 E 使 h 成立（取 E 足够大），所以对象/定理可空洞满足。

**判定：CIRCULAR/tautological as a proof of target**。作为 `criterion`/定义等价可以保留，但 header 的 “PROVED (pure algebra)” 不等于目标进展。

### 1.3 `target_of_growth`

```lean
(hE : D.E = c * D.A)
(h : (D.sF - 1 - c) * D.A ≤ D.V) : 0 ≤ MOf D
```
在 hE 下，`MOf = V − ((sF−1)−c)A`；`h` 即 `V ≥ ((sF−1)−c)A`，与 `MOf≥0` 等价；
c 任意 ⇒ 同样目标改写；若 c 来自几何 enlargement 的增长律，需独立证明 hE 与 c 的构造；当前没有。

**判定：CIRCULAR/tautological**；若 c 被定义为适配目标，则更空洞。

### 1.4 可保留的纯代数部分

* `M_eq_A_add_rhs`：`M=A+rhs`，ring，正确；
* `E_eq_gapOf`：`rhsOf=rhs ↔ E=gapOf rhs sF A V`，代数正确；这只是 gap 簿记，不是 enlargement 构造。

## 2. Mzk1FaithfulEnlargementActual 审计

### 2.1 定义与桥

```lean
faithfulGapHullAt (i) (finite p) :=
  ∑ c, tupleWeight (.finite p) c * ind2Term D i p c
faithfulGapHullAt (i) .infinite := 0
faithfulEnlargement := (∑ i, ∑ᶠ vQ, faithfulGapHullAt D i vQ) / nC
theorem faithfulGapHullAt_eq_gapHullAt : ... := by rcases ... <;> rfl
theorem faithfulEnlargement_eq_gap : faithfulEnlargement D = gap D := by rw [faithfulEnlargement, gap_eq]; ...
```

* `faithfulGapHullAt` 是 lana `gapHullAt` 的逐项复制；finite 情形定义相同，故 rfl；
* `faithfulEnlargement` 是 `(1/nC)Σ_iΣᶠ gapHullAt`；lana `gap_eq` 若正是这个定义，则桥是**定义性等式**；
* 这不是“构造了 Ind1/Ind2/Ind3 hull enlargement E”，而是**把 E 定义为 lana gap**；
* 所有 gap 的 GAP（ind2Term/C0、hull packet、vcI 等）原样继承；没有独立几何内容。

### 2.2 是否循环

* `faithfulEnlargement_eq_gap` 本身只用 `gap_eq`，没有假设 variant/目标；作为定义桥**不循环**；
* 但 `faithfulEnlargement = gap` + `EnlargementData` 的 `target_of_enlargement` 需要 `(sF−1)A−V≤E`，即 `V+gap≥(sF−1)A`（variant/SSIneq）；若把 bridge 当“E 已构造”再喂给 target 定理，就是**假设目标**；
* 结论：桥是**DEFINITIONAL/BOOKKEEPING**，不是非循环的目标证明；不能报告 variant 已证。

### 2.3 编译状态

* import `tmp.external.ported.lana_core.Iut.WallEquiv.Gap`；该 `.olean` **不存在**（路径检查 false）；
* 文件 ole=False；header 自己标 GAP（queued after lana_core build）；
* 当前不能声称 green/PROVED；gate **PENDING/BLOCKED**。

## 3. 判定汇总

| 对象 | 判定 | 说明 |
|---|---|---|
| `Mzk1EnlargementActual` | **CIRCULAR/INVALID as target proof** | E 任意 Real；`target_of_enlargement` 的 h 与 `MOf≥0` 等价；`target_of_growth` 同理；纯代数恒等式可保留 |
| `Mzk1FaithfulEnlargementActual` | **PARTIAL/DEFINITIONAL** | E=gap 是定义桥；faithful 桥本身不循环；但无几何构造、继承 gap GAP、ole 缺失 |
| E 是否可平凡满足 | **YES** | E 无约束，取足够大即可 |
| `target_of_enlargement`/`target_of_growth` | **目标改写** | 假设与结论等价，不能当独立 nonneg 证明 |
| faithful 桥循环性 | **本身不循环；喂入 target 则循环** | 用 gap_eq 定义，不是目标证明 |
| gate | **PENDING/BLOCKED** | lana Gap ole 不存在，未编译 |

**总判定：E 条件不是构造，是目标改写；faithful E=gap 只是簿记；不能把两文件当 variant/SSIneq 已证。**

## 4. 修正建议

1. `Mzk1EnlargementActual`：
   * 把 `target_of_enlargement` 重命名为 `criterion_of_enlargement`，并在 doc 明确 “hypothesis is equivalent to target; not a proof”；
   * 不要标 "PROVED" 作为目标进展；只保留 `M_eq_A_add_rhs`/`E_eq_gapOf` 作簿记；
   * 若要有内容，需要从 Ind1/Ind2/Ind3 构造 E 并证明 `(sF−1)A−V≤E`；这不能靠自由 Real。
2. `Mzk1FaithfulEnlargementActual`：
   * 明确 `faithfulEnlargement_eq_gap` 是 definitional bridge，不是构造；
   * 先等 lana_core Gap ole，再验证 `faithfulGapHullAt_eq_gapHullAt` 的 finite 定义是否真 rfl；
   * 不能把 E=gap 喂给 target criterion 当证明；仍需 variant/SSIneq 的独立输入；
3. 两文件都应标 GAP：E 的几何来源未构造；faithful 只到 gap 簿记；
4. 不编译；gate 由 watchdog/mainline 汇总；当前 `ole=False`，只能 PENDING/BLOCKED。