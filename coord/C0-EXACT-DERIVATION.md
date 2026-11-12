# C0-EXACT-DERIVATION — `ind2Term` 与 `archDefect` 的源码级推导

日期：2026-11-12。**状态：SOURCE-LEVEL CONDITIONAL；两条公式均可从现有定义推出，但都缺若干“体积/取整”引理，不能当作已证定理。**

口径：只读 `Iut/` lana 源码；不依赖 olean，不把源级推导当 Lean 证明。所有路径相对根 `Iut/` 树。

## 1. 定义与源码清单

### 1.1 `ind2Term` 的定义

- `Iut/WallEquiv/Gap.lean:747`：
  ```lean
  def ind2Term (i : Fin (nC D)) (p : Nat.Primes)
      (c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod (.finite p)) : ℝ :=
    LocalTheory.componentVol D.Kt (.finite p) (LocalTheory.tuple D.placeSect _ c)
      (LocalTheory.leastHull (.finite p) (LocalTheory.tuple D.placeSect _ c)
        (D.thetaComponent (nC D) i (.finite p) c)) -
    LocalTheory.componentVol D.Kt (.finite p) (LocalTheory.tuple D.placeSect _ c)
      (D.scaleElt (nC D) i p c • leastHull (.finite p) (LocalTheory.tuple D.placeSect _ c)
        (LocalTheory.shell D.Kt p (LocalTheory.tuple D.placeSect _ c)))
  ```
- 即 `ind2Term = V(LH(Θ_{i,p,c})) − V(q_{v_j}^{j²} • LH(⊗𝓘))`。
- 关键定义：
  - `scaleEltAt`（`Iut/Concrete/ThetaRegion.lean:126`）把 `qroot^{j²}` 放在第 `l` 个张量因子；`scaleElt`（`:136`）是 distinguished label `j=i+1` 的那个；
  - `thetaFiniteOn`（`:170`）是 `⋃_{φ ∈ indAut} φ '' (⋃_{l∈S} q_{v_l}^{j²} • shell)`，`indAut` 在有限位就是 `tensorAut`（`Iut/Concrete/LocalConstruct/IndAut.lean:294-303`）；
  - `tensorAut`（`IndAut.lean:219`）= 张量积 `⊗_j g_j`，每个 `g_j` 是 `Z_p`-lattice 自同构；
  - `leastHull`（`Gap.lean:87`）是包含 `U` 的最小 `b·O`（`O = integral`）；
  - `componentVol`（`Iut/Concrete/LocalConstruct/Volume.lean:196`）`= log(μ(S)/μ(I))/finrank`；`μ(I)=0` 归一并由 `componentVol_integral` 给出。

### 1.2 `archDefect` 的定义

- `Iut/WallEquiv/Gap.lean:459`：
  ```lean
  noncomputable def archDefect (c : ι → Place K) : ℝ :=
    componentVol K .infinite c (leastHull .infinite c (logShell K .infinite c)) -
      componentVol K .infinite c (logShell K .infinite c)
  ```
- `archDefect_nonneg`（`:463`）、`archDefect_pos`（`:468`）只证非负/正；`Gap.lean` 头注释 L66–68 明说**精确值未形式化**（“not formalized here”）。VcI.md L148–154 给出精确值 `log(N!)/(2N)`，`N=2^{m−1}`。
- `archIntegral`（`Archimedean.lean:328`）= `{x | ∀ m, ‖archChar m x‖ ≤ 1}`；`archLogShell`（`ArchLogShell.lean:278`）= `{x | archTensorInner x x ≤ (π^{|I|})²}`；`archTensorBasis` 是乘积正交基（`:227`），`archTensorInner_basis`（`:231`）给正交性。

## 2. `ind2Term` 推导链

### 2.1 记号和目标

固定 `i,p,c`。记：

- `T := Tensor D.Kt (.finite p) (tuple D.placeSect c)`，`d := finrank ℚ_p T`；
- `S := shell D.Kt p (tuple ...)`，`L := leastHull p (tuple ...) S`；
- `a := scaleElt D i p c`（单位，`isUnit_scaleElt`）；
- `Θ := thetaComponent D i p c`，`HΘ := leastHull p (tuple ...) Θ`；
- `x := j² · ordp(qroot_{v_j})`，`j = i+1`。

目标（在下列假设 A1–A4 下）：

```text
ind2Term = frac(x) · log p,   frac(x) = x − floor x ∈ [0,1).
```

### 2.2 证明链（按依赖次序）

**Step 1（展开）**：由 `ind2Term` 定义，

`ind2Term = V(HΘ) − V(a • L)`。

**Step 2（`a` 的 p 进 order）**：`a = incl_l(qroot_{v_l}^{j²})`，`ordp` 在张量因子上可加；由 `ordp_qroot`（`Iut/Concrete/ThetaLocalConstruct/Data.lean:420`）与 `ordp_pow`：

`ordp(a) = j² · ordp(qroot_{v_j}) = j² · qOrder(w)/(2ℓ·ramIdx(w))`，

在 `F_mod` 的截面位（`ordp_qroot_sect`, `SectionAverage.lean:189`）即 `j²·qOrder/(2ℓ)`（`ramIdx=1`）。这就是公式里的 `j²·v_p(q)/(2ℓ)`；若保留一般 `ramIdx`，写 `v_p(q)=qOrder/ramIdx`。

**Step 3（单位缩放的体积）**：对任意可测 `U`，`haar_units_smul`（`ScaleVolume.lean:46`）给

`μ(a•U) = χ(a)·μ(U)`，故 `V(a•U) = V(U) + log χ(a)/d`。

由 `componentVol_prod_incl_smul_integral`（`:118`）/`componentVol_units_smul_integral`（`:52`），对 `a = ∏_j incl_j(y_j)`：

`log χ(a)/d = −(∑_j ordp(y_j))·log p`；

因此 `V(a • L) = V(L) − x·log p`。

**Step 4（`HΘ` 的取整）**：`Θ = ⋃_{φ∈tensorAut} φ(a•S)`。由 `tensorAut` 是因子 `Z_p`-lattice 自同构的张量积（`IndAut.lean:219`, `tensorAut_subset_latticeAut`），它保持 `integral` 的 `Z_p`-lattice 结构；其像的并集在 `a` 的 p 进指数上“向下取整”到整格：

`HΘ = p^{−floor(x)} • L`（A2：`leastHull_thetaComponent_eq_pow_floor`）。

于是 `V(HΘ) = V(L) − floor(x)·log p`。

**Step 5（合并）**：

`ind2Term = [V(L) − floor(x)log p] − [V(L) − x log p] = (x − floor x)log p = frac(x)log p`。

**Step 6（支撑/退化）**：`x=0`（非 bad residue characteristic，`scaleElt=1`）时 `frac=0`，与 `ind2Term_eq_zero`（`Gap.lean:771`）一致；`frac≥0` 与 `ind2Term_nonneg`（`:756`）一致。

### 2.3 `ind2Term` 引理清单与状态

| 引理 | 源码/状态 | 作用 |
|---|---|---|
| `ind2Term` 定义 | `Gap.lean:747`；**有** | 展开 |
| `scaleEltAt/scaleElt` 定义 | `ThetaRegion.lean:126/136`；**有** | `a` 的具体形式 |
| `ordp_qroot` / `ordp_qroot_sect` | `Data.lean:420` / `SectionAverage.lean:189`；**有（源级）** | Step 2 |
| `ordp_pow`/`ordp_mul` | `LocalTheory`；有 | Step 2 |
| `haar_units_smul` | `ScaleVolume.lean:46`；**有** | Step 3 一般集 |
| `componentVol_prod_incl_smul_integral` | `ScaleVolume.lean:118`；**有** | Step 3 显式值 |
| `componentVol_units_smul`（任意可测集版） | **缺**（只有 integral 版 `:52` 和 `haar_units_smul`） | Step 3 直接套用；可由 `haar_units_smul` + `componentVol` 定义一行推出 |
| `tensorAut` 定义/`indAut_shell` | `IndAut.lean:219`/`:?`；**有** | Step 4 的因子自同构保持 shell |
| `leastHull_thetaComponent_eq_pow_floor` | **缺** | Step 4 的核心：`HΘ=p^{−floor x}L`；不是现有 `ind2Term_nonneg` 能给出的 |
| `frac(x)` 与 `ind2Term` 等式 | **缺** | 最终公式 |

**结论（`ind2Term`）**：在上述 A1–A4 下，`ind2Term = frac(j²·v_p(q)/(2ℓ))·log p` **源码级可推出**；但 `leastHull_thetaComponent_eq_pow_floor` 是核心缺失引理，所以当前 **不是已证定理**。lana `Gap.lean` 也把 Ind2 的值标为 Open。

## 3. `archDefect` 推导链

### 3.1 张量度量与正交性

- `archTensorInner`（`ArchLogShell.lean:204`）是因子 Hermitian 度量的张量积：`⟨⊗a_j,⊗b_j⟩=∏⟨a_j,b_j⟩`（`:209`）；
- `archTensorBasis`（`:227`）是乘积正交基，`archTensorInner_basis`（`:231`）给 `=δ_{pq}`；`archTensorCoord`（`:250`）把它等距送到 Euclidean 空间，`norm_archTensorCoord_sq`（`:256`）给 `‖coord x‖²=⟨x,x⟩`；
- 因此 `archLogShell`（`:278`）是 `ℝ^d` 中的 Euclidean 球，半径 `R=π^{|I|}`（`:285` `archLogShell_eq_preimage`）。

### 3.2 维数与体积

设胶囊有 `m` 个标签，每个 `ℂ` 实维 2，故 `T` 实维 `d=2^m`；设 `N=2^{m−1}`（极大谱的个数 / 独立复坐标数）。

- `archIntegral` 是 `N` 个复单位圆盘的乘积（`archIntegral` 定义用 `archChar` 的 `N` 个分量；`ArchLogShell.lean` 的 `card_archTensorIdx` 给 `N≤2^m`，全复时 `=2^{m−1}`）；
- `archLogShell` 的球半径 `R=π^{m}`，故 `vol(ball) = ω_d·R^d`，`ω_d=π^{d/2}/Γ(d/2+1)`；
- `vol(archIntegral) = π^N`（每个复圆盘面积 π）。

**关键缺口**：`haar` 是 `Measure.addHaar`（`Volume.lean:78`），没有现成引理把它与 `archTensorCoord` 下的 Lebesgue 测度比较；但 `componentVol` 是比值，Haar 的常数因子会抵消，所以体积比可用 Euclidean 公式。**这个“Haar 与坐标 Lebesgue 成比例”仍未形式化**（缺失引理 `haar_archTensorCoord_eq_smul_lebesgue`）。

### 3.3 取 hull

`leastHull(archLogShell)` 是包含球的最小 `a·B_I`。球在坐标下是半径 `R=π^m` 的 Euclidean 球；其最小外切多圆盘为 `R·B_I`（由 `exists_forall_archChar_eq`，`Archimedean.lean:284`，可选取 `a` 使每个分量半径 =R）；因此

`LH(archLogShell) = π^m·archIntegral`（A3′：`leastHull_archLogShell_eq_smul_archIntegral`，**缺**）。

### 3.4 `componentVol` 与公式

`componentVol(S)=log(vol(S)/vol(I))/d`（`Volume.lean:196`；`componentVol_integral=0`）。按 VcI.md L148–154 的精确值：

- `μ^log(𝓘_∞) = m logπ + ½logN − log(N!)/(2N)`；
- `μ^log(hull 𝓘_∞) = m logπ + ½logN`；
- 相减：`archDefect = log(N!)/(2N)`，`N=2^{m−1}`。

换成本任务记号（用 `N` 表示因子数 `m`）：

```text
archDefect = log((2^{N−1})!)/(2^N).
```

（两种记号：VcI 的 `N=2^{m−1}`，任务/`Gap.lean:66` 的 `N=m`；展开后相同。）

### 3.5 `archDefect` 引理清单与状态

| 引理 | 源码/状态 | 作用 |
|---|---|---|
| `archTensorBasis`/`archTensorInner_basis` | `ArchLogShell.lean:227/231`；**有** | 正交性 |
| `archLogShell_eq_preimage` | `:285`；**有** | 球半径 `π^m` |
| `archIntegral` 定义 | `Archimedean.lean:328`；**有** | 多圆盘 |
| `card_archTensorIdx` | `ArchLogShell.lean:335`；**有**（≤2^m） | 维数上界 |
| `finrank_tensor_infinite_eq` | **缺**（仅 `exists_ne_maximalSpectrum` 用 `finrank_eq_card_basis`，未单独成式） | `d=2^m` |
| `haar_archTensorCoord_eq_smul_lebesgue` | **缺** | Haar vs Euclidean 体积 |
| `volume_ball/volume_polydisc` | **缺** | `ω_d` 与 `π^N` |
| `leastHull_archLogShell_eq_smul_archIntegral` | **缺** | 最小外切多圆盘 `π^m B_I` |
| `archDefect_eq` | **缺** | 最终 `log((2^{N−1})!)/2^N` |

**结论（`archDefect`）**：公式在张量度量正交性 + Euclidean 球/多圆盘体积 + 最小外切 hull 三条引理下 **源码级可推出**；但当前 Lean 只有 `archDefect_nonneg/pos`，精确值 **未形式化**（`Gap.lean:66-68` 明说）。

## 4. 总判定与下一步

| 公式 | 现有定义下可推出？ | 缺哪条核心引理 | 状态 |
|---|---|---|---|
| `ind2Term = frac(j²v_p(q)/(2ℓ))logp` | **条件可推出** | `leastHull_thetaComponent_eq_pow_floor`；一般集 `componentVol_units_smul` | SOURCE-LEVEL CONDITIONAL；lana Open |
| `archDefect = log((2^{N−1})!)/2^N` | **条件可推出** | `leastHull_archLogShell_eq_smul_archIntegral`；`haar`↔Lebesgue；球/多圆盘体积；`archDefect_eq` | SOURCE-LEVEL CONDITIONAL；Lean 只有 ≥0/>0 |

**两条公式都不能说“已在现有定义下证出”**：它们需要上述缺失引理。最优先补的引理：

1. `leastHull_thetaComponent_eq_pow_floor`（ind2 的核心；同时会给出 `ind2Term_nonneg` 的新证明）；
2. `leastHull_archLogShell_eq_smul_archIntegral`（arch 的核心；把 `archLogShell_subset` 的包含升级为等式）；
3. `componentVol_units_smul`（任意可测集；从 `haar_units_smul` 一行）；
4. `haar_archTensorCoord_eq_smul_lebesgue` + 球/多圆盘体积（arch 的测度输入）；
5. `finrank_tensor_infinite_eq`（`d=2^m`，供体积分母）。

**证据状态**：全部为源级读取，未编译、无 olean；`Gap.lean`/`ArchLogShell.lean` 的 olean 不在本地闭包。不得把本文件当 Lean 证明。
