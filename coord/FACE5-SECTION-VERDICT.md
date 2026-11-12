# FACE5-SECTION-VERDICT — 「截面存在性」是定义展开还是真构造

日期：2026-11-12；qpilot（A903）。**路径相对根 `Iut/` 树（`D:/lean/Iut/...`）**。

## 0. 结论（先给）

**face5 两层要分开**：
1. **`degNorm` 由截面（局部范数）定义，且 `degNorm_toBundle` 是字典恒等式**：`ArithLineBundle.deg = −Σ_w log‖a_w‖ − Σ_v mult(v)·log r_v`（`a_w`,`r_v` 是 chosen generic section 的局部范数），`degNorm = deg/[K:ℚ]`；而 `sectDeg/fullSectDeg` 由同一批 `ordp`/arch 半径定义，`degNorm_toBundle : toBundle.degNorm = sectDeg/fullSectDeg` 只是把权重展开——**不是新定理**。
2. **但“存在非零截面”本身在 idelic 模型中也不是数学内容**：`ArithLineBundle` 结构自带 chosen generic section；`principal x` 对任意 `x ≠ 0` 给出截面，`deg_mul_principal` 说明 degree 与截面选择无关。真正缺的是 **(i) 一个具体的整性截面 `x`（有限位 ord 有界），(ii) 其 arch 范数界**；这两项在 lana 中**没有**（只有一般 principal 的 product formula）。
⇒ **face5 若只写“存在非零截面”，是换说法/定义展开；若要求具体的整性截面 + arch 界，则是真数学构造（未做）。** 不是“已被判换说法”也不是“已留下可解构造”；而是**必须明确成后者**。

## 1. `degNorm` 的定义链（根树精确）

### 1.1 `ArithLineBundle` 与 `degNorm`（`Iut/Arakelov/LineBundle.lean`）
- 结构 `ArithLineBundle`（:69）：`fin : ∀ w, completionAt K w`（局部范数 ‖s‖_w = ‖a_w‖_w）、`inf : InfinitePlace K → ℝ`（‖s‖_v = r_v）——**承载一个 chosen generic section `s` 的局部范数**；
- `finDeg = −log‖L.fin w‖`（:84）；`infDeg = −mult(v)·log(L.inf v)`（:87–88）；
- `deg L = (∑ᶠ w, finDeg w) + ∑ v, infDeg v`（:101）；
- `degNorm L = L.deg / finrank ℚ K`（:105）。
### 1.2 `sectDeg` / `fullSectDeg`（同一批数据）
- `ArithContainer.ScalingDatum.sectDegAt p`（`Iut/Arakelov/Container.lean:140`）与 `sectDeg = ∑ p ∈ b.primes, sectDegAt p`（:145）；`sum_fiber_eq_sectDegAt`（:164–168）把它们写成 `Σ placeWeight·(ordp(b.elt)·log p)`；
- `FullScalingDatum.archSectDeg = −Σ_u weight·log(b.rad (placeSect.inf u))`（`Iut/Arakelov/ArchScaling.lean:205–207`）；`fullSectDeg = sectDeg + archSectDeg`（:210）；
- **定理**：`ScalingDatum.degNorm_toBundle (h) : b.toBundle.degNorm = b.sectDeg`（`Container.lean:196`）；`FullScalingDatum.degNorm_toBundle (h) : b.toBundle.degNorm = b.fullSectDeg`（`ArchScaling.lean:235`）；
- 两个证明都是 `degNorm` 展开 + 权重求和（`ArithLineBundle.degNorm_eq` 的 `finDeg_eq_ordp`/`sum_infDeg_eq_archSectDeg`）——**没有新的数学输入**。

### 1.3 log-volume 与 degNorm 的字典
- **`logVol_fullScale_integral_eq_degNorm`**（`ArchScaling.lean:496–498`）：
  ```lean
  logVol D (fullScale D a lab (integralRegion D)) =
    -(∑ i, (a i).toBundle.degNorm) / nC D
  ```
- **`logVol_fullScaleConst_eq_neg_degNorm`**（`ArchScaling.lean:503–504`）：`= -b.toBundle.degNorm`；
- 前者证明：`logVol_fullScale_integral`（:488） + `degNorm_toBundle`（:500），即**字典展开**。
- 同类：`logVol_lgp_integral_eq_degNorm`（`Iut/Arakelov/QPilot.lean:262`）把 theta 值 `q^{j²}` 的 log-volume 写成 `θBundle.degNorm`、`qDivisor.degNorm` 的平均；这也是 degNorm 字典 + `degNorm_thetaBundle`。

## 2. face5 的 P 与目标的关系

face5 方案（见 `coord/FACE5-ATTACK.md`）：`H = det(hull) ⊗ L_q^{−(sF−1)}`，要一个非零截面 `x`，用 product formula 得
`deg H ≥ −arch(x)`，再配 hull denominator budget 得 SSIneq。

**分析**：
- `deg H` 与截面选择无关（`deg_mul_principal`，`LineBundle.lean:255–257`）：换 `s ↦ x·s` 不变；`principal x` 的 degree 为 0（`deg_principal`，:250）。
- 在 idelic 描述中，“非零截面”**恒存在**（结构自带的 `s`；任意 `x∈K^×` 给 principal 截面）——所以 P 若只要求“∃ 非零截面”，**不产生任何不等式**，是定义/换说法。
- 唯一有内容的是把 `x` 取成**整性**截面：`−Σ_w log‖x‖_w ≥ 0`（即 `x` 在有限位属于 lattice `H` 的整结构），再加上 `arch(x)` 预算；此时 product formula 才给出 `deg H ≥ −arch(x)`。**这是真构造**（等价于证明 `H` 的 lattice 有非零元 + arch 界），lana 没有。
- 与目标的关系：face5 P（整性 + arch 界）⇒ SSIneq 的数值形式；但 P 本身**不是** SSIneq 的等价改写，而是它的一个充分条件（需要额外构造）。若 P 仅“∃ 非零截面”，则 P 与目标无逻辑联系（任何线丛都有）。

## 3. lana 中已有的“截面”定理（检查）

| 内容 | 源 | 是否覆盖 face5 |
|---|---|---|
| `principal x`（任意 `x∈K^×` 的截面）与 `deg_principal : deg = 0` | `Iut/Arakelov/LineBundle.lean:195,250` | 只给 product formula；**不是**特定 H 的整性截面 |
| `deg_mul_principal`（degree 与截面无关） | 同上 :255 | 说明“找截面”不改变 deg；不能产生不等式 |
| `logVol_lgp_integral_eq_degNorm`（theta 值的 degNorm 平均） | `Iut/Arakelov/QPilot.lean:262` | 只把 theta 值 log-volume 转成 degNorm；无截面构造 |
| `thetaBundle`/`qDivisor` 的 degNorm | `Iut/Arakelov/QPilot.lean`（`degNorm_thetaBundle` 等） | 有具体 bundle 的度，但**未构造其非零整性截面** |
| theta 常数/ℓ-分点判别式/κ-coric 赋值 | 根树 `Iut/EtaleTheta/*` 有 theta 函数/值；Arakelov 无“判别式截面”定理 | **无** H 的非零截面定理；`κ`-coric 不在 Arakelov 包 |

结论：**lana 没有 hull-difference bundle 的非零截面存在定理**；只有一般 principal/degree 字典与 theta 值的 degNorm 恒等式。

## 4. 判定

| 层 | 判定 |
|---|---|
| `degNorm` 由截面 degree 定义？ | **是**：`deg`/`degNorm` 由 chosen section 的局部范数定义；`sectDeg/fullSectDeg` 是同一批数据，`degNorm_toBundle` 是展开 |
| “找截面 + 控制 arch 范数”= 定义展开？ | **若是 generic 截面：是**（任何线丛都有；`principal` 任意 x；`deg_mul_principal` 说明无信息） |
| 是否需要真构造？ | **需要**：具体的整性截面（有限位 ord 约束）+ arch 范数界；这是 face5 的唯一真数学输入，lana 无 |
| face5 P 与目标关系 | P（整性+arch 界）⇒ SSIneq；但 P 不是等价改写；若 P 只“∃非零截面”，则与目标无关（换说法） |

**给 lead 的判词**：face5 **没有被判“换说法”**（它留下了一个真实构造任务），但绝不能把“截面存在性”当定理使用；必须把 P 精确写成“存在整性截面 `x`（`ord` 界）且 `arch(x) ≤ budget`”，否则是定义展开。当前 lana 没有该构造；face5 仍是一个真正的 **arithmetic construction gap**（不是接口/表述 gap）。