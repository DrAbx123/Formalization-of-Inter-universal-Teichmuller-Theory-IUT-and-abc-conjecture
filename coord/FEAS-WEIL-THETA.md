# FEAS-WEIL-THETA — Weil 表示/Segal–Bargmann/Hermite 视角 (A1099)

| field | value |
|---|---|
| Status | ANALYSIS (no Lean; no compile) |
| 判定 | 单 theta 的 sup 界 = **A**（标准 Fourier 估计）；乘积截面 "canonical 归一化 sup≤1" = **B/C**（需 det 归一化恒等式 = 我们的缺口）；有限位兼容 = **C**（当前无 Heisenberg/level 整模型） |

## 1. theta 作为 Heisenberg 线丛截面（标准结构）

```
Heisenberg 群 H(R)（中心 R）作用在 L²(R)；Weil 表示给出辛表示；
theta 函数是 H(Z)-不变向量（theta 截面）；
Segal–Bargmann：theta 对应 Fock 空间 Gaussian；
Mehler 核：theta 的 Hermite 展开 = Σ_n c_n h_n（Hermite 函数）；
q-展开 = Σ_n q^{n²/2} e^{2πi n z}（Fourier 级数）。
```

## 2. ① 范数公式 / Mehler / Bargmann

- **Fourier（q-展开）绝对收敛**（`q = e^{2πiτ}`, `|q|<1`）：
  ```
  |θ(z,τ)| = |Σ_n q^{n²/2} e^{2πinz}| ≤ Σ_n |q|^{n²/2}
          ≤ 1 + 2Σ_{n≥1} |q|^{n²/2} ≤ 1 + 2|q|^{1/2}/(1−|q|)      (标准初等估计)
  ```
- **Petersson/L² 范数**：`∫_{E(C)} |θ|² dA` 有显式公式（∝ Im τ 的幂）；
- **Segal–Bargmann/Mehler**：Gaussian 型逐点界（Hermite 展开核），与 Fourier 界同阶。

## 3. ② canonical 归一化使 sup ≤ 1？

**逐字回答**：任何非零连续截面乘实常数可令 sup=1——但**允许的常数**必须是数论对象
（整体截面/单位的归一化），不能是任意实数。问题是：
```
是否存在整体截面 s（Heisenberg/Weil 的 canonical 截面），
使其在 det bundle 的 canonical 度量下 arch sup 范数 ≤ 1？
```
- 允许实常数：**平凡** ⇒ **B（重述）**；
- 要求模变换/自守归一化：需 `sup_z |θ(z,τ)| ≤ C(τ)` 且 `C(τ)` 被 det 度量吸收，
  等价于 `arch_bound ≤ 0`（A1088 的 `arch_le` 输入）⇒ 重述；
- **乘积** `∏_j θ(u_j)^{j²}`：单项界相乘 `∏(1+2|q|^{1/2}/(1−|q|))^{j²}` 一般 **远大于 1**；
  要被 det 度量吸收，必须用 j-average 的 det 归一化 `−sF·A`（我们的缺口）。
⇒ ② 判定：**B（实归一化）/ C（无 det 归一化时不能 ≤1）**。

## 4. ③ 与有限位整性/线丛底座的兼容性

- 归一化常数若为**有理数/单位**（q^{1/24} 幂、eta 幂）：有限位 valuation 可控（算术）；
- 仅 arch 实数归一化：破坏有限位整性，不能作为整体截面；
- Heisenberg 线丛的**整模型**（over O_K）需要 level 结构/Heisenberg 群概型；
  我们 `SourceDefinition31Data` 没有该几何（A1098：无模解释）⇒ canonical 截面的整模型缺。
⇒ ③ 判定：**C（当前底座不兼容）**；需新增 Heisenberg/level 数据（GAP-MODPOINT）。

## 5. A/B/C 汇总

| 子命题 | 类型 | 理由 |
|---|---|---|
| 单 theta 的 Fourier sup 界 | **A（标准估计）** | 初等几何级数 |
| Petersson/L² 范数公式 | **A（LITERATURE）** | 标准；与 sup 不同 |
| 乘实常数使 sup=1 | **B（重述）** | 平凡归一化 |
| canonical 归一化 sup≤1 | **B/C** | 需 det 归一化恒等式 |
| 乘积 ∏θ(u_j)^{j²} sup≤1 | **C（当前不可得）** | 单项界乘积 >>1 |
| 有限位整性兼容 | **C（当前底座）** | 无 Heisenberg/level 整模型（A1098） |

## 6. 结论

1. Weil/Segal–Bargmann/Hermite 给出 theta 的**标准 arch 工具**（Fourier/Mehler），单 theta sup 界 = **A**；
2. "canonical 归一化 sup≤1"允许实常数时 = **B（平凡）**；要求模变换/整体截面归一化时，
   必须已有 det 度量吸收 `−sF·A` ⇒ 回到 Step (xi-d)/det 比较缺口；
3. 乘积 `∏θ(u_j)^{j²} ≤ 1` 不能由单项 Fourier 界推出；
4. 有限位整性需 Heisenberg/level 整模型；当前无模解释（A1098）⇒ C；
5. 结论：此视角提供 arch 工具（A），不改变缺口结构，不构成 hcmp 的独立 A 路线。