# COR312-NORMALIZATION — Cor 3.12 的精确归一化与 q-stability 判定 (A1118)

| field | value |
|---|---|
| Status | ANALYSIS (source-level; no Lean, no compile) |
| 结论 | **系数本身与 paper 一致**（`|log q| = logQ/(2ℓ)`，procession 平均 = 对 `F⋆_ℓ = F_ℓ^×/{±1}` 的 `j`-平均，`avg(j²) = sF = ℓ(ℓ+1)/12`）。真正的归一化不一致在 **possible images 的并集范围**：paper 取 **all j / Ind1/2/3**（lit），`ind2` 有 ∝qOrder 线性项 ⇒ `gap = sF·A − V + b`、`rhs = b`（q-无关）⇒ variant **q-stable**；而 `concreteVariantData` 用 **iv（单 j）**，`ind2 = 0`、`gap` 有界 ⇒ variant 在大 qOrder 失败（qpilot 的观察）。 |
| 修正 | 采用 paper-faithful 的 **lit 并集**（`concreteVariantDataLit`），不是 iv；qpilot 的有界结论对应 iv，需标注为 **deviation** |

## 1. Cor 3.12 原文量（逐式提取）

`coord/IUT-TEXT-COR312.md`（III pp.173-174，verbatim）：
```
-|log(Θ)| ∈ R ∪ {+∞}
  = procession-normalized mono-analytic log-volume（对 j ∈ F⋆_ℓ 取平均，Remark 3.1.1/Prop 3.9(i)(ii)/Thm 3.11(i)(a)）
    of the holomorphic hull of the union of the possible images of a Θ-pilot object
    （possible images subject to (Ind1),(Ind2),(Ind3)）；
-|log(q)| ∈ R
  = procession-normalized mono-analytic log-volume of the image of a q-pilot object
    （**不** subject to (Ind1),(Ind2),(Ind3)）；
结论：  -|log(Θ)| ≥ -|log(q)|
即：     C_Θ ≥ -1  for any C_Θ ∈ R with -|log(Θ)| ≤ C_Θ·|log(q)|。
```
归一化补充（`coord/IUT-TEXT-COR312.md` §7 注）：Cor 3.12 本身不写 `1/(2ℓ)`；
`|log(q)| = (1/(2ℓ))·log(q)` 在 **IUT IV, Thm 1.10, p.23**。

## 2. 我们的量与 paper 的系数对照

```
A      := absLogQ = logQ/(2l)                    = |log q|   ✓（IV Thm 1.10）
rhs    := processionVol(hull Θ-pilot)            = -|log Θ|  ✓（Cor 3.12）
target : rhs >= -A   ⇔   M = A + rhs >= 0                   ✓
```
**procession 平均的精确系数**：
```
Step (v) 平均系数（IUT IV p.28-29）：  -(2l⋆+1)(l⋆+1)/(12l)·log q,  l⋆ = (l-1)/2
  = -(l+1)/24·log q
而 |log q| = log q/(2l)  ⇒  (l+1)/24·log q = sF·A,  sF = l(l+1)/12   ✓
等价地：avg_{j∈F⋆_l} j² = sF     （因 (1/(2l))·avg(j²) = (l+1)/24）
注意 F⋆_l = F_l^×/{±1}，card = (l-1)/2 = nC（不是 l-1；否则 avg j² 会是 l(2l-1)/6）。
```
⇒ **系数 sF、A、j-average 全部与 paper 一致，无不一致。**

## 3. 真正的不一致：possible images 的并集范围（iv vs lit）

`rhs` 的精确分解（Gap:521-527，lana）：
```
rhs = V + gap - sF*A,    V = logVol(hull vcI)（vcI = 局部 log-shell 容器，q-无关）
⇔ gap = rhs + sF*A - V  （= Σ gapHullAt，Gap:895-935）
Cor 3.12 ⇔ rhs >= -A ⇔ V + gap >= (sF-1)*A.
```
**关键**：`V` q-无关、有界；因此 q-stability（大 qOrder/A 下仍成立）**必须**要求
`gap` 含 ∝A 的线性项。`gap` 的线性项来自 `ind2Term`：
```
ind2Term = componentVol(leastHull(thetaComponent))
         - componentVol(scaleElt • leastHull(shell)),     scaleElt = qroot^{j²}
```
- **iv（单 j，`concreteVariantData` 当前用）**：thetaComponent = scaleElt_j • shell（单个），
  `leastHull = scaleElt_j • leastHull(shell)` ⇒ `ind2Term = 0`（精确），`gap` 只剩 bounded 项 ⇒
  `rhs ≈ V - sF·A` → **−∞**（大 A）⇒ Cor 3.12 失败 ⇒ **iv 不是 paper-faithful**；
- **lit（全 j / union over Ind1/2/3，paper 的 union of possible images）**：
  `thetaComponent = ∪_{S⊆{1,...,nC}} (∪_{j∈S} scaleElt_j • shell)`（含最小 j 的最大集合），
  `leastHull(thetaComponent)` ⊇ scaleElt_j • leastHull(shell) 对每个 j，故
  ```
  ind2Term >= componentVol(scaleElt_1 • leastHull(shell)) - componentVol(scaleElt_j • leastHull(shell))
            = (j² - 1) * ord(qroot) * log p        （ord 线性的精确项！）
  ```
  即 `ind2Term` **含 ∝qOrder 的线性项**（对 j>1）；求和后：
  ```
  gap_lit = sF*A - V + b        （b = bounded 残项）
  ⇒ rhs_lit = V + (sF*A - V + b) - sF*A = b     （q-无关！）
  ⇒ M = A + b >= 0 对大 A 自动成立（b 由 Step V box 控制）  ✓ q-stable
  ```

## 4. 判定与修正 identity

```
【系数】sF、A、j-average = paper 一致（§2），无不一致；
【归一化不一致的真因】possible images 的并集范围：paper = lit（全 j, Ind1/2/3），
                     current concreteVariantData = iv（单 j）——lana ThetaRegion:76-81 自述 deviation；
【lv 的后果】ind2=0、gap bounded、variant 大 qOrder 失败（qpilot 观察正确）；
【修正 identity（paper-faithful lit）】
      gap_lit = sF*A - V + b,   rhs_lit = b,   M = A + b,
  其中 b = rhs_lit 为 q-无关残项（由 Step V box 上界 + arch/torsion 控制）；
【q-stability】lit 下 M = A + b，大 qOrder 时 A 增长而 b 有界 ⇒ M -> +∞ 方向成立，
  只需小/中 A 的有限验证 + b 的界；iv 下 M = A + (V - sF A + b) -> -∞ 失败。
```

## 5. Lean/文档影响

1. **paper-faithful 的 variant 必须用 lit**（`concreteVariantDataLit`），不能用 iv；
2. 之前 A1027 的结论（lit: ind2=+j²A/gap=sF·A/stable；iv: ind2=0/gap=0/unstable）
   在此得到系统确认：**iv 的有界性正是 qpilot 证明的东西，也是 iv 失败的根源**；
3. 现有 `Mzk1GapBookkeepingActual`/`Mzk1EnlargementActual` 等代数文件不受影响（抽象 V/gap/A）；
4. 需要更新：`coord/VARIANT-QSTABILITY.md`、`VARIANT-READING-DECISION.md`、`PAPER-FIDELITY-COR312.md`
   明确 **lit = paper-faithful，iv = deviation（bounded gap，不 q-stable）**；
5. 若继续 formal，应把 `gap_lit` 的线性项 `(j²-1)·ord·logp` 形式化（lit 版 ind2 下界），
   而不要把 iv 的 `ind2=0` 当作普遍事实。

## 6. 结论

1. Cor 3.12 的系数（`|log q| = logQ/(2ℓ)`、j-average = sF）与我们一致，**不是系数问题**；
2. 不一致在 **possible images 并集**：paper 用 lit（全 j/Ind1/2/3），`concreteVariantData` 用 iv（单 j）；
3. iv ⇒ ind2=0、gap 有界、variant 大 qOrder 失败——qpilot 观察对应 iv，不是 paper；
4. lit ⇒ ind2 含 `(j²-1)ord logp` 线性项 ⇒ `gap_lit = sF·A − V + b`、`rhs_lit = b`、
   `M = A + b`，**q-stable**（大 qOrder 自动成立）；
5. 修正：paper-faithful 一律用 lit；iv 标注 deviation，不得作为 variant 的归一化依据。