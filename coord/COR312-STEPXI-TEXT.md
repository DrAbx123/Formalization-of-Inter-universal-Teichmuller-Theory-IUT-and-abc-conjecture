# COR312-STEPXI-TEXT — Step (xi) 的 log-volume 计算逐式提取 (A1119)

| field | value |
|---|---|
| 源 | `coord/IUT-TEXT/III.txt`，行号如引；对照 `coord/IUT-TEXT-COR312.md`（III pp.173-185） |
| 结论 | Step (xi) **不显示** `|log q|`/`|log Θ|` 的数值公式；二者定义为**区域 log-volume**（j∈F⋆ 的 procession 归一化）。xi 段**没有** level/n·log p/(1/2)log p 显式项；Ind3 以 **`≤` / inequality from above** 进入；唯一的 q 线性增长来自 hull/possible-image 的 theta 缩放（`q^{j²}`），xi 本身不展开。 |

## 1. `|log q|` 与 `|log Θ|` 的定义（原文行号）

III:10845-10851（p.183）：
```
L10845:  R_{≤−|log(Θ)|}
L10846:  def
L10847:  = {λ ∈ R | λ ≤ −|log(Θ)|} ⊆ R;   −|log(q)| ∈ R
L10848:  — where we recall that, by definition, −|log(Θ)| is the [negative — cf. the discussion
L10849:    of “possible images” at the beginning of the present proof] log-volume of 1,◦U, while
L10850:    −|log(q)| is the log-volume of the region that arises from the representation of
L10851:    the q-pilot object at (1,0) on 1,◦UQ.
```
定义要点：
```
−|log Θ| := (negative) log-volume of 1,◦U   （1,◦U = holomorphic hull of possible images，
              subject to Ind1/Ind2/Ind3）
−|log q| := log-volume of q-pilot region on 1,◦UQ （NOT subject to Ind1/Ind2/Ind3）
```
归一化：III:10840 “the [suitably normalized, with respect to j ∈ |F_l|] log-volume”；
III:1183-1184 “for the procession-normalized mono-analytic log-volume [where the average
is taken over j ∈ F⋆...]”；标签集 III:5976 “for j ∈ {1,...,ℓ⋆}, ℓ⋆ = (ℓ−1)/2”（与我们 nC 一致）。
**xi 段不出现 1/(2ℓ) 的数值公式**；`|log q| = (1/(2ℓ))log q` 在 IUT IV Thm 1.10 p.23（另见 `IUT-TEXT-COR312.md` §7）。

## 2. 是否出现 level/upperSemiLevel 项（`n·log p`、`(1/2)log p` 等）

III:10790-10880（xi-b..xi-e）**逐行检索结果**：
```
✗ 没有 “level”“upperSemiLevel”“n·log p”“(1/2)log p” 形式的显式加项；
✓ 只有 processioin 归一化（j-average，III:10840、1183-1184）；
✓ q 的显式依赖通过 “q-pilot object at (1,0) on 1,◦UQ” 与其 log-volume 进入（III:10850-10851），
  具体数值计算留给 Step (v)/IV Thm 1.10（`−(ℓ+1)/24·log q` 等）；
✓ III:10856-10865 的 “log-Kummer correspondence … rectify the vertical shift/mismatch”
  说明 log-Kummer 用于**修正** unit portion 与 log-shells 的 shift，但 xi 段不写具体量。
```
⇒ **xi 段没有 level 项**；若有 `n·log p` 型项，它们出现在 Θ-link/level 结构的其它步骤（不是 xi-d 的 display）。

## 3. Ind3 如何进入（`≤` 还是 `=`）

```
III:10897-10899（p.184）：
  “The inclusion −|log(q)| ∈ R_{≤−|log(Θ)|}, hence also the inequality
   −|log(q)| ≤ −|log(Θ)| ∈ R”
⇒ **最终不等式是 inclusion 的推论：−|log q| ≤ −|logΘ|**（`≤`，不是等式）。

Ind3 的原始表述（Theorem 3.11）：
  “(Ind3) … ‘upper semi-compatible’ … certain natural inclusions ‘⊆’ at vQ∈V_non_Q
   and certain natural surjections ‘↠’ at vQ∈V_arc_Q”  （III:671 起（Ind3））
Step (x)（p.181）：“procession-normalized log-volumes … convert the indeterminacy (Ind3)
   into an inequality [from above]”（`IUT-TEXT-COR312.md` §4 引文）。
```
⇒ **Ind3 进入方式是单侧 `≤`（upper semi / inequality from above），不是 `=`**；
Cor 3.12 的 `−|log q| ≤ −|log Θ|` 正是这一侧。

## 4. 哪一步提供随 qOrder 线性增长的正项？

```
xi 段本身**不显示** qOrder 线性项；它只把两边都定义为区域 log-volume。
qOrder 的线性增长来自 **hull/possible-image 的 theta 缩放 q^{j²}**：
  - 1,◦U = holomorphic hull of the union of possible images；
  - possible images = LGP · (log-shell region)，LGP 按 theta values q^{j²} 缩放；
  - 因此 logVol(1,◦U) 对 log q 的依赖通过 q^{j²}-缩放与 j-average（系数 sF）进入；
  - 对 **大 qOrder**（如 I_n, qOrder=n），`log q ≈ n log p` 增长，
    hull 的 enlargement（union over j/Ind1/2/3）给出 ∝ n 的正项（即 lit 的 ind2-型项，
    见 A1118/A1027：`ind2Term` 含 `(j²−1)·ord·log p`）。
```
⇒ 线性正项的**来源** = possible images 的并集/hull enlargement（q^{j²} 缩放），
   不是 xi 段中某个显式 level 项。**xi-d 的关键操作正是**：
   取 determinant of localizations（rank>1）→ 与 q-pilot 线丛（rank 1）可比 →
   应用 j-归一化 log-volume（III:10837-10843）
   从而把 `1,◦U` 与 q-pilot region 放到同一标量尺度（III:10844-10851）。

## 5. 结论清单

| 问题 | 答案（带行号） |
|---|---|
| `|log q|`、`|log Θ|` 定义 | 区域 log-volume（III:10845-10851）；procession j-average（III:10840、1183-1184） |
| level 项（n·log p/(1/2)log p） | **xi 段没有**；只在 Step (v)/IV Thm 1.10 的显式不等式/其它步骤出现 |
| Ind3 进入方式 | **`≤` / upper semi / inequality from above**（III:671、10897-10899；Step (x) p.181） |
| qOrder 线性正项来源 | hull enlargement by q^{j²}-scaled possible images（lit/Ind1-3 union）；xi 只给 determinant 比较框架（III:10837-10843） |

## 6. 对 formalization 的直接含义

1. `StepXiDData`（A1114）的 `containment`/`logVol_mono` 正对应 III:10897-10899 的 inclusion-⇒-inequality；
2. xi 段**不需要**形式化 level 项；需要的是 (a) `1,◦U` 与 q-pilot region 的 log-volume 归一化（j-average），
   (b) determinant of localizations 的 rank>1 → rank-1 比较（III:10837-10843），
   (c) Ind3 的 upper-semi 单侧性（我们现有 Ind3 upper-bound 资产方向正确，但用于**上界**，
   而目标需要 `−|log q| ≤ −|logΘ|` 方向；对应 A1110 的方向分析：需把 upper-semi 与 inclusion 对齐）；
3. 若 gap 的线性项来自 hull enlargement（lit），则 A1118 的 q-stability 结论成立；
4. xi 段无 level 项这一事实，排除了「用 level 项吸收 gap」的路线；gap 的 q-线性只能来自 hull enlargement。