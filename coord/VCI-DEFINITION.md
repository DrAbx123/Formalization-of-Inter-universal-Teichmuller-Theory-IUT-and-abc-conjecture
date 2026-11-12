# VCI-DEFINITION — 决定性核验：`vcI` 是否含 q-幂依赖

日期：2026-11-12；qpilot（A904）。**所有路径相对根 `Iut/` 树（`D:/lean/Iut/...`）**。

## 0. 结论（先给）

**`vcI` 不含 q-幂依赖。** `vcIComp D i (.finite p) c` 有限位分量是 **log-shell `LocalTheory.shell`**（对偶 different 的 log-shell），无穷位分量是 **archimedean log-shell**；`vcIAt` 只是这些分量的 product region。源码中 **没有** `D.qroot`/`scaleElt`/`q^{j²}` 因子。
于是 `V(q) := logVol D (hullOf D (vcI D))` **与 qOrder（= A = |log q| 的分子）无关**；而 SSIneq 的 LHS `(sF−1)·absLogQ` 随 qOrder 线性增长。因此 **在 LANA 模型中，SSIneq 作为“对所有 D”的陈述对足够大的 qOrder 为假**（模型级事实；LANA 源本身明确“SSIneq 及其否定均未证”，所以这不是矛盾，而是**陈述强度问题**）。
论文的 q-依赖 RHS 不是 `V`：它是 `rhsData.rhs = logVol(hull(theta-pilot region))`（`Cor312/RightHandSide.lean:107`），含 theta 值的 q^{j²} 缩放；由 LGP 律 `logVol_lgp_integral : logVol(LGP·O) = −sF·|log q|`（`Wall/IdentifiedCopies.lean:444`），theta-pilot 侧才能随 q 增长。SSIneq 与 variant 之间隔一个 `gap`（`WallEquiv/Gap.lean:505`，`gap ≥ 0`；`ss_iff_variant_of_gap_eq_zero`：仅当 gap=0 等价）；SSIneq 是更强、RHS q-无关的陈述。

## 1. `vcI`/`vcIComp` 完整定义

### 1.1 `vcIComp`（`Iut/Wall/Ind3.lean:58–62`）
```lean
noncomputable def vcIComp (i : Fin (nC D)) :
    ∀ (vQ : RationalPlace) (c : InitialThetaData.Lab (nC D) i → LocalTheory.Fiber D.Fmod vQ),
      Set (LocalTheory.Tensor D.Kt vQ (LocalTheory.tuple D.placeSect vQ c))
  | .finite p, c => LocalTheory.shell D.Kt p (LocalTheory.tuple D.placeSect _ c)
  | .infinite, c => LocalTheory.logShell D.Kt .infinite (LocalTheory.tuple D.placeSect _ c)
```
- 有限位：`LocalTheory.shell`，即由局部域 `K_w` 的 `log` 核/单位球定义的 **log-shell（逆 different 的 log-shell）**；
- 无穷位：`LocalTheory.logShell`，即 archimedean log-shell（polydisc）；
- **没有任何 `D.qroot`、`D.qPilot`、`D.tateParam`、`scaleElt`、`q^{j²}` 因子**；只有 `D.Kt`、`D.Fmod`、`D.placeSect`、`D.tuple` 与局部 `Fiber`/`Lab` 数据。

### 1.2 `vcIAt` / `vcI`（`Iut/Wall/Ind3.lean:80–81,123`）
```lean
noncomputable def vcIAt (i : Fin (VC D).proc.length) : (VC D).AdmissibleRegion i where
  region vQ := (LocalTheory.packet D.placeSect _ vQ).productRegion fun c => vcIComp D i vQ c
  ...
noncomputable def vcI : Region D := vcIAt D
```
即逐 capsule 的 **tensor packet 的 product region**；capsule `i` 的有 `i+1` 个张量因子，分别取 `vcIComp`（有限 log-shell / arch log-shell）。

### 1.3 q 依赖来自哪里？
- `D.Kt := ↥D.prime.torsionField`（`Cor312/ThetaData/Basic.lean:132`），而 `torsionField := IntermediateField.fixedField D.rep.ker`（`AdmissiblePrime.lean:165–166`）——只依赖 **mod-ℓ 表示 ρ**（`E[ℓ]`），不依赖 Tate 参数 `q`；
- `q` 的 qOrder 只以 **互素条件** `q_order_coprime` 进入 `AdmissiblePrimeData`（`AdmissiblePrime.lean:145–156`），并在 `absLogQ` 中线性出现（`Cor312/LeftHandSide.lean:81–88`），**不进入 `vcIComp`/`hullOf`/`logVol`**；
- 在坏素数 p、qOrder=m（ℓ∤m）时，`E[ℓ]` 扩张的局部分歧指数 `e = ℓ/gcd(ℓ,m) = ℓ`（Tate 曲线标准），与 m 无关（本模型把 `Kt` 及其位置/分歧都固定在 ρ 中）⇒ `hullPacket` 的 `(1−1/e)` 项与 m 无关。

## 2. `hullOf` 与 `logVol(hull(vcI))` 的显式公式

### 2.1 定义
- `hullOf`（`Iut/Wall/Rss.lean:328`）：
  ```lean
  noncomputable abbrev hullOf (U : Region D) : Region D :=
    (LocalTheory.hull D.placeSect (nC D)).hullFamily U
  ```
- `logVol`（`Iut/Wall/Rss.lean:324`）：`processionVol`（capsule 平均）。

### 2.2 显式定理（`Iut/WallEquiv/VcI.lean`）
- `logVol_hull_vcI_eq`（:741–742）：
  ```lean
  logVol D (hullOf D (vcI D)) = (∑ i : Fin (nC D), ∑ᶠ vQ, hullPacket D i vQ) / nC D
  ```
- `hullPacket`（:689）定义：`∑_c tupleWeight vQ c · componentVol (leastHull (vcIComp …))`。
- 有限位精确（`hullPacket_finite` :806–812）：`∑_c w_c · ∑_j logShellRadius(…)·log p`；
- tame 素数显式（`hullPacket_tame` :844–849）：`∑_c w_c · ∑_j (1 − 1/e_{c j})·log p`；
- 无穷位（`componentVol_archLogShell_le_leastHull_le` :653–657）：`μ^log(𝓘_∞) ≤ μ^log(hull 𝓘_∞) ≤ |I|·log(√2π)`（只有界，无精确闭式）；
- 容器 vs hull 差（`logVol_hull_vcI_sub_eq` :762–764）：`= (1/nC)∑_i ∑ᶠ_vQ defectPacket i vQ`（有限 shellDefect + arch defect）；
- SSIneq 的 packet 形式（`WallEquiv.ssIneq_iff_packets` :889–892）：
  ```lean
  Wall.SSIneq D ↔ (Wall.sFactor (Wall.nC D) - 1) * D.qPilot.absLogQ ≤
    (∑ i, ∑ᶠ vQ, WallEquiv.hullPacket D i vQ) / Wall.nC D
  ```

**结论：V = logVol(hull(vcI)) 有显式公式（hullPacket 平均）；有限位由 log-shell 半径/`(1−1/e)` 给出，arch 只有 `≤ |I|log(√2π)` 的界。公式中出现的 e、p、weight、nC 均为 `Kt`/数据依赖量，无 qOrder。**

## 3. V 与 q 的关系（决定性计算）

记 `A := D.qPilot.absLogQ = logQ/(2ℓ)`（`Cor312/LeftHandSide.lean:88`），`logQ = Σ_w weight·qOrder·log p`（:81–84）；`sF := sFactor (nC D) ≈ ℓ/3`（`Wall/Pilots.lean:55,67`；`nC=(ℓ−1)/2`）。

SSIneq：`(sF − 1)·A ≤ V`。
- `V = logVol(hull(vcI))` 只依赖 `Kt`（ρ 决定的域）、placeSect、labels、局部 shell/logShell 半径；**不含 `qOrder`**；
- `(sF − 1)·A ≈ (ℓ/3)·(logQ/(2ℓ)) = logQ/6 = (1/6)Σ weight·qOrder·log p`，随 `qOrder` 线性增长；
- 因此在固定 `Kt/ℓ` 下让 qOrder 任意大，SSIneq 必假。模型级结论：**若把 SSIneq 解释为 RHS=V 的不等式，它不可能普遍成立**；LANA 源也明确不证 SSIneq/否定（`MultiContainer.lean:86–87`）。

## 4. q 依赖在哪个正确对象上

关键在于 **SSIneq 的 RHS 不是 theta-pilot 的 log-volume**。
- theta-pilot 侧（paper 的 `−|log(Θ)|`）：`rhsData.rhs = logVol(processionVol, hull(thetaPilot))`（`Cor312/RightHandSide.lean:107`；`thetaHull` = `hull.hullFamily thetaPilot` :99–100）；theta-pilot 区域由 theta 值 `q^{j²}` 缩放，`logVol_lgp_integral`（`Wall/IdentifiedCopies.lean:444`）：`logVol(LGP·O) = −sF·A`；因此 **RHS 随 qOrder 增长**，与 LHS 同阶，paper 的 variant 才可能普遍成立。
- Gap：`gap D := rhsData.rhs − logVol(LGP·hull(vcI))`（`WallEquiv/Gap.lean:505`），`gap_nonneg`（:514），`logVol_lgp_integral` + `logVol_lgp`（:281）⇒ `logVol(LGP hull(vcI)) = V − sF·A`，故
  `gap = rhsData.rhs + sF·A − V`，即 `rhsData.rhs = V − sF·A + gap`。
- variant（`−A ≤ rhsData.rhs`）⇔ `(sF−1)A ≤ V + gap`；SSIneq ⇔ `(sF−1)A ≤ V`。因 `gap ≥ 0`，**variant 比 SSIneq 弱**；`ss_iff_variant_of_gap_eq_zero`（Gap:548–550）表明仅当 `gap=0` 时等价。
- 所以 q 依赖性在 `gap`/`rhsData.rhs` 中，而不在 `V` 中；SSIneq 的 q-无关 RHS 是 LANA 的**更强、不同**的墙（Step (xi) 的 SS 形式），不是 paper 的 Θ-hull 体积。

## 5. 决定性问题答案

**问题**：`vcI D` 与 `vcIComp D i (.finite p) c` 是否含 q 依赖（qroot/scaleElt/q-幂因子）？
**答案：不含。** 有限位是 `LocalTheory.shell`（log-shell/逆 different），无穷位是 `LocalTheory.logShell`；`vcI` 是它们的 product region。源码无 `D.qroot`/`scaleElt`/`q^{j²}`。

**推论**：`V = logVol(hull(vcI))` 与 `qOrder` 无关。因此：
1. 若某计算声称“V = logMu+arch 与 A 无关” ⇒ 与 LANA 定义一致（这是对的）；
2. 但 **SSIneq（RHS=V）不能作为 paper 的普遍不等式**：它随 LHS 增长必然失败（模型级），除非 V 含 q-依赖——而定义不含；
3. paper 的 q-依赖在 **`rhsData.rhs`（theta-pilot hull）**；由 LGP 律 `logVol(LGP·O)=−sF·A` 提供；SSIneq 与 variant 差 `gap≥0`，等号 `gap=0` 是 Gap.lean 的开放点（`ind2Term` 在坏素数是否为零未定）；
4. 所以**不是 `vcI` 定义缺 q 依赖**，而是 **SSIneq 是比 variant 更强的、RHS 冻结的陈述**；要恢复 paper 的 q-依赖，应引用 `rhsData.rhs`/variant（含 theta-pilot），而不是只引用 `logVol(hull(vcI))`。任何用 SSIneq 替换 variant 的论证都需要额外证明 `gap=0`（或 gap 可吸收），这是真数学内容。

## 6. 源索引（根树）

| 内容 | 源 |
|---|---|
| `vcIComp`（finite shell / arch logShell） | `Iut/Wall/Ind3.lean:58–62` |
| `vcIAt`, `vcI`, `isAdelic_vcI`, `vcI_le_hullOf` | `Iut/Wall/Ind3.lean:80–92,123–134` |
| `hullOf`, `logVol` | `Iut/Wall/Rss.lean:324,328` |
| `hullPacket`, `vcIPacket`, `defectPacket` | `Iut/WallEquiv/VcI.lean:683,689,703` |
| `logVol_hull_vcI_eq`, `logVol_hull_vcI_sub_eq`, `hullPacket_finite/tame`, arch bound | `Iut/WallEquiv/VcI.lean:741,762,806,844,653` |
| `ssIneq_iff_packets` | `Iut/WallEquiv/VcI.lean:889` |
| `absLogQ`, `logQ` | `Iut/Cor312/LeftHandSide.lean:81,88` |
| `Kt`, `torsionField` | `Iut/Cor312/ThetaData/Basic.lean:132`；`AdmissiblePrime.lean:165` |
| `rhsData.rhs`, `thetaHull` | `Iut/Cor312/RightHandSide.lean:99,107` |
| LGP 律 | `Iut/Wall/IdentifiedCopies.lean:281,444` |
| Gap, `gap_nonneg`, `ss_iff_variant_of_gap_eq_zero` | `Iut/WallEquiv/Gap.lean:505,514,548` |
| `SSIneq` 定义与“未证”注记 | `Iut/Wall/MultiContainer.lean:88,83–87` |
| `sFactor` | `Iut/Wall/Pilots.lean:55,67` |