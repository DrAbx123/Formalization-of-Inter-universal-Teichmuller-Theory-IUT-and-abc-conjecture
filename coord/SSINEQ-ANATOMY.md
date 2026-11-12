# SSINEQ-ANATOMY — SSIneq / VC(I) / hull 体积的精确定义与计算

日期：2026-11-12；qpilot（A901）。**路径相对根 `Iut/` 树（`D:/lean/Iut/...`）**。

## ① `SSIneq` 完整定义

`Iut/Wall/MultiContainer.lean:83–89`：
```lean
/-- **The Scholze–Stix inequality** `(s − 1)·|log(q)| ≤ log-vol(hull(VC(I)))` ...
Neither it nor its negation is proved in this repository. -/
def SSIneq (D : InitialThetaData.{0}) : Prop :=
  (sFactor (nC D) - 1) * D.qPilot.absLogQ ≤ logVol D (hullOf D (vcI D))
```
- `sFactor n = (Σ_{j=1..n} j²)/n = (n+1)(2n+1)/6`（`Iut/Wall/Pilots.lean:55,67`），`nC D = (ℓ−1)/2`；
- `D.qPilot.absLogQ = D.qPilot.logQ/(2ℓ)`（`Iut/Cor312/LeftHandSide.lean:88`），`logQ = Σ_{w∈badFinset} weight w · qOrder w · log(residueChar w)`（:81–84）；
- `logVol`（`Iut/Wall/Rss.lean:324`）：`processionVol`（capsule 平均的 packet log-volume）；
- `hullOf`（`Iut/Wall/Rss.lean:328`）：`(LocalTheory.hull D.placeSect (nC D)).hullFamily U`（逐 capsule 的 holomorphic hull）。

## ② `vcI`/`vcIComp` 定义（每 capsule 的有限位/无穷位）

`Iut/Wall/Ind3.lean:58–62`：
```lean
noncomputable def vcIComp (i : Fin (nC D)) :
    ∀ (vQ : RationalPlace) (c : Lab (nC D) i → Fiber D.Fmod vQ),
      Set (Tensor D.Kt vQ (tuple D.placeSect vQ c))
  | .finite p, c => LocalTheory.shell D.Kt p (tuple D.placeSect _ c)
  | .infinite, c => LocalTheory.logShell D.Kt .infinite (tuple D.placeSect _ c)
```
- **有限位 `p`**：`LocalTheory.shell`——局部域 `K_w` 的 **log-shell**（逆 different 的 shell，`shell` 定义见 `Concrete/LocalConstruct/Integral` 等）；
- **无穷位**：`LocalTheory.logShell`——archimedean log-shell（polydisc `archHullRadius ^ card ι · I` 一类，见 `VcI.lean:653` 邻域）；
- `vcIAt`（:80–81）= 逐 vQ 的 `packet.productRegion (fun c => vcIComp …)`；`vcI = vcIAt`（:123）；
- 因 `Kt = ↥D.prime.torsionField = fixedField(ker ρ)`（`Cor312/ThetaData/Basic.lean:132`；`AdmissiblePrime.lean:165–166`），**`vcI` 不含 `D.qroot`/`scaleElt`/q^{j²} 因子**；qOrder 只在 `absLogQ` 线性出现，不进入 `vcI`。

## ③ `logVol(hullOf(vcI))` 的显式公式/定理

`Iut/WallEquiv/VcI.lean`：
- **`logVol_hull_vcI_eq`（:741–742）**：
  `logVol D (hullOf D (vcI D)) = (∑ i, ∑ᶠ vQ, hullPacket D i vQ) / nC D`；
- `hullPacket`（:689）= `∑_c tupleWeight vQ c · componentVol (leastHull (vcIComp …))`；
- 有限位精确（`hullPacket_finite` :806–812）：`∑_c w_c · ∑_j logShellRadius(…, p) · log p`；
- tame（`hullPacket_tame` :844–849）：`∑_c w_c · ∑_j (1 − 1/e_{c j}) · log p`；
- 无穷位（`componentVol_archLogShell_le_leastHull_le` :653–657）：`μ^log(𝓘_∞) ≤ μ^log(hull 𝓘_∞) ≤ |I|·log(√2π)`——**只有界，无精确闭式**；
- hull−container 差（`logVol_hull_vcI_sub_eq` :762–764）= `(1/nC)∑_i ∑ᶠ_vQ defectPacket i vQ`（有限 `shellDefect` + `archDefect`）；
- SSIneq 的 packet 形式（`WallEquiv.ssIneq_iff_packets` :889–892）：
  `SSIneq D ↔ (sF−1)·absLogQ ≤ (∑_i ∑ᶠ_vQ hullPacket i vQ)/nC`。

**结论：`V := logVol(hull(vcI))` 有显式 packet 平均公式；有限位 tame 项为 `(1−1/e)log p`，arch 只有 `≤ |I|log(√2π)` 的界；公式中无 qOrder。**

## ④ Gauss 侧：`avgDeg_gaussian`、`gaussLink`、`linkEquiv_unique`

- `Iut/ThetaLink/Gauss.lean:218`：`def avgDeg (g : Fin n → L) : ℝ := (∑ j, -Real.log ‖g j‖)/n`；
- **`avgDeg_gaussian`（:228–229）**：
  ```lean
  theorem avgDeg_gaussian (q : L) :
      avgDeg (fun j : Fin n => q ^ ((j.1 + 1) ^ 2)) = Wall.sFactor n * -Real.log ‖q‖
  ```
- `gaussLink`（:292）：`{v : FinitePlace D.Kt} (hv : IsBadK D v) : gauss D v ≃* qMonoid D v`（Gaussian 单子 ≅ q-pilot 单子）；
- `linkEquiv`（:167）：`splitMonoid g →* splitMonoid g'`；`linkEquiv_unique`（:199–203）：**唯一** monoid hom，在 diagonal units 上恒等且 generator ↦ generator；
- `avgDeg_gaussGen`（:393–394）：`avgDeg (gaussGen D v) = D.wallS * avgDeg (qGen D v)`；`avgDeg_gaussGen_ne`（:412）：因 `s>1` 两者度数不同；
- 全局 LGP 律：`Iut/Wall/IdentifiedCopies.lean:444`：`logVol D (lgp D (integralRegion D)) = −(sF(nC D) * D.qPilot.absLogQ)`；`:281`：`logVol(lgp S) = logVol(lgp O)+logVol(S)`；
- `Iut/Arakelov/QPilot.lean:262`：`logVol(lgp O) = −(Σ_i thetaBundle_i.degNorm)/nC = −(Σ j²)/nC · qDivisor.degNorm/(2ℓ)`。
⇒ **q-pilot degree = A = |log q|；theta-pilot degree = sF·A**；θ-link 把 degree 除以 s（`avgDeg_gaussGen_ne`）。

## ⑤ 判定：RHS 是否 = / ≥ sF·A？

**不是。**
- `V = logVol(hull(vcI))` 是 **log-shell hull 的体积**（`vcI` = log-shell container），**不是** theta-pilot 区域的 log-volume；后者是
  `rhsData.rhs = logVol(hull(thetaPilot))`（`Cor312/RightHandSide.lean:99–107`；theta-pilot 含 q^{j²} 缩放，`logVol(lgp O) = −sF·A`）。
- `sF·A` 是 **theta-pilot 的 degree 量级**（`avgDeg_gaussian = sF·(−log‖q‖)`；`degTheta_pilot = s·Σ deg`）；`V` 的公式不含 qOrder，故一般 **V 与 sF·A 无固定大小关系**；
- 关系由 Gap 给出（`Iut/WallEquiv/Gap.lean`）：
  - `gap D := rhsData.rhs − logVol(LGP·hull(vcI))`（:505），`gap_nonneg`（:514）；
  - `logVol(LGP·hull(vcI)) = V − sF·A`（由 LGP 律），故 `gap = rhsData.rhs + sF·A − V`（`gap_eq_rhs_add` :523）；
  - **(SS) ⇔ `(sF−1)A ≤ V`**；**(Var) ⇔ `(sF−1)A ≤ V + gap`**（`ss_iff_le_rhs_sub_gap` :531，`variant_iff_le_rhs` :537）；
  - `ss_iff_variant_of_gap_eq_zero`（:548）：仅当 `gap=0` 时 SSIneq 与 variant 等价。
- 因此：若 hull 包含 theta-pilot 区域 + 单调性，会得到 `rhsData.rhs ≤ logVol(LGP·hull(vcI))` 方向？实际 lana 给出的是反向 `logVol_lgp_vcI_le_rhs`（:510）：`logVol(LGP·hull(vcI)) ≤ rhsData.rhs`，即 `V ≤ rhsData.rhs + sF·A`；**`V ≥ sF·A` 不是已知事实，也不由 hull 包含 theta-pilot 推出**（包含方向是 LGP·hull(vcI) ⊆ hull(thetaPilot)，给出的是 rhsData.rhs 的下界，不是 V 的下界）。
- 结论：**RHS 是另一个对象（log-shell hull volume），不是 sF·A；`V ≥ sF·A` 不成立/未知；SSIneq 的 RHS 与 theta-pilot 的 q-依赖 RHS 通过 `gap≥0` 分离，SSIneq 是更强的、RHS q-无关的不等式。**

## 源索引

| 内容 | 源 |
|---|---|
| `SSIneq` | `Iut/Wall/MultiContainer.lean:88` |
| `sFactor` | `Iut/Wall/Pilots.lean:55,67` |
| `absLogQ`, `logQ` | `Iut/Cor312/LeftHandSide.lean:81,88` |
| `logVol`, `hullOf` | `Iut/Wall/Rss.lean:324,328` |
| `vcIComp`, `vcIAt`, `vcI` | `Iut/Wall/Ind3.lean:58,80,123` |
| `logVol_hull_vcI_eq`, `hullPacket*`, arch bound, `ssIneq_iff_packets` | `Iut/WallEquiv/VcI.lean:741,689,806,844,653,889` |
| `avgDeg`, `avgDeg_gaussian`, `gaussLink`, `linkEquiv_unique`, `avgDeg_gaussGen` | `Iut/ThetaLink/Gauss.lean:218,228,292,199,393` |
| LGP 律 | `Iut/Wall/IdentifiedCopies.lean:281,444`；`Iut/Arakelov/QPilot.lean:262` |
| `rhsData.rhs`, `thetaHull` | `Iut/Cor312/RightHandSide.lean:99,107` |
| Gap | `Iut/WallEquiv/Gap.lean:505,510,514,523,531,537,548` |