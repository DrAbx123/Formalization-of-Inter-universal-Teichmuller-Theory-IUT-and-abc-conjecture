# PROOF-CHAIN-COR312 — 按 paper 原文的 Cor 3.12 证明骨架 (A1039)

| field | value |
|---|---|
| Status | PARTIAL (proof-chain 骨架；逐 display 翻译与 lana 偏差标注；不写 Lean、不编译) |
| 源 | `coord/IUT-TEXT-COR312.md`（IUT III pp.153-183）、`coord/IUT-TEXT-THM110.md`（IUT IV pp.22-29）、`coord/PAPER-FIDELITY-COR312.md`（A1038 判定） |

## 1. 记号（paper → 我们）

| paper | 我们 | 说明 |
|---|---|---|
| initial Θ-data (F/F, X_F, l, C_K, V, V_bad_mod, ϵ) | `D : InitialThetaData` | Definition 3.1 |
| l⋆ = (l−1)/2 | `nC D = (D.ℓ - 1)/2` | capsule 数 |
| S±_{j+1} = {0,...,j}, j∈|F_l| | `Lab nC i`，j = i+1 | capsule labels |
| q_v（= q_v^{2l} 为 Tate 参数） | `qrootOf D v` = q_Tate^{1/(2l)} | IUT I Ex 3.2(iv)；`ordp qroot = qOrder/(2l·e_w)` |
| log(q) = deg(q^ADiv) | `logQ = Σ_w weight_w * qOrder_w * log p_w` | lana LeftHandSide:81-84 |
| \|log(q)\| = (1/(2l))·log(q) | `absLogQ = logQ/(2l))` | lana :86-88；IUT IV p.23 |
| −\|log(q)\| | `lhs = -absLogQ` | lana :90-93 |
| −\|log(Θ)\| | `rhs`（signed；R = \|logΘ\| = −rhs） | lana RightHandSide:107 |
| procession-normalized log-vol | `logVol = processionVol` = (1/nC)Σ_i | LogVolume:207 |
| q-pilot q-side 系数 | `A = absLogQ`；`T = (sF−1)A` | A1034/A1035 |
| Θ-hull 体积 | `V = logVol(hull(vcI))` | Ind3:122-134 |
| gap | `gap = rhs + sF·A − V` | Gap:521-527 |
| ind2 | `ind2Term = V(θ-comp hull) − V(scaleElt•hull)` | Gap:747-756 |

## 2. Cor 3.12 证明的 displays（按原文顺序）

### D1 — Cor 3.12 statement（PDF p.173）
```
−|log(Θ)| ≥ −|log(q)|        (i.e. C_Θ ≥ −1)
−|log(Θ)| := procession-normalized log-volume [average over j∈F_l^*] of
  the holomorphic hull of the union of the possible images of a Θ-pilot object,
  subject to (Ind1),(Ind2),(Ind3);
−|log(q)| := procession-normalized log-volume of the image of a q-pilot object,
  NOT subject to (Ind1),(Ind2),(Ind3).
```
**类型**：定义（两个量）+ 不等式结论。
**翻译**：`lhs = -absLogQ`，`rhs = -(R)`，`Variant ⇔ absLogQ ≥ R`。
**所需引理**：Θ-pilot hull 定义（Definition 3.8 + Remark 3.9.5）、q-pilot 定义（Def 3.8）。

### D2 — Proof WLOG（p.174）
```
−|log(Θ)| < 0   WLOG (若 −|log(Θ)| ≥ 0 则 ≥ 0 > −|log(q)|)
```
**类型**：归约/估计。
**翻译**：`R = |logΘ| > 0` 情形，或直接 `rhs < 0`。
**所需**：`0 < |log(q)|`（q-pilot 正性）。

### D3 — n,◦U 定义（pp.174-175）
```
n,◦U_{j,vQ} ⊆ n,◦UQ_{j,vQ} = IQ(S±_{j+1}; n,◦D⊣_{vQ})
n,◦U_{j,vQ} = union of possible images of Θ-pilot, subject to Ind1,Ind2,Ind3
n,◦U_{j,vQ} := holomorphic hull of n,◦U_{j,vQ}
−|log(Θ)| 有限 ⇒ negative
```
**类型**：定义展开。
**翻译**：`thetaPilotOn S`（lana 的 region），`hullOf`；`R = -rhs`。
**所需引理**：`logVol_le_rhs`（hull 包含）、`logVol` 有限性/可加性。

### D4 — Thm 3.11 (i) 的 Ind1/Ind2/Ind3（pp.153-156）
```
(a)(b)(c) 数据 up to indeterminacies:
(Ind1) automorphisms of the procession Prc(n,◦D⊣_T);
(Ind2) independent copies of Ism on each direct summand of the j+1 factors;
(Ind3) upper semi-compatibility relative to log-links ⇒ upper bound inequality.
IQ(S±_{j+1}; ...) = tensor product of j+1 copies of direct sum of log-shells.
```
**类型**：定义 + 不确定性（Ind1/2 是等价关系，Ind3 是不等式）。
**翻译**：`indAut = tensorAut / archIndAut`（lana IndAut:298-301）只覆盖 Ind2；Ind1 由 label union
（ThetaRegion:168-175 的 S）；Ind3 在 lana 是 `Ind3 = {S | S ≤ hull(vcI)}`（Ind3:213）+ gap ≥0。
**所需引理**：`indAut` 的 admissible/σ-不变性、semi-compatibility 的上界。

### D5 — Step (x)（p.181）
```
log-volumes ∈ R are invariant under (Ind1),(Ind2), and convert (Ind3) into
an inequality [from above].
```
**类型**：不变性 + 上界。
**翻译**：`logVol` 对 label 置换/tensorAut 不变；Ind3 ⇒ `logVol(hull) ≤ upper bound`。
**所需引理**：`processionVol_perm_inv`、`logVol_le_logVol_hullOf`（Ind3:136-147）、upper bound 估计。

### D6 — Step (xi-a/c/d)（pp.181-183）
```
(xi-a) q-pilot at (1,0) ↔ Θ-pilot at (0,0) via Θ×μ_LGP-link;
(xi-c) multiradial algorithm yields 1,◦U linked to q-pilot representation on 1,◦UQ;
(xi-d) compare via determinant / log-volume: R_{≤−|log(Θ)|} ⊆ R; −|log(q)| ∈ R.
```
**类型**：构造（LGP-link）+ 比较（determinant/log-volume）。
**翻译**：`lgp D`（IdentifiedCopies:281, `logVol_lgp = logVol − sF·A`）；比较 `lgp·hull(vcI)` 与
`hull(thetaPilot)` 的包含关系（`inHullOfImage_lgp`，IdentifiedCopies:229）。
**所需引理**：Θ×μ_LGP-link 的实现（lana `lgp` 的 `isAdelic`）、determinant side 的 log-volume 比较。

### D7 — Step (xi-d) 结论（pp.181-183）
```
−|log(Θ)| ≥ −|log(q)|   (Cor 3.12)
```
**类型**：不等式（由比较 + 上/下界）。
**翻译**：`Variant (concreteVariantDataLit)` 或 paper-faithful lit 版本。
**所需引理**：`lgp` 比较 + Ind3 上界 + 归一化。

### D8 — Thm 1.10 Step (iv)（p.27）
```
estimate the procession-normalized log-volume of the hull at each vQ;
component in IQ(S±_{j+1}; ...) for each j∈{1,...,l⋆}; average over j;
for each tuple {v_i}, estimate via Prop 1.4(iii) with λ = ord(q^{j²}_{v_j}) (bad).
```
**类型**：估计（upper bound）+ 平均。
**翻译**：`hullPacket_i(vQ)` 的 quantitative bound；`j-average` 即 `sF = Σj²/nC`。
**所需引理**：Prop 1.4(iii) 包含式、`(E1)(E2)` 的估计、Prop 1.7 的 weighted average。

### D9 — Thm 1.10 Step (v)（pp.27-29）
```
per (j, tuple): (j+1)log d^K_{vQ} − j²/(2l)log(q_{vQ}) + log s^Q + 4(j+1)l*_mod log s^≤
after symmetrization over i†∈I (Prop 1.7);
average over j∈{1,...,l⋆}:
(l+5)/4 log d^K_{vQ} − (l+1)/24 log(q_{vQ}) + log s^Q + (l+5)l*_mod log s^≤
≤ (l+1)/4 { (1+4/l)log d^K − 1/6 log(q) + ... }
```
**类型**：估计 + 平均 + 归一化。
**翻译**：`(l+1)/24 = sF/(2l)`（A1038 对齐）；`−sF·A` 即 q 项；`arch`/`T` 项对应 `log d^K`/`log s`。
**所需引理**：Prop 1.7 的 weighted-average/symmetrization、`(E1)(E2)`、`Σj²/nC = sF`。

### D10 — Thm 1.10 结论（pp.22-23）
```
C_Θ = (l+1)/4 * |log(q)| * { ... − 1/6(1−12/l²)log(q) } − 1
C_Θ ≥ −1  ⇒  1/6 log(q) ≤ (1+20d_mod/l)(log d + log f) + ...
```
**类型**：不等式（由 Cor 3.12 的 C_Θ≥−1）+ 估计。
**翻译**：`1/6 log q ≤ ...` 是算术估计，不对应 `Variant` 本身；它是 Cor 3.12 的后果。
**所需引理**：`1/6` 系数的算术、`d_mod/l` 估计、`C_Θ` 定义。

## 3. 类型汇总

| display | 类型 | 关键量 |
|---|---|---|
| D1 | 定义 + 不等式 | −\|logΘ\|, −\|log q\| |
| D2 | 归约 | sign |
| D3 | 定义展开 | n,◦U, hull |
| D4 | 不确定性定义 | Ind1/2/3 |
| D5 | 不变性 + 上界 | logVol, Ind3 |
| D6 | 构造 + 比较 | LGP-link, determinant |
| D7 | 不等式（结论） | Cor 3.12 |
| D8 | 估计 + 平均 | j, vQ, tuple |
| D9 | 估计 + 平均 + 归一化 | j²/(2l), (l+1)/24 |
| D10 | 估计/算术 | C_Θ, 1/6 |

## 4. 对照 lana：哪些步被改写/缺失

| paper step | lana 状态 | 偏差 |
|---|---|---|
| D1 RHS = union over possible images（Ind1 全部） | `concreteVariantData` 用 iv（distinguished singleton，ThetaRegion:60-62/315-316） | **deviation**（ThetaRegion:76-81 自述）；paper-faithful 是 lit/sym |
| D4 Ind3 = upper bound 不等式 | lana `Ind3` 只给 `S ≤ hull(vcI)`；`rhs` 是 hull 体积等式，gap≥0 后置 | 把 Ind3 的「上界」误作「值」；iv 不稳定的可能来源 |
| D5 Ind1/Ind2 log-vol 不变性 | lana 有 `processionVol` 的 label 置换不变性（`rhsDataOn_perm` 等） | 部分覆盖；symmetrization（Prop 1.7 weighted average）未显式 |
| D6 LGP-link/determinant 比较 | lana `lgp` + `inHullOfImage_lgp`（包含关系） | determinant side 的比较未显式形式化；只有 hull 包含 |
| D8/D9 Prop 1.4/1.7 定量估计 | lana 有 `hullPacket` 公式与 `j-average`（sF），但无 Prop 1.4/1.7 的定量 bound | 缺定量估计（估计/不等式），只有结构等式 |
| D10 1/6 log q 算术 | lana 未形式化（Thm 1.10 的 C_Θ 算术） | 缺 |

## 5. paper-faithful 形式化骨架（建议）

```lean
-- 1. lit 目标（union over labels / possible images）
def Cor312PaperFaithful : Prop := Cor312LiteralHolds   -- 或 sym 版本（Prop 1.7 平均）

-- 2. Ind3 作为 upper bound（而非 rhs 值）
def Ind3UpperBound (U : Region D) (bound : Real) : Prop := logVol D U <= bound
theorem ind3_upper_bound_of_hull : Ind3UpperBound (hullOf D (thetaPilot D)) (upperBound D)

-- 3. LGP/determinant 比较（paper Step xi-d）
theorem lgp_hull_le_theta_hull :
  logVol D (lgp D (hullOf D (vcI D))) <= logVol D (hullOf D (thetaPilotLit D))

-- 4. j-average 系数（paper Step v）
theorem jAverage_q_coeff (l nC) (h : nC = (l-1)/2) :
  (1/(nC:Real)) * (∑ j in Finset.range nC, ((j:Real)+1)^2/(2*(l:Real))) = sFactor nC/(2*(l:Real))

-- 5. 最终 Cor 3.12（lit / paper-faithful）
theorem cor312_paper_faithful : Cor312PaperFaithful
```

## 6. 结论

1. paper 证明链 = D1-D10：定义（D1/D3/D4）→ 不变性/上界（D5）→ 构造/比较（D6）→ 定量估计与平均（D8/D9）→ 结论（D7/D10）；
2. 关键数值对齐：`−(l+1)/24 log q = −sF·A`（j-average），lhs 归一化忠实（A1036）；
3. lana 的主要偏差：(a) iv vs paper 的 union/sym（D1）；(b) Ind3 上界被当作 rhs 值（D4/D5）；
   (c) 缺 Prop 1.4/1.7 的定量估计（D8/D9）；(d) 缺 determinant 比较（D6）；
4. 形式化路线：以 lit/sym 为目标 + Ind3 上界 + j-average 系数 + LGP 比较，按 D1→D10 顺序逐 display 写；
5. 本文件不写 Lean、不编译；建议作为 C 线 proof-chain 的权威路线图，并据此更新 FINAL-STATUS/AUDIT 的偏差记录。