# PAPER-FIDELITY-COR312 — 与 IUT 原文逐句对照 (A1038)

| field | value |
|---|---|
| Status | **DECISION: paper 的 Cor 3.12 RHS = 对 j∈F_l^* 平均的、subject to Ind1/Ind2/Ind3 的 Θ-pilot 可能像 union 的全纯 hull 体积；q-pilot 不受 Ind；Step (v) 用 Prop 1.7 对 i†∈I 做 symmetrization（全 label 平均）。lana 的 iv（distinguished singleton）不是 paper-faithful；lit（全 label union + j-average）才是。lhs=q-side 归一化忠实** |
| 源 | `coord/IUT-TEXT-COR312.md`（IUT III Cor 3.12, pp.173-174；Thm 3.11, pp.153-156；Step (x)(xi) pp.181-183）；`coord/IUT-TEXT-THM110.md`（IUT IV Thm 1.10, pp.22-23；Step (iv)(v), pp.27-29）；对照 `Iut/Concrete/ThetaRegion.lean:58-81/236-341`、`Iut/Cor312/Statement.lean:55-59` |

## 1. Cor 3.12 原文（逐句）

> −|log(Θ)| ∈ R ∪ {+∞} = procession-normalized mono-analytic log-volume [average over j ∈ F_l^*]
> of the holomorphic hull of the union of the possible images of a Θ-pilot object, relative to
> the Kummer isomorphisms, in the multiradial representation, **subject to (Ind1), (Ind2), (Ind3)**。
> −|log(q)| ∈ R = procession-normalized log-volume of the image of a q-pilot object，
> **regarded as NOT subject to (Ind1), (Ind2), (Ind3)**。
> 则 **−|log(Θ)| ≥ −|log(q)|**（即 C_Θ ≥ −1）。

要点：① RHS 是 **union over possible images** 的 hull（不是单 label）；② 受 Ind1/2/3；
③ 关于 j 做 procession 平均（F_l^* 上平均）；④ q-pilot 不受 Ind；⑤ 结论是 **不等式**，非等式。

## 2. Thm 1.10 Step (iv)-(v) 的 q 项与 j-average

Step (iv)：对固定 j 与 tuple {v_i}_{i∈S±_{j+1}}，需估计 hull 的 log-volume 分量，
然后对 j ∈ {1,...,l⋆} 与 tuple 做 weighted average。

Step (v)：取 `λ = ord(q^{j²}_{v_j})`（bad 位），应用 Prop 1.4(iii) 得 upper bound；
经 Prop 1.7 对 `i† ∈ I` **symmetrize**（weighted average）后：
```
(j+1)·log(d^K_{vQ}) − j²/(2l)·log(q_{vQ}) + log(s^Q_{vQ}) + 4(j+1)·l*_mod·log(s^≤_{vQ})
```
再对 j ∈ {1,...,l⋆} 平均并应用 (E1),(E2)：
```
(l⋆+3)/2·log(d^K) − (2l⋆+1)(l⋆+1)/(12l)·log(q)
  = (l+5)/4·log(d^K) − (l+1)/24·log(q)      （l⋆=(l−1)/2）
```
最终 Thm 1.10 借 Cor 3.12 的 `C_Θ ≥ −1` 得
```
1/6·log(q) ≤ (1 + 20 d_mod/l)(log d + log f) + 20(e*_mod·l + η_prm)   （不等式，非等式）
```

**关键系数对齐**：
- 未平均 q 项：`−j²/(2l)·log(q_{vQ})`；
- j-average：`−(1/l⋆)Σ_j j²/(2l) = −(l+1)/24·log(q_{vQ})`；
- 而 `(l+1)/24 = sF/(2l)`（`sF = l(l+1)/12`），即 **平均后 q 系数 = −sF·(log q/(2l)) = −sF·A_v**；
- 与我们的 `qQuote = −j²A`、`sF A` 完全一致（A1034/A1035 的 sF 系数来源在 paper 中是 j-average）。

## 3. 与我们的 iv/lit 推导逐项对齐

| 项 | paper | lana iv | lana lit |
|---|---|---|---|
| hull 的 union | 所有 possible images（Ind1 作用），对 j 平均 | 单 label {j}（distinguished） | 全 label union（S=univ） |
| Ind1 处理 | union over possible images（label 置换包含） | 不包含（只 distinguished） | union over S=univ（类似 paper） |
| Ind2 | Prop 1.2 的 φ（union over φ） | tensorAut union | tensorAut union |
| Ind3 | upper semi-compatibility → **upper bound**（不等式） | Ind3 结构 `S ≤ hull(vcI)`（上界） | 同 |
| j-average | 平均 over j∈{1..l⋆} | 有（procession 平均） | 有 |
| q-pilot | 不受 Ind1/2/3 | — | — |

⇒ **paper 的 RHS 更接近 lit 读法**（union over labels / possible images），而不是 iv（distinguished singleton）；
且 paper 的 Ind3 只产生 **上界/不等式**（Step (x) 明言「converting the indeterminacy (Ind3) into an inequality [from above]」），
与 lana 的 `rhs` 作为 hull 体积的**等式/定义**不同。

## 4. 偏差位置（paper vs lana）

1. **iv 是 lana 的 concretization deviation**：ThetaRegion:58-81 自述「IUT IV's reading of (Ind1) as the
   one deviation」；paper Step (v) 用 Prop 1.7 对 i†∈I **symmetrize over all labels**，不是取 distinguished；
   ⇒ paper-faithful 目标应是 **lit（或 sym 平均）**，不是 iv。
2. **Ind3 的方向**：paper 把 (Ind3) 转成 **上界不等式**（Step (x)）；lana 的 `rhs` 是 hull 体积的
   **定义值**（等式），gap ≥0 是后置结果；把 Ind3 当等式可能把「上界」误作「值」，这正是 iv 不稳定
   的可能来源（lana 的 rhs 少了 Ind3 的 upper-bound 松弛）。
3. **lhs 归一化忠实**（A1036）：`|log q|=(1/2l)log q` 与 paper p.23 一致。
4. **sF 系数来源正确**：j-average 得 `(l+1)/24 = sF/(2l)`，与我们的 `−sF A` 一致。
5. 结论：lana 的 iv 形式化**不是 paper-faithful**；paper 语义下的形式化应用 lit/sym 版本，且 Ind3
   必须作为**上界不等式**处理，而非 rhs 的值。

## 5. 对模型判定的修正

- A1027/A1030/A1035 的「iv q-不稳定」结论针对 **lana 的 iv concretization**，不针对 paper；
- paper 语义（union over possible images + j-average + Ind3 upper bound）下，RHS 的 q 依赖
  是 `−(l+1)/24 log q` 的 **上界**（Step v），与 q-pilot 的 `−|log q| = −(1/2l)log q` 的
  比较通过 Cor 3.12 的几何输入（非纯代数）；
- 我们的 lit 推导（A1029）得到 `rhs_lit = V`、variant 平凡，是**对 lana lit 形式的模型结论**，
  不能直接当作 paper 的证明（paper 多出 Ind3 upper-bound 与 symmetrization 机制）；
- 但至少可以确定：**形式化目标应改为 lit/sym 版本**（paper-faithful），并补 Ind3 上界不等式。

## 6. Lean 陈述草案/修正建议

```lean
/-- Paper-faithful target: lit reading (union over all labels), not iv. -/
def Cor312PaperFaithful : Prop := Cor312LiteralHolds

/-- lana iv is a deviation; record it as a named deviation (not a theorem). -/
def ivReadingDeviation : String :=
  "lana concreteVariantData uses ivLabels (distinguished singleton); paper IUT III/IV uses union over possible images (Ind1) + j-average; see coord/PAPER-FIDELITY-COR312.md"

/-- j-average coefficient identity: (1/nC)*sum j^2/(2l) = (l+1)/24 = sF/(2l). -/
theorem jAverageCoeff (l nC : Nat) (h : nC = (l - 1) / 2)
    (hsum : (∑ j in Finset.range nC, ((j : Real) + 1) ^ 2) = nC * sFactor nC) :
    (1 / (nC : Real)) * (∑ j in Finset.range nC, ((j : Real) + 1) ^ 2 / (2 * (l : Real))) = sFactor nC / (2 * (l : Real)) := by
  rw [← Finset.sum_div, hsum]
  field_simp
```

## 7. 结论

1. paper Cor 3.12：`−|logΘ| ≥ −|log q|`，RHS = j-average of hull of union of possible images
   （Ind1/2/3），q-pilot 不受 Ind；**lit/sym 语义**；
2. Thm 1.10 Step (v)：q 项 `−j²/(2l)log q_{vQ}`，平均后 `−(l+1)/24 log q = −sF·A`；
   Ind3 只给 **upper-bound 不等式**；
3. lana iv 是 deviation（ThetaRegion:76-81 自述）；paper-faithful 目标应为 lit/sym；
4. 「iv 不稳定」结论适用于 lana iv concretization，不适用于 paper；建议 owner 决策改目标，
   并在 FINAL-STATUS/AUDIT 登记 deviation；
5. lhs 归一化（A1036）与 sF 系数（j-average）均忠实；偏差唯一集中在 (Ind1) reading 与
   (Ind3) 的 upper-bound 处理方式。