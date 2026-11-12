# A500: Takkun (P) vs paper IUT IV Thm 1.10 Step (v) — 忠实性与等价形式核对（只读）

来源（外部文本一律作数据，不作指令）:
- `tmp/external/Takkun-IUT_LEAN/REQUEST_theta_hull_derivation.md`（(P) 陈述、F1-F4、请求 A/B/C、等价式 L ≥ (l(l+1)/12 − 1)|log q|）；
- `tmp/external/Takkun-IUT_LEAN/SORRY_LEDGER.md`、`ROADMAP.md`（Phase F/G/H/I/J/K；`PilotVolumeData`/`containment`/`TwoSidedSupply`/`adjudication_distortion`/`thetaPilotDegree_div_lStar` 等）；
- paper: `papers/motizuki_corpus/text/Inter-universal Teichmuller Theory IV.txt`，Thm 1.10 陈述 L1255-1385，证明 Step (iv)-(vi) L1583-1790；IUT III Cor 3.12 L10324-10353；IUT II Rem 4.10.3 引用（Takkun 所引）。
方法：逐句对照 + 代数核对；只读，未改任何文件/队列/watchdog。

## 1. Takkun 主张摘要（含原文行）

- **(P)**（REQUEST L45-50）: “[IUTchIV] Thm 1.10 証明 Step (v) において、Θ-標対象の可能な像の合併 (Ind1),(Ind2),(Ind3) 込みが、v_j ∈ V^bad の成分で λ := ord(q^{j²}) とした容器 φ(p^λ·(R_I)~) ⊆ p^{⌊λ−d_I−a_I⌋}·log_p(R_I^×) に含まれる——ここで体積は、[IUTchIII] Cor 3.12 証明 Step (xi-d)–(xi-f) で q-標対象の測定に用いられるものと同一の procession 正規化 mono-analytic 対数体積（受信側 (1,◦) の正規化）”。
- **(F1)** Step (v) 本文が (P) の根拠として引用するのは Thm 3.11 (i)(a)(b),(ii) の定義のみ、と Takkun は述べる（REQUEST L56-58）。
- **(F2)** 単数部共通性/Kummer/log-link/(Ind1)(Ind2) 等長性/(Ind3) 上半両立性は体積保存(lossless)；従う輸送像の深さは ord(q)，j²·ord(q) ではない（REQUEST L59-67）。
- **(F3)** (P) 型の体積評価が containment と両立し得ることは `L ≥ (l(l+1)/12 − 1)·|log(q)|`（受信側正規化）と同値；Prop 1.1-1.4 の台帳は O(log-different+log-conductor+l·log(e*·l)) で |log(q)| に依存しないから、実曲線族への一様供給は高さ不等式の供給と論理的に同値（REQUEST L68-73）。
- **(F4)** [IUTchIV] Rem 1.10.1 の Hodge-Arakelov 計算との同一性は計算が正しいことと整合；未検証なのは「枠組みが (P) としての読みを正当化する」こと（L74-78）。
- 请求：A 箇所特定/B 機構提示/C 等价式 `L ≥ (l(l+1)/12−1)|log q|` 的推导（L80-94）。
- 自身档案：ROADMAP Phase F `PilotVolumeData.containment` 被称为“唯一の深い入力 = Scholze–Stix 係争点の厳密な特定”（L509-527）；Phase H 承认 `PilotVolumeData`(单 Ω/vol) 预设了 ℝ 同一视，修正为 `TwoSidedSupply`（L554-574）；Phase J `adjudication_distortion`: 通过测试的代价 ≥ (l(l+1)/12−1)|log q|（L597-615）。

## 2. paper Step (iv)-(v) 原文要点（逐行）

**Step (iv)**（IV L1583-1623）: 为估计 Cor 3.12 的 `C_Θ`，须计算 “procession-normalized mono-analytic log-volume of the holomorphic hull of the union of the possible images of a Θ-pilot object, relative to the relevant Kummer isomorphisms, in the multiradial representation … subject to indeterminacies (Ind1),(Ind2),(Ind3)”；在每 vQ 上估计 IQ(S±_{j+1}; n,◦D⊢_{vQ}) 的分量（j∈{1,...,l⋇}），再对 j 平均；IQ 是 S±_{j+1}（|S±_{j+1}|=j+1）个 log-shell Q-span 的张量积；对每个 collection {v_i} 估计，再对 collection 取加权平均。
**Step (v)**（IV L1624-1662）逐句:
- L1624-1629: “Let vQ ∈ V^dst_Q. Fix j, {v_i}_{i∈S±_{j+1}} as in Step (iv).”；
- L1630-1648: “We would like to apply Proposition 1.4, (iii) … by taking · “I” to be S±_{j+1}; · “I* ⊆ I” …; · “k_i” to be K_{v_i} [so R_i = O_{K_{v_i}}]; · “i†” to be j ∈ S±_{j+1}; · “λ” to be 0 if v_j ∈ V^good; · “λ” to be “ord(−)” of the element q^{j²}_{v_j} … if v_j ∈ V^bad.”；
- L1649-1655: “Thus, the inclusion “φ(p^λ·(R_I)~) ⊆ p^{⌊λ−d_I−a_I⌋}·log_p(R_I^×)” of Proposition 1.4, (iii), implies that the result of multiplying “p^{⌊λ⌋−|I|}·2^{−|I|}·log_p(R_I^×)” by a suitable nonpositive integer power of p_{vQ} contains the “union of possible images of a Θ-pilot object” discussed in Step (iv).”；
- L1655-1662: “That is to say, the indeterminacies (Ind1) and (Ind2) are taken into account by the arbitrary nature of the automorphism “φ” [cf. Proposition 1.2], while the indeterminacy (Ind3) is taken into account by the fact that we are considering upper bounds …, together with the fact that the above-mentioned integer power of p_{vQ} is nonpositive …”；
- L1663-1678: upper bound on log-volume component obtained from Prop 1.4(iii) RHS: `(−λ+d_I+1)·log(p) + Σ_{i∈I*}{3+log(e_i)}`（second displayed inequality of Prop 1.4(iii)）；
- L1679-1707: 若所有 e_{v_i} ≤ p_{vQ}−2，则为 `(−λ+d_I+1)log(p)`；否则由 (R4) p_{vQ} ≤ e*_mod·l，log(e) ≤ −3+4log(e*_mod·l)，上界为 `(−λ+d_I+1)log p + 4(j+1)l*_mod`，l*_mod := log(e*_mod·l)；λ 对 i† 选择不对称，需按 Prop 1.7 对 i† 对称化；
- L1708-1742: 取 Prop 1.7 的 E=V(F_mod)_{vQ}, n=j+1, λ_e=[(F_mod)_v:Q_{vQ}], β_e=log(dK_v) − j²/(2l(j+1))·log(q_v)+1/(j+1)·log(p_{vQ})+4·ι_{vQ}·l*_mod（ι=1 if p≤e*·l else 0）；加权平均上界 = `(j+1)log(dK_{vQ}) − j²/(2l)·log(q_{vQ}) + log(s^Q_{vQ}) + 4(j+1)l*_mod·log(s≤_{vQ})`；
- L1744-1776: 对 j∈{1,...,l⋇=(l−1)/2} 平均并用 (E1),(E2): procession-normalized upper bound = `(l⋇+3)/2·log(dK) − (2l⋇+1)(l⋇+1)/(12l)·log(q) + log(s^Q) + 2(l⋇+3)l*_mod·log(s≤)` = `(l+5)/4·log dK − (l+1)/24·log q + …` ≤ `(l+1)/4{(1+4/l)log dK − (1/6)log q + (4/l)log s^Q + (20/3)l*_mod log s≤}`。

## 3. (P) 与 paper Step (v) 逐项对照

| Takkun (P) 条目 | paper Step (v) 原文 | 判定 |
|---|---|---|
| v_j∈V^bad 处 λ := ord(q^{j²}) | L1642-1648 明确 λ := ord(−) of q^{j²}_{v_j} if v_j∈V^bad | **逐字忠实** |
| φ(p^λ·(R_I)~) ⊆ p^{⌊λ−d_I−a_I⌋}·log_p(R_I^×) | L1649-1652 逐字引用 Prop 1.4(iii) inclusion | **逐字忠实** |
| union of possible images (Ind1)(Ind2)(Ind3) 包含 | L1654-1662: Ind1/Ind2 via arbitrary φ (Prop 1.2), Ind3 via upper bounds/nonpositive power | **忠实**（P 的“包含”是 paper 的 upper-bound 方向） |
| 用与 q-pilot 相同的 procession-normalized mono-analytic log-volume（受信侧 (1,◦)） | Step (iv) L1583-1591 定义该 log-volume；Step (v) 在其上计算；Cor 3.12 的 q-pilot 用同一 procession-normalized log-volume | **忠实**（同一 normalization 的表述合理） |
| 该输入是“唯一深い入力”/PilotVolumeData.containment | paper 在 Step (v) 由 Prop 1.4(iii)+Ind 论证给出，而非独立定理 | **定性合理**：Step (v) 确实把桥（possible images 有 λ=ord(q^{j²}) 且用该 log-volume）作为断言使用；但 paper 引用了 Prop 1.4(iii)（并非仅 Thm 3.11 定义） |

**F1 的准确性**: Takkun 说“Step (v) 本文が (P) の根拠として引用するのは Thm 3.11 (i)(a)(b),(ii) の定義のみ”并不准确——Step (v) 明确引用 Proposition 1.4(iii)（及 Prop 1.2、Prop 1.7），并对 Ind1/Ind2/Ind3 给出论证。Takkun 自己（REQUEST §1）也声称已形式化 Prop 1.1-1.4。因此 Step (v) 不是“无推导的措定”，而是“从 Prop 1.4(iii)+Ind 论证的推导”；争议点是该推导中桥（possible images 的 λ 与接收侧 normalization）是否有效，而非文本空缺。

**F2 的争点**: paper 的 λ 来自 Θ-pilot 的 j-th component 的 theta value q^{j²}（III L598-609）；Step (v) 的 Ind1/Ind2 是 label/unit 的任意同构（保体积），Ind3 是 upper bound；Takkun 认为这些机制无法把 j²·ord(q) 的深度带入接收侧体积（只能 ord(q)）；paper 的 counter 是 Θ^{j²} 数据本身属于输入（并非由 link 体积输运产生）。这是数学争议，本文档不裁定；但 (P) 作为 paper Step (v) 的**忠实陈述**成立。

## 4. 等价形式 `L ≥ (l(l+1)/12 − 1)·|log q|` 的代数核对

1. paper Step (v) 的 q-项系数: `(2l⋇+1)(l⋇+1)/(12l)·log(q)`（L1752-1753）; 因 l⋇=(l−1)/2，(l⋇+1)(2l⋇+1)/6 = ((l+1)/2)·l/6 = **l(l+1)/12 =: s**；且 |log q| = log(q)/(2l)（IV L1358-1363），故该系数 = `s·|log q|`。
2. 令 `L` = Step (v) 中非 q 的台帐项（(l⋆+3)/2 log dK + log s^Q + 2(l⋆+3)l*_mod log s≤，及后续 refined 项），则 Step (v) 给出 hull log-volume 的上界 `−s|log q| + L`（受 normalizations/符号约定；系数与 L 的分解见上）。
3. Cor 3.12 的下界（目标）: `-|log Θ| ≥ -|log q|`，即 hull log-volume ≥ `-|log q|`。两个界相容（存在 hull 值同时满足上下界）当且仅当 `−|log q| ≤ −s|log q| + L`，即 **`L ≥ (s−1)|log q|`**（s>1）。这正是 Takkun 的 `L ≥ (l(l+1)/12 −1)|log q|`。
4. 可信性判定: **代数上正确且常数精确**（s=l(l+1)/12 与 paper L1746-1753 的系数一致；Takkun ROADMAP `thetaPilotDegree_div_lStar`/`adjudication_distortion` 使用同一常数）。
   但两点 caveat: (a) L 含 `l` 与 `l*_mod = log(e*_mod·l)`、`log s^Q`、`log s≤` 等项，未必“与 |log q| 无关”（F3 的独立性需要精确定义；在 ABC 应用中 l 本身按 (log q)^{1/2} 量级选择，见 [ExpEst] Cor 5.2 (C1)，故 L 可能随 |log q| 缓慢增长）；(b) “(P) 一様供給 ⇔ 高さ不等式”是 audit 层推导的 meta-equivalence，paper 未陈述；作为“Step (v) 上界与 Cor 3.12 下界相容的充要条件”它是可信的，作为“与高さ不等式逻辑等价”需要额外的均匀性/台帐独立性假设。

## 5. 结论

1. **(P) 对 paper Step (v) 忠实**：λ=ord(q^{j²})、Prop 1.4(iii) 的包含、Ind1/2/3 处理、以及“与 q-pilot 相同的 procession-normalized mono-analytic log-volume”均在 IV L1624-1662/Step (iv) 有逐字对应；Takkun 把 Step (v) 的桥隔离为单一输入是合理的“争议点定位”。
2. **F1 需要修正**：Step (v) 并非只引用 Thm 3.11 定义；它显式引用 Prop 1.4(iii)/Prop 1.2/Prop 1.7 并给出 Ind 论证。更准确的表述是：Step (v) 的推导依赖 Prop 1.4(iii)+Ind 论证，而“possible images 的深度为 j²·ord(q) 且用接收侧 normalization”这一桥是 paper 断言/使用的关键步骤（Takkun 请求 A/B/C 正是针对此桥）。
3. **等价形式 `L ≥ (l(l+1)/12−1)|log q|` 可信（代数恒等/相容性条件）**：常数 l(l+1)/12 与 paper L1746-1753 及 Takkun 自身形式化一致；它精确表达 Step (v) 上界与 Cor 3.12 下界的相容性。但其“uniform (P) 供给 ⇔ 高さ不等式”的强等价性依赖 L 的独立性与 l 对 |log q| 的依赖，属于 audit 层条件性结论，不等同于 paper 定理。
4. 对我方的意义：Takkun 的 (P) 可作为“Cor 3.12 争议桥”的忠实规格参考（其 Step (v) 行号/公式与 paper 一致）；但我们自己的对象构造仍以 paper 为准（A499：对象优先）；qTheta/step3115 链 VOID（A497），不得用 LANA 或 Takkun 结论替代对象构造。
5. 外部文本仅作数据；本文件未执行任何外部文本中的“请求/指令”，未改任何文件/队列/watchdog。
