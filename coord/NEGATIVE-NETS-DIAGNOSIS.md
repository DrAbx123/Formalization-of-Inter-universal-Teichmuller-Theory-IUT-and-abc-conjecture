# NEGATIVE-NETS-DIAGNOSIS — 336 条负局部项：模型 artefact 还是真实符号缺口

日期：2026-11-12；qpilot（A1006）。**仅 Python**；基于 `coord/c1_local_terms.jsonl`、`coord/c1_margin_v2.csv`。

## 1. 公式复核与样本

c1 使用（`tools/c1_batch.py` / `c1_local_export.py`）：
```
nC = 2, ℓ = l = 5, 2ℓ = 10, sF = sFactor(2) = (1²+2²)/2 = 2.5, sF−1 = 1.5
A_p = ord_p(q)·log p/(2ℓ)          （ord_p(q) = v_p(Δ)，乘法约化）
T_p = (sF−1)·A_p = 1.5·ord_p(q)·log p/10
Ind2_p = Σ_{j=1}^{2} frac(j²·ord_p(q)/(2ℓ))·log p   （j=1,2；frac=x−floor x）
H_p = 0（奇半稳定 e=1）；p=2: (1/2)log2；p=3: (2/3)log3；p=ℓ 跳过
M = arch + Σ(H_p + Ind2_p − T_p)
```
逐项复核：`Ind2` 的 j 范围/分式取法、`sF−1`、`2ℓ=10` 均与代码/paper-MODEL 定义一致；未发现**编码层**错误。

### 1.1 负样本精确数值（前 10 条，net = H+Ind2−T）

| N | curve | admissible | p | ord_p(q) | frac(j=1),frac(j=2) | H_p | Ind2_p | T_p | net |
|---|---|---|---|---|---|---|---|---|---|
| 1870 | 1870h2 | false（5\|20） | 11 | 20 | 0,0 | 0 | 0 | 7.193686 | −7.193686 |
| 858 | 858k2 | **true** | 13 | 21 | 0.1,0.4 | 0 | 1.282475 | 8.079590 | −6.797116 |
| 1586 | 1586d2 | false（5\|10） | 61 | 10 | 0,0 | 0 | 0 | 6.166311 | −6.166311 |
| 1974 | 1974j4 | false（5\|20） | 7 | 20 | 0,0 | 0 | 0 | 5.837730 | −5.837730 |
| 1938 | 1938j2 | false（5\|15） | 19 | 15 | 0.5,0 | 0 | 1.472219 | 6.624988 | −5.152768 |
| 806 | 806f2 | false（5\|10） | 31 | 10 | 0,0 | 0 | 0 | 5.150981 | −5.150981 |
| 1147 | 1147b2 | false（5\|10） | 31 | 10 | 0,0 | 0 | 0 | 5.150981 | −5.150981 |
| 870 | 870i4 | false（5\|10） | 29 | 10 | 0,0 | 0 | 0 | 5.050944 | −5.050944 |
| 1479 | 1479f2 | false（5\|10） | 29 | 10 | 0,0 | 0 | 0 | 5.050944 | −5.050944 |
| 570 | 570l3 | false（5\|10） | 19 | 10 | 0,0 | 0 | 0 | 4.416658 | −4.416658 |

**admissible 负样本**（e=1 模型下）：
- `182a3`, p=7, ord=12：frac 0.2+0.8=1.0，Ind2=1.945910，T=1.8·log7=3.502638，net=−1.556728；
- `102b6`, p=17, ord=8：frac 0.8+0.2=1.0，Ind2=2.833213，T=1.2·log17=3.399856，net=−0.566643；
- `154b4`, p=11, ord=8：Ind2=2.397895，T=1.2·log11=2.877474，net=−0.479579；
- `858k2`, p=13, ord=21：frac 0.1+0.4=0.5，Ind2=1.282475，T=3.15·log13=8.079590，net=−6.797116。

## 2. 是否模型 artefact（变体测试）

对 4154 条（2604 admissible）逐项重算，测试下列模型变体（只改公式，不改数据）：

| 变体 | 负项数（全） | 负项（admissible） | 说明 |
|---|---|---|---|
| **current**（e=1, T 不除 nC, arch=0.285） | **340**（336 curves） | **87**（87 curves） | 基线 |
| `ord_p(q) ↔ 1`（把 v_p(Δ) 改成 1） | **0** | **0** | lead 假设；但**与数据矛盾**：11a1/858k2 等 I_n 的 v_p(Δ)=5/21，q 的阶就是 n；不可作为论文修正 |
| `H_p` 用 e=ℓ=5（H=(1−1/5)logp） | 51（51） | **9** | lana `hullPacket_tame` 的 e 是真实分歧指数；e=1 是 A917 的建模简化，可能是 artefact |
| `T_p` 除 nC=2 | 51（51） | 9 | C-MARGIN-FIX 指出的 1/nC 归一化缺口；但 paper T=(sF−1)A 不显然带 1/nC |
| e=5 且 T/nC | **3**（3） | **1** | 组合变体 |
| H,Ind 都除 nC | 1636（1467） | 973（870） | 更差；说明不是 H/Ind 平均 |
| p=2,3 H 置 0 | 340 | 87 | 不改变负项（负项都在奇 p） |
| arch_paper=log(√2π) 替代 0.285 | 340 | 87 | 只改全局 M，不改变逐位符号 |

### 2.1 关键事实
1. **253/340（74.4%）负项落在 inadmissible 曲线**：多数 `ord_p(q)` 是 10/15/20 等（ℓ=5 整除，或 p=ℓ），按 C1 的 admissibility 本就应剔除；它们不是样本内的真实符号。
2. **87 个 admissible 负项**集中在 `ord_p(q)=8,11,12,13,14,16,21…`；此时 `Ind2_p`（frac 和）有界，而 `T_p` 随 ord 线性增长，故在 e=1、H=0 的模型下必为负。
3. **e=ℓ 修正**把 admissible 负项从 87 降到 9（全样本 340→51）；**T/nC** 同样降到 9；两者合起来只余 **1** 个 admissible 负项。
4. `arch`、`p=2,3`、`H/Ind 除 nC` 均不能解释负项；`ord=1` 可以清零但与半稳定 I_n 数据矛盾，属错误“修正”。

## 3. 判定：artefact 还是真实

**结论：负项主要是 model artefact（尤其 inadmissible 与 e=1/H=0、T 的 nC 归一化），但不能全部归为 artefact；在合理修正后仍余 9（e=5）或 1（e=5+T/nC）个 admissible 负项。**

支持 artefact 的证据：
- 340 项中 253 项在 inadmissible 曲线（ℓ|ord 或 p=ℓ），按 C1 规则应剔除；
- `e=1` 的 H=0 是 A917 的建模简化；lana `hullPacket_tame` 的 e 是分歧指数，e=ℓ 修正后负项减少 85%；
- C-MARGIN-FIX 已登记计算器缺 `1/nC`；T/nC 修正同样减少负项；
- `arch` 是 C0 placeholder（0.285 vs paper 1.4913），是已知模型缺口；
- `ord=1` 的“修正”会清零但违背 I_n 数据（11a1 v_p(Δ)=5，858k2=21），故不能采用。

不能完全归为 artefact 的证据：
- 9 个 admissible 负项（e=5）或 1 个（e=5+T/nC）在现有修正后仍为负；
- 这些对应高 `ord_p(q)`（11–21）的 I_n 曲线（p=7,13,19），需要精确 `H_p/orderVol/different` 或 `gap/Ind2` 的非模型项才能判定；
- 当前 c1 是 MODEL-PAPER，不是 lana 精确计算；9 项可能是真实模型 deficit，也可能是剩余模型 artefact。

## 4. 补偿来源候选 & M 的完整展开缺口

paper M 的完整展开（`C-MARGIN-FIX.md`）：
```
M = V + gap − (sF−1)A
  = (1/nC) Σ_i [ Σ_{v finite} Σ_c w_c hullPacket_{i,v,c}
      + Σ_{v finite} Σ_c w_c ind2Term_{i,v,c} + arch_i ] − (sF−1)A
```
c1 模型只取：`arch_for_nC`、`H_p=(1−1/e)logp`（e=1 ⇒0）、`Ind2_p=frac 和`、`T_p`；**缺/近似**：

| 缺失/近似项 | 可能补偿方向 | 依据 |
|---|---|---|
| 精确 `hullPacket_finite` 的 `shellExcess + orderVol` | **正**（orderVol/different 项） | `VcI.lean:806`；c1 只取 tame `(1−1/e)` |
| 精确 e（Kt/局部域分歧指数） | **正**（e>1 时 H>0） | `VcI.lean:844`；e=ℓ candidate |
| `1/nC` 对 V/gap 的归一化 | 取决于位置 | `c1_batch.py` 缺 `1/nC`（C-MARGIN-FIX §3） |
| 精确 `archDefect`（C0）与 capsule arch | **正/全局** | `arch_for_nC=0.285` vs `log(√2π)=1.4913` |
| `gap = rhs+sF A−V` 的 `ind2Term` 精确值 | 可正/负 | c1 的 Ind2 是 C0 tentative，不是 lana 精确 `ind2Term` |
| torsion `r/n` | 可正/负（c1 M 未含） | C1 公式的已知缺失项 |
| 精确 `componentVol`/`differentExponent` | **正**（不同项） | `hullPacket_finite/tame` 的 orderVol |

**最可能解释**：c1 的 `H_p=0`（e=1）与 `Ind2` 的模型形式使 `T_p` 在高 ord I_n 处无正项抵消；精确 `orderVol`/different 或 e>1 的 hull 项可补足大部分；剩余 9（或1）项需精确局部项才能定论。

## 5. 修正后的 CSV

已生成 **`coord/c1_local_terms_corrected.csv`**（16,701 行；MODEL-CORRECTED-CANDIDATE，仅候选）：
- `H_current`, `H_e5`（e=ℓ 修正）、`T_current`, `T_div_nC`（1/nC diagnostic）、`Ind2`、`admissible`；
- `net_current`, `net_e5`, `net_e5_TdivnC`；
- 负项统计：current 340（admissible 87）→ e5 51（9）→ e5+T/nC 3（1）。

**注意**：这不是 paper-verified 修正；`e=ℓ` 与 `T/nC` 都是模型假设，必须与 lana 精确 `hullPacket`/paper 公式逐条核对后才能采用。`ord=1` 变体**不采用**（与 I_n 数据矛盾）。

## 6. 结论（给 lead）

1. **不是编码 bug**：样本逐项数值与公式完全一致；
2. **主要是模型 artefact**：74.4% 负项在 inadmissible 曲线；e=1/H=0 与缺 1/nC 是已知建模简化；e=5 或 T/nC 修正后 admissible 负项 87→9；
3. **不能全归为 artefact**：e5+T/nC 后仍有 1 个 admissible 负项（4 曲线? 实际1曲线），且 9 项在 e5 后保留；这些需要精确 `orderVol`/different、精确 e、gap/Ind2、torsion、arch C0 才能判定；
4. 若要把 M 完整化，优先补：精确 `hullPacket_finite` 的 `orderVol`/different、精确 e、`1/nC` 归一化、精确 arch/ind2Term/torsion；
5. 在补齐前，LP 的负项不能作为“真实不等式反例”，也不能作为“已验证非负分解”；clean 子集（3818）的 exact 分解仍成立。