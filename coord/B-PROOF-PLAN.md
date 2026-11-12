# B-PROOF-PLAN — 证书族的证明级构造计划

**Status: DESIGN/THEORY**（非数值；无 Lean 代码）。日期：2026-11-12；qpilot（A987）。
**目标**：把 B 线的“数值证书搜索”转成 proof-grade 计划：证书引理的可证形式、统一上界需要什么结构、外部文献可引什么、需要自证什么。

## 1. 设置与目标

固定平方自由导子 `N` 的权 2 新形式 `f`（对应半稳定椭圆曲线 E/Q），`S₂(Γ₀(N),ℤ)` 为整系数权 2 尖形式格，`T = ℤ[T_n]` 为 Hecke 代数，`m_E = deg φ` 为模次数，`r_f` 为**同余数**（congruence number；`f` 与其它整系数形式的同余模数，见 Agashe–Ribet–Stein 定义 2.8）。

已知（外部定理，class-B）：
- **ARS 2005, Theorem 2.10**：`m_E | r_E`；且若 `ord_p(N) ≤ 1`，则 `ord_p(r_E) = ord_p(m_E)`。平方自由 N（半稳定）时所有 `ord_p(N)=1`，故 `m_E = r_E`。
- **Frey–Mai-Murty**：模次数的适当渐近上界等价于 abc（Agashe–Ribet–Stein 引 [Fre97, p.544], [Mur99, p.180]）。

B 线要证的目标（弱 ABC 的数值前提）：
> 存在绝对常数 `C`，使所有平方自由半稳定 E/Q 的 `r_f = m_E ≤ N^C`。
强 ABC 需要 `C = 2+ε`（B 线 B.2）；弱 ABC 需要任意固定 C。

## 2. 证书引理的可证形式（纯线性代数）

设 `L = S₂(Γ₀(N),ℤ)`，`V = L⊗ℚ`；设 `P ∈ ℤ[T_p]` 为 Hecke 多项式（允许有限个 p、任意整数系数）。记 `P(g)` 为 P 在正规化特征形式 g 上的特征值（若 g 非有理，按系数域嵌入作用；P 为整系数时为其迹/值，见下）。

**引理 C（Certificate Lemma，可证，纯线性代数）**
```
若 P(g) = 0 对所有与 f 不同的整系数特征形式 g（含同层其它新形式与所有 oldforms），
且 P(f) ≠ 0，则 r_f | P(f)。
```
证明思路（可 Lean 化）：令 `L_f = L ∩ ℚ·f`，取 f 的正交补在 L 中的整格 `L^⊥`；P 在 L 上作用，`P(L^⊥)=0`，`P(L) ⊆ L_f`；在同余数/理想定义下，`[L : L_f ⊕ L^⊥] = r_f`，故 `r_f | P(f)`。

关键：**引理 C 只给整除性，不给上界**。要从它得到 `r_f ≤ N^C`，必须构造一个 P 使 `|P(f)| ≤ N^C`（并且 P 确实杀掉所有其它特征形式）。

**定义（最小证书值）**：
```
m_f := min { |P(f)| : P ∈ ℤ[T_p], P(g)=0 for all g≠f, P(f)≠0 }
```
（若集合空，m_f=∞；P 可取常数 1 当且仅当没有其它形式。）由引理 C，`r_f | m_f`，所以 **`m_f ≤ N^C ⇒ r_f ≤ N^C`**。

## 3. 统一上界需要什么结构性的 P

### 3.1 等价/障碍命题（可证，说明问题核心）

**命题 O1（大素数同余障碍）**：若存在整数 `M` 与整系数特征形式 `g≠f` 使 `f ≡ g (mod M)`（逐 Fourier 系数），则对任何整系数 P 满足 `P(g)=0`，有 `P(f) ≡ 0 (mod M)`，因此 `m_f ≥ M` 且 `r_f ≥ M`。
**证明**：P 的系数是整数、Hecke 算子在同余下作用；`f≡g mod M ⇒ P(f)≡P(g)=0 mod M`；P(f) 是 `r_f` 的倍数（引理 C），故 M | P(f)。
**推论 O1'**：若存在一条曲线序列使同余数 `r_f` 超多项式增长，则不存在统一 `m_f ≤ N^C` 的 P 族；B 线目标即失效。

**命题 O2（引理 C 的反向充分条件，理想情形）**：若 `r_f` 恰为集合 `{P(f): P kills others}` 的理想生成元，则 `m_f = r_f`；此时找 P 与算 r_f 是同一问题。
（在整 Hecke 模/对偶格上这通常成立；但需要精确的整结构/对偶定理，独立于 abc。）

### 3.2 构造 P 的候选结构

**(S1) 特征多项式消去（univariate）**：
对素数 p，令 `P_p(T_p)=∏_{g≠f} minpoly(a_p(g))`；它杀掉所有 g。`P_p(f)=∏ (a_p(f)-a_p(g))`。
要 `≤N^C`，需要对全部 g 的 `|a_p(f)-a_p(g)|` 的**下界/分离**；Deligne 只给 `|a_p|≤2√p` 的上界，**没有统一下界**（同余可任意小）⇒ 这是核心困难，不是线性代数。
**(S2) 分步/局部化**：`P=P₂∘P₁`。`P₁` 用旧形式/小素数先杀掉大部分 g（oldforms），`P₂` 在剩余局部化 Hecke 代数上处理；每步用 S1。复杂度（support/degree/max prime）相加；需要控制每一步的“同余损失”。
**(S3) 整 Hecke 代数/SNF**：取 `T` 在 `L` 上的整矩阵，P 对应一个整矩阵；`m_f` 是某个整数矩阵的 SNF 最大不变因子/核上线性泛函 gcd。要证 `m_f ≤ N^C`，等价于给 **Hecke 矩阵的 SNF 不变因子** 的多项式界；这可用模符号/整模型几何（Arakelov、Manin 常数）尝试，但无现成定理。
**(S4) 模符号/周期**：`P(f)` 可写成 `∫_γ P·f` 的周期比；用 `X₀(N)` 的整模型/双曲度量、Abbes–Ullmo 型度量比较给上界；需要把 `|P(f)|` 与几何量（体积、注入半径、Manin 常数）联系，可能得到指数级界，未必到 N^C。
**(S5) 模形式/特征值分离（解析数论）**：用 Hecke 算子联合特征值的**有效分离**（Rankin–Selberg L 函数、zero-free region、effective multiplicity one）。目前文献给上下界多为指数/大常数，且 GRH 条件；无统一 N^C。

### 3.3 候选构造定理（精确陈述；目前均未证）

**Conjecture ECC(C,k)（Explicit Certificate Conjecture）**：
```
存在绝对常数 C>0 和 k>0，使得对每个平方自由半稳定 E/Q（导子 N）、对应新形式 f，
存在整系数 Hecke 多项式 P（只用 p ≤ (log N)^k 的 T_p，support ≤ k，degree ≤ k），
满足 P(g)=0 对所有 g≠f，且 |P(f)| ≤ N^C。
```
等价地（由引理 C 与 O1）：`m_f ≤ N^C`，从而 `r_f = m_E ≤ N^C`。

**特化**：
- `C=2+ε`（任意 ε>0，k 可依赖 ε）⇒ 由 B 线 B.2 的 Frey 曲线构造给 **完整 ABC**（前提：`m_E=r_E` 的 ARS 等式；平方自由半稳定满足）。
- `C` 固定但 >2 ⇒ **弱 ABC**（固定指数）。
- `k` 有限（至多 `(log N)^k` 个素数）是“显式/可构造”的关键；仅存在无限 support 的 P 不够。

**反例条件（何时 ECC 必假）**：若存在一族曲线使 `r_f > N^C` 对任意 C（即 `log r_f/log N→∞`），则由引理 C 任何 P 的 `|P(f)|≥r_f>N^C`，ECC(C,k) 全部失败。因此 ECC 是**关于同余数/模次数增长的猜想**，不是纯形式构造。

## 4. 文献核查（可引的外部定理 vs 无现成定理）

| 文献 | 可引内容 | 是否给显式证书/上界 |
|---|---|---|
| Agashe–Ribet–Stein, *The Manin constant, congruence primes, and the modular degree* (2005) | 定义 2.8 同余数 `r_E`；**Theorem 2.10**: `m_E | r_E`，且 `ord_p(N)≤1` 时 `ord_p(r_E)=ord_p(m_E)`；Conjecture 2.11 `ord_p(r_E/m_E)≤½ord_p(N)` | **无**显式证书 P 的构造；只给整除/局部等式与猜想 |
| Ribet, *Modular degrees and congruence numbers* (2010, socal slides) | 同余理想 `I_c⊆I_d`；`N` 素时 `I_c=I_d`；ARS 局部（平方因子外）等式；`d|c` | **无**统一上界/证书 |
| Frey 1997 (p.544), Mai-Murty 1999 (p.180)（经 ARS 转引） | 模次数的适当渐近上界**等价于 abc** | 这是**等价性观察**，恰说明求 `N^C` 界是 abc 级难题；无显式 P |
| Pasten, *Shimura curves and the abc conjecture* (arXiv:1705.09251, 2018) | 无条件 `log δ_{1,N} < (1/24+ε)N logN`（Thm 7.2）；Conjecture 3.2 `log δ_{1,N}≪logN`（Frey 模次数猜想）；无 certificate | **无**显式证书；多项式界是猜想 |
| Watkins 系列（rank/2-adic valuation、特殊情形） | `rank(E) ≤ v_2(m_E)` 的分情形定理 | 无上界/certificate |
| 本仓库 B1-EXACT/EXACT2 数值 | 完整约束 SNF 的 `min_abs`、`r_f^opt | min_abs` 100% 数值验证 | 只是数值证据，不是定理 |

**检索结论**：在已检索文献（ARS、Ribet、Frey/Mai-Murty、Pasten、Watkins）中**没有**“存在显式整系数 Hecke 证书 P，使 |P(f)|≤N^C”的现成定理。该命题与 Frey 模次数猜想/abc 同级；文献只给整除性（引理 C 的输入）、局部等式/猜想与指数级无条件界。

## 5. 需要自证/形式化的引理清单

### 5.1 可自证（纯线性代数/整数格）
1. **引理 C（certificate_lemma）**：`r_f | P(f)`（在“r_f 为同余数/理想指数”定义下）。
2. **定义/引理 m_f**：`m_f` 为整数核上线性泛函 gcd；`r_f | m_f`；`m_f` 计算为 SNF 不变量。
3. **O1（同余障碍）** 与 **O1'**（超多项式增长 ⇒ ECC 失败）。
4. **O2**：在整 Hecke 模/对偶格上 `m_f` 与 `r_f` 的关系（需精确整结构假设；可形式化为条件引理）。
5. **分步/局部化引理**：`P=P₂P₁` 杀灭集合的复合、`|P(f)|` 的乘法上界与 support/degree 相加。

### 5.2 需要外部输入（class-B，登记为假设，不证）
1. **ARS Theorem 2.10**：平方自由半稳定时 `m_E=r_E`（`ord_p(N)≤1` 时局部相等；由 `m_E|r_E` 和局部等式得全局相等）。
2. **Frey–Mai-Murty 等价性**：模次数多项式界 ⇒ weak ABC；`N^{2+ε}` ⇒ ABC。
3. **Deligne 界** `|a_p|≤2√p`（用于 S1 上界；无分离下界）。
4. **（若走 S5）** 有效 multiplicity one/Rankin–Selberg L 函数 zero-free region/GRH 条件（文献不统一）。

### 5.3 需要的新数学（不可从现有文献直接引）
- **ECC(C,k)**（主猜想）：显式整系数证书的 `|P(f)|≤N^C`；
- **特征值有效分离**：对 S1/S2 的 `|a_p(f)-a_p(g)|` 可证下界（这直接对应同余数控制）；
- **SNF/整 Hecke 模的多项式界**（S3）或 **周期/几何界**（S4）给出 `m_f` 上界；
- 任何这些都会直接推出弱 ABC；当前均未知。

## 6. 结论与建议

1. **引理 C 可以独立证明并 Lean 化**（纯线性代数；建议作为下一步正式任务）。
2. 从引理 C 到 `r_f≤N^C` 的缺口**不是接口/写法**，而是 **ECC 猜想**；它等价于模次数/同余数的多项式界，因而至少与弱 ABC 同级；文献中无现成显式证书存在定理。
3. B 线当前不应进入 B2（成族构造/证明）除非先接受 ECC 为显式假设（class-B）；数值 EXACT2/EXACT3 只提供 `m_f` 的有限样本与增长趋势，不能替代证明。
4. 可执行的 proof-grade 小目标（优先级）：
   - (P1) 形式化引理 C（抽象 Hecke 格/同余数接口）；
   - (P2) 形式化 O1/O1'（同余障碍）与 m_f 的 SNF 定义；
   - (P3) 把 ARS/Frey–Mai-Murty 登记为 class-B 接口，陈述 ECC(C,k) 及其推论（条件定理）；
   - (P4) 任何对 ECC 的尝试都需先给出 S1–S5 之一的实质数学进展，否则不启动。

**一句话**：证书引理可证；统一上界即 ECC，属于模次数/同余数的 abc 级猜想，文献无显式证书定理；B 线只能作为条件性路线，不能 proof-grade 闭合。