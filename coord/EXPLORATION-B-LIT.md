# EXPLORATION-B-LIT — 路线 B 外部输入文献检索（精读 arXiv:1705.09251 + Watkins）

**Status: LITERATURE**；日期：2026-11-12；qpilot（A930/A936）。本版用 **WSL curl 下载并 pypdf 抽取全文**（1705: 已读 88 页；1611: 已读全文）；degphi 下载超时/截断（见 E-table）。

## 1. 检索记录

- 工具：`web_search` / `web_fetch`；WSL `curl` 下载 PDF；Windows `pypdf` 抽取文本（`tmp/1705export.txt`、`tmp/1611.txt`）。
- 下载成功：**arXiv:1705.09251**（Pasten, Shimura curves and the abc conjecture, v4）、**arXiv:1611.05671**（Kazalicki–Kohen）。
- 下载失败/不完整：Watkins `degphi.pdf`（服务器 375378 bytes，多次只到 177576 due timeout）、`moddeg.pdf`（308924，只到 283976）；未用于精确陈述。
- 反爬：AMS、ScienceDirect、zbMATH、ADS、LMFDB 均 403/验证码。

## 2. arXiv:1705.09251 精确定理/陈述（全文核对）

作者：Héctor Pasten；标题 Shimura curves and the abc conjecture；v4 (5 Jul 2018)。以下编号均为论文编号。

### 2.1 经典关系与核心猜想
- 式 (1)：`h(E) ≤ ½ log deg φ + 9`（E/Q，φ:X0(N)→E 最优模参数化；h 为 Faltings 高度）。
- 式 (4)：`log Δ_E ≤ 12 h(E) + 16`。
- **Conjecture 3.2（模次数猜想，Frey）**：当 E 遍历 Q 上椭圆曲线，`log δ_{1,N}(E) ≪ log N_E`。**这是猜想，不是定理**；论文明确指出 Szpiro 由它推出。
- Remark 3.3：Frey 原版为 `log(δ_{1,N}/c_f²) ≪ log N_E`（Manin 常数 c_f）；论文的 Theorem 1.3/Corollary 10.2 在 additive reduction 限制在固定有限素数集时证明了两版本等价。

### 2.2 无条件上界（关键：指数而非多项式）
- **Theorem 7.2**：对任何 E/Q（导子 N）及 admissible factorization `N=DM`，
  `log δ_{D,M}(E) ≤ (1/(12·φ(D)M) + 7/(12·d(DM²))) · (log N + 4 log N log log N)`；
  渐近：`log δ_{D,M} < (1/24 + ε) φ(D)M log N`（N≫_ε 1，effective implicit constant）。
  **取 D=1,M=N**：`log δ_{1,N} < (1/24+ε) N log N`（无条件）。
- **Theorem 7.5**：对 E/Q，`h(E) ≤ (1/24)(N+7d(N²))(log N + 4 log N log log N) + 9`；
  `log|Δ_E| ≤ ½(N+7d(N²))(log N+4logNloglogN)+124`；
  渐近 `h(E) < (1/48+ε) N log N`、`log|Δ_E| < (1/4+ε) N log N`（N≫_ε 1）；
  GRH 下 `h(E)<(1/24+ε) N log log N`、`log|Δ_E|<(1/2+ε) N log log N`。
- **Theorem 1.9 / Corollary 7.8**：S 固定、E 在 S 外半稳定：`h(E) < (ε+1/48) φ(N) log N`（unconditional）；GRH 下 `(ε+1/24) φ(N) log log N`。

### 2.3 判别式/高度与模次数、Shimura 参数化
- **Theorem 1.7 (= Theorem 7.6)**：`log|Δ_E| < (6+ε) log δ_{D,M}(E)`，`h(E) < (1/2+ε) log δ_{D,M}(E)`（N≫_ε 1）。
- **Theorem 1.5**：`log(∏_{p|D} v_p(Δ_A)) = log δ_{1,N} − log δ_{D,M} + O(log D log log D)`（条件 (i) N squarefree 且 M 非素数；或 (ii) Frey-type…）。
- **Theorem 1.8**（Hecke eigenvalue congruences）：`δ_{D,M}` 整除 `∏_{[χ]≠[χ0]} η_{[χ0]}([χ])`。
### 2.4 其它明确陈述
- Theorem 1.3：Manin 常数在 additive reduction 限制于固定 S 时 `c_f ≤ M_S`。
- Theorem 1.4：Shimura 参数化分量群 cokernel 一致有界。
- Theorem 1.6：`h ∈ S_D^2(M)` 非零 ⇒ Petersson 范数 `≥ C_ε N^{-5/6-ε} M^{-1/2}`。
- Theorem 1.10：abc 三元的 `∏_{p|abc} v_p(abc) < K_ε rad(abc)^{8/3+ε}`；Theorem 1.11 等价 `d(abc) < K_ε rad(abc)^{8/3+ε}`。
- Theorem 1.12：半稳定 E/Q，`∏_{p|N_E} v_p(Δ_E) < K_ε N_E^{11/2+ε}`。
- Theorem 1.13：半稳定 E/Q，level-lowering 素数个数 `#L(E) < 6 log N_E log log N_E + c`。

### 2.5 全实域（totally real）
- **Theorem 1.17 (= Theorem 18.10)**：F totally real，E/F 半稳定、modular、bad reduction 素数个数与 [F:Q] 奇偶相反；Shimura 曲线 X→E 的 φ：
  `h(E) < ½ log(deg φ) + c_n(log N_E + log d_F)`；`(1/n)log|Δ_E| < 6 log(deg φ) + c_n(log N_E + log d_F)`。
- **Conjecture 18.11**：`log δ_E < κ log(d_F N)`（κ 只依赖 n）— **猜想**；Theorem 1.18 在假设此猜想下给 `h(E) ≤ c log(d_F N_E)`、`Δ_E ≤ (d_F N_E)^c`（real quadratic）。
- **Theorem 18.14**（无条件）：`log δ_E ≪_{F,ε} N_E^{1+ε}`，故 `h(E) ≪ N^{1+ε}`、`log Δ_E ≪ N^{1+ε}`。

## 3. 逐条判定：能否与 `h ≈ ½log deg φ − ½log N` 组合得 `deg φ ≤ N^C`？

### 3.1 关键方向错误
论文的式 (1) 是 `h(E) ≤ ½ log δ_{1,N} + 9`：**高度上界只给 δ 的下界**（`log δ ≥ 2h-18`），不能给 δ 的上界。B 线需要的 `h ≈ ½log δ − ½log N` 若作为**等式/渐近**使用，则 `log δ ≈ 2h + log N`；即便代入论文无条件高度上界 `h < (1/48+ε)N logN`，得到的是
`log δ ≪ N log N`（即 `δ ≤ exp(O(N logN))`），**不是** `δ ≤ N^C`。

### 3.2 直接上界（Theorem 7.2）
`log δ_{1,N} < (1/24+ε) N log N` ⇒ `δ_{1,N} ≤ exp((1/24+ε)N logN)`。这是**无条件可用**的上界，但它比任何 `N^C`（固定 C）都弱：`exp(N logN)` 远大于 `N^C`。
要得到 `δ ≤ N^C`，需要 `log δ ≪ log N`，这正是 **Conjecture 3.2（Frey 模次数猜想）**；论文明确未证。

### 3.3 条件性结果
- 若假设 **Conjecture 3.2**：`log δ ≪ log N` ⇒ 由 (1) `h ≪ log N`；结合 `log Δ ≤ 12h+16` 得 `Δ ≤ N^{12C+...}`，从而 **Szpiro（因此 ABC，经 Frey 曲线）**。这是论文的核心条件性结论；不是定理。
- 若假设 **Conjecture 18.11**（全实域 Shimura 类比）：Theorem 18.12/18.13 给 `h ≤ κ log(d_F N)`、`Δ ≤ (d_F N)^κ`（条件性）。
- 两者都是 **Conjecture**，不能作为 B 线的已证外部输入。

### 3.4 结论
**用 1705 的精确定理不能推出 `deg φ ≤ N^C`（C 固定）。** 可用的无条件结果是：
1. `log δ_{1,N} < (1/24+ε) N logN`（Theorem 7.2）— 指数上界；
2. `h(E) < (1/48+ε)N logN`（Theorem 7.5）— 指数高度界；
3. `log Δ < (6+ε)log δ_{D,M}`、`h < (1/2+ε)log δ_{D,M}`（Theorem 1.7）— 方向相反（高度/判别式受 δ 控制）；
4. 条件性：Conjecture 3.2 / 18.11 才给多项式/对数界。
所以 B 线的 `deg φ ≤ N^C` 必须登记为 **UNPROVEN 假设**（或等价地登记 Conjecture 3.2）；1705 只提供指数级上界。

## 4. Watkins 文献精核（arXiv:1611.05671 全文）

论文：M. Kazalicki, D. Kohen, *On a special case of Watkins' conjecture* (arXiv:1611.05671v1, 2016)。
- **Watkins 猜想**（原文引 [8, Conjecture 4.1]）：若 E/Q 的 rank 为 r，模次数 `m_E` 被 `2^r` 整除。即 `r ≤ v_2(m_E)`。
- **Theorem 1.1**：若 E/Q 的模次数为奇数，则 `rank(E)=0`。
- **Theorem 1.3**：E/Q 素数导子且 `rank(E)>0`；若对所有 `j(E_i)∈F_p` 的 `v_E(e_i)` 为偶数，则 `4 | m_E`。
- 推论：若 E 素数导子、`disc(E)>0`、`rank(E)=2`，则验证 Watkins 猜想（原文摘要）。
- 条件限制：prime conductor / positive discriminant / rank=2 等特殊情形；**不是 deg φ 上界**，也不能给 B 线的 `N^C`。
- Watkins `degphi.pdf`：多次下载只到 177576/375378 bytes（超时），未提取全文；不用于精确陈述。

## 5. E-table（V 级别 / 消费者 / 状态）

V 级别约定：**V0** = 全文 PDF 抽取并逐条核对；**V1** = abstract/官方页面核对；**V2** = 二手摘要/metadata（未核全文）；**V3** = 不可得（反爬/超时/截断）。

| 项 | V 级别 | 消费者 | 状态/用途 |
|---|---|---|---|
| arXiv:1705.09251（Pasten） | **V0**（88 页 PDF 抽取） | B 线上界/条件性；B2 若启 | 精确定理见 §2；无条件上界为指数级；多项式界是 Conjecture 3.2 |
| arXiv:1611.05671（Kazalicki–Kohen） | **V0**（6 页全文） | B 线背景（Watkins 猜想） | Theorem 1.1/1.3；rank 整除性，非上界 |
| Watkins `degphi.pdf` | **V3**（下载截断） | — | 未使用；不引精确陈述 |
| Watkins `moddeg.pdf` | **V3**（截断） | — | 未使用 |
| ARS arXiv:0810.5176 | **V1**（abstract） | B0/B1（`deg φ=r_f`） | 等式/数值核对依据；非上界 |
| arXiv:math/0408126 | **V1**（abstract） | B 线下界参考 | 显式下界 |
| arXiv:2102.04185 / 2206.10008 / 2407.17680 / 2203.10932 | **V1**（abstract/HTML） | B 线背景 | Watkins 猜想/函数域/二次扭；非上界 |
| Papikian, degree conjecture function fields | **V2**（MPIM metadata；全文不可得） | B 线背景 | 函数域类比；Q 上 open |
| AMS / ScienceDirect / zbMATH / ADS | **V3** | — | 403/验证码，未取全文 |
| LMFDB | **V3** | B0/B1 | 反爬；未用（Sage/Cremona 替代） |
| Sage 10.9 + Cremona（WSL） | **green 环境** | B0/B1 | B0/B1 已用（941 条曲线/43 条） |
| Lean | — | — | 本文件不写 Lean |

## 6. 可用外部输入清单与结论

### 6.1 可用（无条件）
- **ARS**：squarefree N 下 `deg φ = r_f`（等式；B0/B1 数值核对 941/941）。
- **Pasten Theorem 7.2**：`log δ_{1,N} < (1/24+ε) N logN` ⇒ `deg φ ≤ exp(O(N logN))`。
- **Pasten Theorem 7.5**：`h(E) < (1/48+ε) N logN`、`log|Δ| < (1/4+ε) N logN`。
- **Theorem 1.7**：`h < (1/2+ε)log δ`、`log|Δ| < (6+ε)log δ`（反方向：δ 控制高度/判别式）。
- **Theorem 1.12**：`∏_{p|N} v_p(Δ) < K_ε N^{11/2+ε}`（弱 abc 型，但不给 deg φ）。

### 6.2 不可用为定理（必须登记为假设/猜想）
- **Conjecture 3.2（Frey 模次数猜想）**：`log δ_{1,N} ≪ log N`（等价/条件下等价于 height conjecture；论文明确未证）。这是 B 线 `deg φ ≤ N^C` 的精确来源；**没有已发表定理**。
- **Conjecture 18.11**：全实域 Shimura 类比 `log δ_E < κ log(d_F N)`（未证）。
### 6.3 结论
**1705 不能给 `deg φ ≤ N^C`**；它给出的无条件上界是**指数级** `log δ ≪ N logN`。要得到 B 线的多项式上界，必须**假设 Conjecture 3.2**（或等价的模次数猜想）；本检索没有找到已证版本。B 线因此仍是 **条件性路线**，外部输入应写成 `hdeg : log (deg φ_E) ≤ C log N_E`（UNPROVEN，class-B），不能写成定理。

### 主要来源
- [arXiv:1705.09251](https://arxiv.org/abs/1705.09251) / [HTML v4](https://arxiv.org/html/1705.09251v4)；全文 PDF 已下载 `tmp/1705export.pdf`（88 页）
- [arXiv:1611.05671](https://arxiv.org/abs/1611.05671)；全文 `tmp/1611.05671.pdf`
- [arXiv:0810.5176](https://arxiv.org/abs/0810.5176) (ARS)
- [arXiv:math/0408126](https://arxiv.org/abs/math/0408126) (explicit lower bounds)
- [arXiv:2102.04185](https://arxiv.org/abs/2102.04185), [2206.10008](https://arxiv.org/abs/2206.10008), [2407.17680](https://arxiv.org/abs/2407.17680), [2203.10932](https://ar5iv.labs.arxiv.org/html/2203.10932)
- [Papikian, Analogue of the degree conjecture over function fields](https://archive.mpim-bonn.mpg.de/id/eprint/2686/)