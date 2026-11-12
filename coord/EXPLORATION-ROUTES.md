# EXPLORATION-ROUTES — 三条探索路线的指导书

日期：2026-11-12（v2，交接版）。作者：单线程审阅会话（未编译、未实验）。
读者：负责写代码和证明的执行 agent。本文只给宏观设计、接口、顺序和防跑偏规则，不给实现。

收录标准：结局现在判断不了、必须跑到底才知道。已经看得到停点的方向在 `ABC-ROUTES-SCREEN.md`，不要重走。

## 0. 所有路线共用的约定

### 0.1 目标（不许改写）

- 仓库内目标：对所有真实初始 Θ-数据 D，`(sF−1)·A ≤ V + gap`，即 lana 的 `Corollary312Variant (concreteVariantData D)`。
- 最终目标：ABC（`LeanFormal/IUT/ABCBridge/Statement.lean`）。
- 路线 A、B 不经过 IUT，直接指向 ABC；路线 C 服务于仓库内目标，并为 A、B 供数据。

### 0.2 试金石（每个新主张先过这一关）

全称不等式会推出：`rad(3^k − 1) ≥ 3^{(1/2+δ)k}`，进而推出以 3 为底的非 Wieferich 素数无穷多（公开未解决）。
所以每条主张都要回答："`3^k − 1` 不是近似完全幂"这条信息从哪一步进来。答不出就是换说法，停。

### 0.3 防跑偏规则

1. **不换目标。** 不许把目标换成等价命题后报告"完成"；等价关系只能登记为等价。
2. **数值不是定理。** 每张表标注"数值/模型"或"已证"。零违例不算证明。
3. **整性要证，不能靠观察。** 凡是用到"系数是整数""分母只含某些素数"的地方，必须有证明或文献出处。
4. **真实数据。** 局部数据取自真实曲线和真实挠域；坏位剩余特征为奇；不用 `e=1` 的玩具样例。
5. **外部定理显式登记。** 模性、迹公式、holonomy 界等在 Lean 里只能是显式假设，不进最终公理闭包。
6. **每个阶段只做到判定点。** 到判定点先写结果，再决定是否继续；不自行扩大范围。
7. **负结果照实写。** 没有信号就写"没有信号"，不包装成进展。

### 0.4 每个阶段的交付格式

`coord/EXPLORATION-<路线>-<阶段>.md`，固定四节：做了什么、数据表、与判定条件的对照、下一步或停止。

---

## 路线 A：算术 holonomy 界

### A.1 一句话

用"幂级数系数的整性 + 无穷位的共形半径"得到不等式的那个定理（Calegari–Dimitrov–Tang），看它能不能界 abc 点的高度。

### A.2 引擎（我记得的形状，细节以原文为准）

- 设 `φ` 是单位圆盘到 ℂ 的全纯映射，`φ(0)=0`，`|φ′(0)| > 1`。
- 设 `f₁,…,f_m ∈ ℤ[[x]]` 在 ℚ(x) 上线性无关、holonomic，且每个 `f_i∘φ` 在圆盘上亚纯。
- 则 `m ≤ (与 φ 的增长有关的积分) / log|φ′(0)|`。
- 后续工作把系数放宽到分母受控的类型，代价是分母里多一项。

### A.3 为什么可能咬得住 abc

- 定理的结构是"各位收敛半径之积大于 1 时，函数个数受限"。
- 对三元组 `(a,b,c)`，自然出现的函数在 `p | abc` 处的 p 进半径由 `v_p` 决定；无穷位可以用共形半径代替朴素半径，这是增益来源。
- 朴素坐标下乘积远小于 1。要靠覆盖把坏素数处的半径拉回接近 1，这一步对应"高度换成根式"。
- 覆盖有代价（分歧、分母类型变坏）。增益和代价谁大，现在判断不了。

### A.4 阶段

**A0 抄准定理（必须先做）。**
- 取得原文（无界分母猜想一文及其后续）中 holonomy 界的精确陈述：假设、分母类型、上界公式。
- 交付：定理陈述的逐字转述 + 一页"哪些量需要计算"的清单。
- 判定：陈述拿不准就停在这里，不许凭印象往下做。

**A1 复现已知应用（校准管线）。**
- 用原文自己的例子（`x = λ/16` 的单值化）把上界数值算出来，与原文的数对上。
- 交付：共形半径、增长积分、上界三个数，与原文对照。
- 判定：对不上说明管线有错，修到对上为止。

**A2 设计与三元组相关的函数族。**
- 输入 `(a,b,c)` 和覆盖参数 m；输出一族候选级数，以及每个级数的三样东西：系数整性的证明思路、各坏素数处的 p 进半径、无穷位的共形半径。
- 候选来源（都要试，逐个登记）：
  - Legendre 周期 `Σ C(2n,n)² t^n` 在缩放坐标下的展开；
  - 以 `λ₀ = a/c` 为分支点的代数函数 `(1 − u·s)^{k/m}`；
  - 上面两类的乘积与导数；
  - 沿 Belyi 映射的拉回（仓库里已有 Belyi 对象）。
- 交付：函数族定义 + 每族的"半径之积"公式（符号形式，不是数值）。
- 判定：至少一族的半径之积在某个参数区间内大于 1；否则停。

**A3 第一个实验。**
- 族 `(1, 3^k−1, 3^k)`，k = 1…60；另取 20 个已知高质量 abc 三元组。
- 对每个三元组和每个可行的 m 列表：半径之积、定理上界、实际线性无关的函数个数。
- 判定（有戏）：得到形如 `log c ≤ C·log rad + cost(m)` 的不等式，且 `cost(m)` 不随 k 线性增长。
- 判定（停）：`cost(m)` 总是吃掉全部增益，或半径之积无法超过 1。

### A.5 防跑偏

- 半径之积必须在**同一个整体坐标**下算，不许各位各用各的坐标。
- 覆盖次数 m 引入的分歧和分母必须全额计入，不许忽略 `p | m` 的位。
- 不要把"函数是代数的"当作结论；代数函数本来就是代数的，要的是高度不等式。
- A3 之前不写 Lean。

### A.6 与仓库的接口

可复用：`Iut/Tripod/Height.lean`（Legendre 族、`legendreHeight`）、`tmp/sheaf/xif/paper/Mzk1*`（Belyi 映射）。
holonomy 界本身作为显式假设。

---

## 路线 B：总量可算、其余项非负

### B.1 一句话

把要界的量写成一个大和里的一项，其余项独立且非负，总和有公式；再想办法让权集中在我们这一项上。

### B.2 数学骨架（范围：ℚ 上半稳定曲线，即 Frey 曲线的情形）

- 模性（外部定理）：E 对应权 2、级 N 的有理新形式 f，模参数化次数记 `deg φ`。
- 高度与次数：`h_Fal(E) = ½·log(deg φ) − ½·log N + o(log N)`（Petersson 范数与对称平方 L-值的标准估计）。
- 所以：`deg φ ≤ N^{2+ε}` 给出完整的 ABC；`deg φ ≤ N^C`（C 固定）只给弱 ABC（某个固定指数）。**两者要分开登记。**
- 同余数 `r_f`：整格 `L = S₂(Γ₀(N), ℤ)` 中，`(L∩ℚf) ⊕ (L∩f^⊥)` 的指数。N 无平方因子时 `deg φ = r_f`（Agashe–Ribet–Stein）。
- **证书引理**（要先在 Lean 里证，纯线性代数）：若整系数 Hecke 多项式 P 在所有其它特征形式上为零、在 f 上非零，则 `r_f` 整除 `P(f)`。
- 基线：取 P 为特征多项式的余因子，得 `log r_f ≪ N·log N`，这是已知量级。

### B.3 要探索的问题

有没有**成族的、有结构的**证书 P，使 `|P(f)| ≤ N^C` 能对所有曲线统一证明？

具体可调的自由度：
- 用哪些 Hecke 算子（只用 `p ≤ (log N)^k` 的够不够）；
- P 的次数；
- 是否允许分步：先用一个 P₁ 杀掉大部分形式，再对剩下的局部化代数用 P₂。

### B.4 阶段

**B0 基础对象。**
- 能对给定 N 计算：`S₂(Γ₀(N))` 的整基、`T_p` 的整矩阵、全部特征系、`r_f`、`deg φ`。优先接现成的计算库，不要重造。
- 交付：对导子 ≤ 500 的全部半稳定曲线，`r_f` 与数据库中的 `deg φ` 一致的核对表。

**B1 最优证书的形状。**
- 对导子 ≤ 10⁴ 的全部半稳定曲线，求使 `|P(f)| = r_f` 的证书，并在"支撑最小""次数最小"两种意义下各求一个。
- 记录：用到的最大素数、次数、系数大小、f 与每个其它形式的同余模数。
- 交付：这些量对 N 的散点和拟合。
- 判定（有戏）：最大素数和次数随 N 至多按 `(log N)^k` 增长，且出现不依赖具体曲线的构造规律。
- 判定（停）：最优证书的复杂度随 N 多项式增长且无规律。

**B2 成族构造（仅当 B1 有戏）。**
- 把 B1 的规律写成显式构造 `P_N,f`，对全部样本验证 `r_f | P(f)` 且 `|P(f)| ≤ N^C`。
- 然后才尝试证明。证明里需要的新引理单独列出，逐条过试金石。

### B.5 防跑偏

- 迹公式看到的是 L² 归一化，`deg φ` 是整归一化。任何只用 L² 量的论证都界不住 `deg φ`，不要往那个方向花时间。
- "f 与其它形式很少同余"是这条路线真正的内容，不要把它当作已知。
- 不要把基线 `N·log N` 的重证当成进展。
- 模性、`h` 与 `deg φ` 的关系、Agashe–Ribet–Stein 都是外部输入，登记为显式假设。

### B.6 与仓库的接口

仓库内没有模形式和 Hecke 代数。Lean 侧只需要：证书引理（可证）、外部假设的陈述、从次数界到 ABC 的条件定理。计算在 Lean 之外做。

---

## 路线 C：大规模精确计算 + 自动找可加项

### C.1 一句话

把余量 `M(D) = V + gap − (sF−1)·A` 对几十万条真实曲线精确算出来，让机器去找它和其它不变量之间的零违例关系。

### C.2 阶段

**C0 先补两条定理（计算器的依据）。**
- Ind2 项：`ind2Term = frac(j²·v_p(q)/(2ℓ))·log p`。这是我的推导，lana 标为 Open；先对照 `Iut/WallEquiv/Gap.lean` 的 `ind2Term`、`tensorAut` 定义证出来或否掉。
- `archDefect` 的精确值（lana 文件头给了公式的形状但未形式化）。
- 判定：两条都要有结论，计算器才能叫"精确"。

**C1 局部项计算器。**
- 输入：`ℚ` 上的半稳定曲线、可容许素数 ℓ、`V^bad` 的选择。
- 输出：每个有理位的 `T_v`（q 侧）、`H_v`（hull 侧）、Ind2 项，以及总余量 M。
- 各类位的算法依据：
  - tame 坏位：`(1 − 1/e)·log p`，e 为真实 ℓ-挠域的分歧指数（`hullPacket_tame`）；
  - 2、3、ℓ 及其它 wild 位：按 `logShellRadius` 的定义逐个算（`hullPacket_finite`）；
  - 无穷位：C0 的结果。
- 可容许性检查必须实现：`ℓ ∤ ord_v(q)`、Galois 像含 `SL₂(𝔽_ℓ)`、坏位为奇。不满足的 (曲线, ℓ) 不进样本。
- 交付：计算器 + 对 20 条手算曲线的核对。

**C2 不变量库。**
- 每条曲线：导子、判别式、`deg φ`、Tamagawa 数、挠群、Ш 的解析阶、实周期、同源类、`a_p`（p ≤ 10⁴）、每个坏素数的 `v_p(Δ)`。
- 小 ℓ 时加上挠域的判别式、类数、调节子（能算多少算多少）。

**C3 搜索。**
- 样本：数据库中导子 ≤ 5·10⁵ 的全部半稳定曲线；已知高质量 abc 三元组的 Frey 曲线；族 `(1, p^k−1, p^k)`。
- 模型：线性、对数线性、按坏素数个数或最大 `v_p` 分段。
- 只保留全样本零违例的候选关系 `M(D) ≥ −X(D)`。
- **预先剔除已知等价关系**：凡是能由 `h ≈ ½log(deg φ) − ½log N` 和 `12h ≈ log|Δ|` 推出的关系，一律标为"已知等价"，不算发现。

**C4 判定。**
- 有戏：剔除之后仍有零违例关系，且 `X` 有已知上界或能独立去证。把它写成猜想，过试金石，再立项证明。
- 停：只剩已知等价关系。

### C.3 防跑偏

- 余量在已知曲线上为正是预期之内的事（已知最大 Szpiro 比约 9，有限 ℓ 的常数留有余量），不要把"没找到反例"写成证据。
- 找到反例是重要结果：说明目标陈述在该 D 处为假，要立刻上报，不要调参数让它消失。
- 回归得到的系数不许手工凑整后当作定理。

### C.4 与仓库的接口

C0 的两条定理进 Lean。计算器和搜索在 Lean 之外；其输出作为 A3、B1 的输入数据。

---

## 总顺序

1. C0、C1（其它两条路线都要用）。
2. A0–A1 与 B0 并行。
3. A2–A3、B1、C2–C3 并行，各自跑到判定点。
4. 三条都停在"没有信号"时，把结果写回本文件末尾，结束探索。

---

## 探索结果写回（2026-11-12，执行轮次 A928）

按总顺序第 4 条，三条路线均已到达判定点，结果为 **全部 STOP / 无信号**。以下为写回摘要；详细四节文档见各指针。

### 路线 A（holonomy 界）——STOP，无 ABC 增益

| 阶段 | 判定 | 关键数据 | 文档 |
|---|---|---|---|
| A0 抄准定理 | PASS | Thm 2.0.1 / Cor 2.0.5 / Thm 5.1.4 γ_N 闭式 / Thm 6.0.1 | `coord/EXPLORATION-A-A0.md` |
| A1 校准 | PARTIAL-PASS | 共形半径 4/2/8/16/1 精确；γ₂=4.37687923045；N=2 `C_obs≤1.13`；§6 无显式常数；N=3–5 未校准 | `coord/EXPLORATION-A-A1.md`, `-A1b.md` |
| A2 候选族 | 设计通过 | F1–F4；F4 符号 𝓡=4（退化） | `coord/EXPLORATION-A-A2.md` |
| A3 首实验 | **STOP** | 80 样本全 STOP；𝓡=3；B≈5.44m；cost≈4.44m（线性） | `coord/EXPLORATION-A-A3.md` |
| A2′ rad 嵌入 | **STOP-NO-TOUCHSTONE** | Q2 答不出；有限乘积退化/无限乘积违反整性 | `coord/EXPLORATION-A-A2PRIME.md` |

结构性观察：`R_p>1 ⟺ ∃c>0, v_p(a_n) ≥ cn eventually`；仅整性只给 `R_p≥1`。A3 的 F4 在有限 p 上只有平凡半径 ⇒ 路线 A 的增益实际需要**模形式/同余输入（A∩B 交叉）**。A2″ 需新预登记，含 `R_p>1` 证书与 `cost(m)` 抵消判据。

### 路线 B（证书/deg φ）——B1/B1-FIX2 STOP，B2 不启；A980 SNF 进行中

| 阶段 | 判定 | 关键数据 | 文档 |
|---|---|---|---|
| B0 基础对象 | PASS | N≤30 半稳定 43 条；S₂ 整基/T_p 整矩阵/r_f/deg φ 全出；ARC 43/43 | `coord/EXPLORATION-B-B0.md` |
| B1 最优证书 | **STOP** | N≤500 共 941 条；deg φ=r_f 941/941；证书发现率 69%(N<100)→~0%(N≥200)；degree ~ N^1.47（多项式非对数幂）；无构造规律 | `coord/EXPLORATION-B-B1.md` |
| B1-FIX2 强族 N≤1000 | **STOP** | 2122 条；found 1938/2122=91.3%；C_obs max 24.014、median 1.923、slope 11.51；C>3 597/1938；`|P|≤N³` 1341/1938；F2 vs F1 仅 10/899 改善；B2 不启 | `coord/EXPLORATION-B-B1-FIX2.md` |
| A980 完整约束 SNF | **进行中** | 仅产出 `coord/b1_exact_snf_1000.csv`（68,441B，22:03:04）、`b1_exact_snf_500.csv`、`b1_exact_snf_bins.csv`；无最终判定 | `coord/EXPLORATION-B-B1-EXACT.md` |
| B2 成族构造 | 不启 | 依据 B1/B1-FIX2 停止 | — |

**B1-FIX2（qpilot A975）判定**：F2 强族（Q_p 列 + 多变量/degree≤3）没有消除增长；N≤1000 全量 C_obs max 24.014、median 1.923、slope 11.51、C>3 597/1938，预登记判据失败 ⇒ STOP；N≤2000 未完成；B2 不启。**A980** 的完整约束 SNF 仍在进行，只登记数据产物，不把 partial SNF 当结论。

Lean 侧：证书引理 rank 2 / rank 3 完整构造 green（`Mzk1BCertificateFullActual`, `Mzk1BCertificateGeneralActual`，仅 [propext]）；一般有限秩需 `Submodule.index`/Smith 标准形，已精确记录为 GAP。

### 路线 C（余量计算）——C 线收口；C3/C3b 代理 INVALID

| 阶段 | 判定 | 关键数据 | 文档 |
|---|---|---|---|
| C0 两条定理 | PARTIAL | `ind2Term` 算术侧与条件形式 T1/T2 green/trio；精确化依赖 lana `Gap.lean`/`LocalConstruct` oleans | `coord/EXPLORATION-C-C0.md` |
| C1 计算器 | PARTIAL / MODEL | paper-MODEL 余量；4154 条曲线 canonical CSV | `coord/EXPLORATION-C-C1.md` |
| C2 不变量库 | NUMERIC COMPLETE | 4154 条半稳定（N≤2000），字段 100%，Cremona 上限 9999 已记录 | `coord/EXPLORATION-C-C2.md` |
| C3 搜索 | **STOP（代理 INVALID）** | 只用了 M0 代理；真实 M=A−R 不可数值计算 | `coord/EXPLORATION-C-C3.md` |
| C3b 阶梯复测 | **STOP（代理 INVALID）** | M0/最大素因子阶梯不是 M=A−R；旧阶梯不保持 | `coord/EXPLORATION-C-C3b.md` |

关键负结果：坏素数阶梯在真实 MODEL 余量下不保持（admissible 子集 b=3/4 出现负值）；74 个负值中 70 个非 admissible；可容许性规则与 Frey 三元组冲突（坏位 2 恒存在，A3 样本 0/80 可容许）。**C 线收口（hull A971，`coord/C3M-FEASIBILITY.md`）**：C3 必须用 `M=A−R`；`R = |log Θ|` 来自 `rhs = vol.processionVol thetaHull`（抽象 `LogVolumeData` 字段），`globalThetaHullLogVolume` 需每 v 的 `I.sourceSetVolume`/实际 holomorphic hull 或 concrete C3 tensor Haar；当前无具体 l=5 `C3` 实例与 measure 计算 ⇒ **R 不可数值计算，M=A−R 无表**；`c1_margin_symbolic.csv` 只有 `A_from_T=T/1.5`、`M_symbolic=A−R`、`M_ss_symbolic=A−R−gap`（R/gap 无数值，不重用 M0）。缺口 5 条见文档：concrete C3、actual tensor Haar/sourceSetVolume、`RHSData.vol` 公式、具体 qPilot/I、C0 ind2Term 精确公式。

### 结论与下一步

- 三条路线全部到达停止判定点，**本轮探索未产生 ABC 证明**；所有主张均按 NUMERIC/MODEL/LITERATURE 标注，无数值冒充定理。
- 下一轮候选（按优先级）：
  1. **C0 精确化**：形成 lana `Gap.lean`/`LocalConstruct` 的精确依赖，再用精确余量复测 C3b 的 maxvp 负尾。
  2. **A2″ 新预登记**：把模形式/同余输入（`R_p>1` 的显式证书）与 `cost(m)` 抵消判据写死，再跑 A3″。
  3. **B1′ 新预登记**：高 support/多变量/分步证书族，明确复杂度判据。
  4. 回到 IUT 对象线：E1/E4 字典与 paper 链（`paperGap ↔ Paper312`、`ClassicalABC ⇒ ABC`）的剩余形式化。

（写回完成；本轮探索按总顺序第 4 条结束。）
### A932 补记（A2″/B1′/C0/E1-E4 最新）

- **A2″（显式 `R_p>1` 机制）——STOP**：机制 (a) 模形式/同余、机制 (b) theta/CM 都**不满足 H**：Hecke 递推给 `v_p(a_n)=O(log n)`，theta/CM 系数有界或 `O(n^{1/2+ε})`，均有 `v_p(a_n)/n→0`，故 `R_p=1` 而非 `>1`；且 **Q2 答不出**（`log c−log rad` 没有进入 `I_N`）。按 A2″ 预登记，H 不满足即 STOP，不进入 A3″。见 `coord/EXPLORATION-A-A2PRIME2.md`。
- **B1′ 小样本——门槛未过**：50 个样本中证书发现 **25/50 = 50%**（预登记要求总 ≥80%）；高半区 `100≤N<200` 为 **0/25**（要求 ≥60%）；degree≤2 单项式族无任何非平凡证书。按预登记判据，**不进 B1′ 全量、B2 不启**；`0/25` 是 prototype 非穷尽（未用分步/局部化/index 优化），但不是“已证明不存在”。见 `coord/EXPLORATION-B-B1PRIME.md`。
- **C0 精确化推导——完成（源级条件形式）**：`coord/C0-EXACT-DERIVATION.md` 给出 `ind2Term = frac(j² v_p(q)/(2ℓ))·log p` 与 `archDefect = log((2^{N−1})!)/2^N` 的源码级推导；两条均**不是已证定理**，核心缺口引理：`leastHull_thetaComponent_eq_pow_floor`、`leastHull_archLogShell_eq_smul_archIntegral`、一般集 `componentVol_units_smul`、`haar_archTensorCoord_eq_smul_lebesgue`、球/多圆盘体积、`archDefect_eq`。
- **E4 接口最新状态**：`tmp/sheaf/xif/paper/Mzk1E4DictionaryActual.lean`（src SHA `A851D007…`，olean 19:08:48）只有 `E4Dictionary` 定义、`E4Dictionary_iff`/`e4_inequality`/`e4_of_unconditional` 等条件消费者和 `E4Witness`；**没有构造 actual P/VolShell**，E4 仍是 GAP，不能把接口当字典。
- **E1 接口最新状态**：`Mzk1E1ConcreteActual.lean`（src SHA `0298633F…`，olean 19:09:52）证明 `q.order=0 ⇒ qSideContribution=0 ⇒ E1PaperScaledHull`，但 `l=5/{2}/{2,11}` 只是 **MODEL** 数据；actual `QPilotIdentificationActual` 仍未构造，`ActualOrderZeroIdentification`（存在性+order=0）未证；此前 `Mzk1E1ConcreteRealActual` 草案**未落盘**（文件当前不存在），不列入审计。E1 仍是条件接口。
- **`Mzk1OurFrameworkABCActual` 更新**：当前 src SHA `5AA68ED7…`（5,246B，19:39:09），olean 19:41:12（fresh）；已修复 A940/A941 残留定理与编译错误（`E1_of_qSide_zero` 不再 `unfold` 带参 def；`assumptionInterfaceRows` 改为 `String×String×String`）；`ourFramework_ABCConjecture` 条件于 `OurFrameworkAssumptions`，最终只消费 **E3**（`ClassicalABCNatShape`，等价 ABC）；E2 真实 `E2VolumeUpper` 由 `ourFramework_E2` 消费，E4 接 `E4Dictionary` 由 `ourFramework_E4` 消费；`E4_face5` 及其残留定理已移除（源码 `E4_face5|Face5ConstructionObligation` 引用数 0）；**不是 ABC 证明**。
- **`Mzk1C0TargetsActual`**：src SHA `2D1649F1…`，olean 18:56:28；T1/T1′/T2 条件算术已 green，但显式登记缺口 `TensorAutCommutationDefect`、`TensorMetricOrthogonality`、`componentVol_leastHull_tensorLogShell_eq`；C0 = PARTIAL。
- **A942 stage4 复审：PASS**（新 ABC pin `5AA68ED7…`，5,246B，olean fresh，EXIT=0，6 声明 trio，零 sorryAx；E4/E1/C0/B certificates 见 `coord/STAGE4-AUDIT-RESULT-A932.md`；E4 actual 字典仍 GAP）。`Mzk1E1ConcreteRealActual` 因未落盘不列入；队列 §9 已记 PASS。
- **A947 housekeeping 复审：PASS**：E4 `49F0501B…`、E1Concrete `5DBD8772…` 均为 doc-only delta，无新假设；`Mzk1QPilotLineLActual` `A1765858…`（olean 180,024B fresh，EXIT=0，3 声明 trio）为 parametric/interface，C1/C2 义务 OPEN、`lana-transitive`；FINAL-STATUS 资产表已补并标 PASS。登录 `STAGE4-AUDIT-RESULT §12` / `EVIDENCE-ISOLATION §14`。

### A970/A971 补记：路线 A 终结

- **A3 人工族降级（A970）**：`EXPLORATION-A-A3.md` 头部已限定：实验族 `p(x)=c x^N−a`、`x(t)=t`、`φ(z)=β(rz)` 是为满足 Thm 2.0.1 假设人工构造的，p 进半径只有平凡值（`R_p≥1`/多项式），不携带 `rad(abc)` 因子；因此其 STOP 只在该人工族内成立，不是对路线 A 一般机制的否定/肯定。
- **A2‴ STOP-NO-TOUCHSTONE（A970）**：`EXPLORATION-A-A2PRIME3.md` 按先判据设计，三种显式构造（p^{cn} 几何级数、阶乘清分母、rad 进 x(t)/抽象 r_n）全部失败；H 无法满足（Archimedean 全纯 + 整系数 + `v_p≥cn` 冲突），Q2 答不出 ⇒ STOP-NO-TOUCHSTONE，不进入 A3‴ 数值化。
- **结论：A 线终结**；若继续需先解决独立分析/算术构造问题；未伪造构造、未声称 abc 增益。

### A991 补记：8 lane 分解工作流

- 新增 `coord/DECOMP-MASTER-PLAN.md`：把分解目标 `M=V−(sF−1)A≥0` 的 8 步流程（R 展开→正项清单→配对候选→LP 搜索→循环审查→恒等式 Lean 化→watchdog 编译→审计）写成可执行清单，含每步 owner/产出/验收；8 lane 分工：mainline(S7)、hull(S1)、qpilot(S2/S3)、shehdd(S5/S6 支持)、abc(S4/S6)、stage4(S5/S8)、lattice(文档/状态/S1 支持)、stepxi(S1/S6 支持)。
- 当前状态：S1 部分（R 不可数值，`C3M-FEASIBILITY.md`）、S3 初稿（`DECOMP-PAIRING-CANDIDATES.md` C1–C6 未证）；S4–S8 未启动；只写文件，所有 Lean 编译交 watchdog。

### A1035 最新审计事实（写回）

- **lana variant 是未证假设**：`Cor312VariantHolds` 是 def，无 theorem/instance；`classicalABC_of_variant : Cor312VariantHolds → ClassicalABC` 是纯蕴含；无隐藏 qOrder/height 上界（`LANA-VARIANT-STATUS.md`）。
- **iv/lit + q-不稳定**：`concreteVariantData`/ABC 桥用 iv；paper IUT III 字面 lit、IUT IV Steps iv；A1027 模型 iv 不稳定（I_n qOrder=n；首个 admissible 负值 n=21，M=−1.369；n=50 M=−10.806），lit 稳定（`gap=sF·A`，variant ⇔ V≥−A；V≥0 GAP 未证）；见 `AUDIT-IV-LIT-QSTABILITY.md`。
- **qOrder 原始整数**：`orderNat`，无 mod 2ℓ/ℓ；只要求正性+`Nat.Coprime ℓ qOrder`；I_n 的 n 无界（`QORDER-NORMALIZATION.md`）。
- **分解现状**：恒等式 `M=logp·[(1−sF)x1+mean(frac)]+Kbar'` 与正项清单已建；frac 有界（<1）已确认，但负 qScale 的线性补偿未决；lit 读法下 variant 平凡（`DECOMP-ALGEBRAIC.md`、`DECOMP-PAIRING-CANDIDATES.md`、`decomp_feature_lp_results.json`）。
- **具体对象路径**：唯一闭 provider `tripodProviders` + x + ℓ≥7 + 显式 hP2/hP4/hP5/hcore ⇒ `thetaData`；ℓ=5 被排除；无无条件 `InitialThetaData`，可满足性 OPEN（`INITIALTHETADATA-CONCRETE-PATH.md`）。
- **移植管线**：lana_a 的 `Iut/Cor312` **7 文件**已移植，闭包 7/7、无 missing prerequisite，7 oleans 存在（脚本化；不手编）；见 `tmp/external/ported/lana_a/import_chain.md`。

### A1043 巡检补记（A1045 后）

- **S3137 L 载体 green（98s）**：`Mzk1S3137LChainActual`（src 4,939B/23:49:55；olean 147,880B @00:08:56 fresh）；**MDecomposition green（91s）**：`Mzk1MDecompositionActual`（src 5,306B/23:50:13；olean 244,848B @00:04:19 fresh）；**lana_a 7/7 green**：`tmp/external/ported/lana_a/Iut/Cor312` 7 文件 fresh oleans（23:22–23:24）。
- **N5**：paper Step (xi-d) determinant comparison；upper-bound 栈不能给下界 `rhs≥−A`；`hheight` 非 green；N5 仍 PARTIAL/OPEN（见 `N5-STATEMENT.md`、`N5-ASSEMBLY-INVENTORY.md`，A1045 已降 gate 为 PENDING-WATCHDOG）。
- **watchdog 修复**：graph rebuild skip 补丁、单实例、noise 清除；结果由 mainline 汇总；lane 不手工编译（`dag/watchdog/heartbeat.json`、`RUNTIME-MISMATCH.md`）。
- **Batch B**：闭包含 TG 744 节点，需分层最小闭包；不能整批当 gate 已闭。
