# C9：把真实 log 定义域扩展到 tame e<p−1 之外

任务 ID：task-146（C9-LOG-DOMAIN-EXTEND-20261025）；owner：logdescent；日期：2026-10-25。用户要求 C9 stage1 自然语言研究；本文件是唯一交付物。未写 Lean、未改 Project、未改其他 owner 文件、未改目标；未运行 Lean/Project/kernel/comparator/独立审查。

消费者/阶段：n8-c9-output-region-source-route，SHEAF stage1。目标保持为每份原文合格完整 C、固定 native q/BPS/gluing/目标列/normalization，排除整个最终输出族的 h_C<Q_C。下面只研究原 log-link 的真实定义域及其分支边界，不把局部模型、额外 log/exp 箭头或外 shell 当作实际输出。

复用与冻结：C9-TAME-LOG-DOMAIN-20261025.md（SHA256 23b3514b94972de511f1b17e23ab3da832ed5bc63e89daca3875adeb07961f06；EVIDENCE SHA256 1850b6aa5004fba40d9f406910d65a6939ddd53082ff740631863a6f2505475a）的源范围、III Def1.1/Prop1.2/Rmk1.1.1/Rmk1.2.2/Prop3.4-3.5/Thm3.11 读法、Kondo 单位/reciprocity/perfection 匹配、以及 C9-FIXED-GLUING-SWAP-20261025.md 的固定 gluing 共同末端运输。本文件只追加 e≥p−1 及其分支分析；原全局 P6 未被证明。

## 0. 记号与源对象

固定 p 为奇素数，K/Q_p 有限，绝对分歧指数 e，惯性指数 f，剩余域基数 q_res=p^f，d=[K:Q_p]=ef，极大理想 m=(π)，π 为 uniformizer，v_p(π)=1/e，O_K 为整数环。取 p 进绝对值 |·|_p 与 v_p。

原 log-link 的源定义按 IUT III Def1.1(i)：先取 O_K^× 上的 p 进 log，再经 Frobenius 同构到下一有限域的相应对象；不是任意代数闭包上的形式 log。Rmk1.1.1(i) 规定下一步 log-link 的输入必须为单位；Rmk1.2.2(i) 的 log-shell 是 p^{-1} 乘 log(O_K^×) 的构造。源有限 Galois invariants 与下一域的 invariants 由实际函子性连接。

tame 包的核心结论是：当 e<p−1 时 log(O_K^×)=m，I_K=p^{-1}m，第一次 log 像为非单位，故同一路径的 h≥2 次 log-link 定义域为空；Kummer 零路径的整数格为 O_K。下面逐项检查这些结论在 e≥p−1 时的真实变化。

## 1. p 进 log/exp 的一般收敛阈值

**标准事实（p 进 log 的收敛域）。** 对 x∈m，log(1+x)=∑_{k≥1}(-1)^{k+1}x^k/k，exp(x)=∑_{k≥0}x^k/k!。Legendre 公式给出 v_p(k!)≤(k−1)/(p−1)，从而对 x∈m^n（即 v_p(x)≥n/e）：

    v_p(x^k/k) ≥ k n/e − (k−1)/(p−1),
    v_p(x^k/k!) ≥ k n/e − (k−1)/(p−1).

若 n≥e/(p−1)，则 n/e≥1/(p−1)，故上式 ≥ n/e >0，两个级数都在 m^n 上一致收敛。若 n<e/(p−1)，取 k=p^t，v_p(k)=t，则被加项赋值 ≤ n p^t/e−t → −∞；对取到边界赋值的 x，log 级数不收敛。exp 用 k! 的同一上界得到同样阈值。

因此令

    n0 := ceil(e/(p−1)) = min{n∈Z_{≥1} | n/e ≥ 1/(p−1)}.

则 log 与 exp 在 1+m^{n0} 与 m^{n0} 之间互逆；这是对**所有** e 都成立的精确阈值。证明只用 Legendre 估计和 p 进级数收敛判别。标准参考：Neukirch, *Algebraic Number Theory*, GTM 322, Ch. II §5；Fesenko–Vostokov, *Local Fields and Their Extensions*, Ch. I；Serre, *Local Fields*, Ch. IV 的 p 进 log 构造。这里不引入任何额外的 log/exp。

三种情形：

1. e<p−1：n0=1；1+m=m 全在收敛域；tame 包的 log(O_K^×)=m 成立。
2. e=p−1（边界）：n0=ceil(1)=1；e=p−1 时 v_p(π)=1/(p−1)，上界仍给出 log 在 m 上收敛。因此 tame 结论可扩展为 **e≤p−1**，不仅是 e<p−1。这是本包第一个精确边界修正。
3. e>p−1：n0≥2；log 只在 1+m^{n0} 上由该幂级数定义，U^1/m^{n0} 中的主单位没有这个 p 进 log。

注：e=p 时 n0=ceil(p/(p−1))=2；e=2(p−1) 时 n0=2；e=p(p−1) 时 n0=p，等等。n0 随 e/(p−1) 增长，不是常数。

## 2. Teichmüller 根单位与真实 log 定义域

p 进单位分解（p 奇）：

    O_K^× ≅ μ_{q_res−1}(K) × U^1,
    U^1 = 1+m.

源 Teichmüller 根单位 ζ∈μ_{q_res−1} 的 log 取 0；这是源 log 的 Teichmüller 约定（IUT III Rmk1.1.1/1.2.2 的根单位处理；AbsTopIII Def5.4(iii)/Prop5.8 的 O^× 与 shell 重建）。

精确分两种口径，不能混写：

(a) **纯解析口径**：只用上述幂级数的收敛域 D_an=U^{n0}。此时 ζ 只有在 v_p(ζ−1)≥n0/e 时才落在 D_an；对 e>p−1，一般 Teichmüller 根不在幂级数收敛域内，不能直接说「解析 log(ζ)=0」。
(b) **源 Teichmüller 口径**：在 μ_{q_res−1} 上定义 log ζ=0，并把它与 U^{n0} 上的解析 log 合并为

    D_K := μ_{q_res−1}(K) · U^{n0} = μ_{q_res−1}(K) · (1+m^{n0}),
    log: D_K → m^{n0},  ker(log|D_K)=μ_{q_res−1}(K).

(b) 与 tame 包及 IUT 的 Teichmüller 处理一致；但它不是由同一个收敛幂级数在 ζ 上直接求和得到的。这是一个**源约定分支**，不是本包新加的可调用箭头。若原 C 的 log 定义只允许 (a)，则 Teichmüller 零点不是收敛域内的点；若原定义采用 (b)，则它们以零进入、不改变像。两种口径下 log 的非零像都是 m^{n0}，但定义域点集不同。

在 (b) 下：

    J_K := log(D_K) = m^{n0},
    I_K := p^{-1}J_K = m^{n0−e} = π^{n0−e}O_K.        (2.1)

对 e≤p−1，n0=1，得 J_K=m、I_K=p^{-1}m；tame 公式完全恢复。对 e>p−1，J_K 比 m 小 n0−1 级，I_K 比 p^{-1}m 小 n0−1 级：

    I_K^{actual} = m^{n0−1} · (p^{-1}m).               (2.2)

这里 p^{-1}m=m^{1−e}；n0−1≥1。以 m 的整数指数计，归一化 shell 的「损失」正是 n0−1。

对 O_K 归一化的 log-volume（用 [O_K:m^n]=q_res^n 和 d=ef）：

    logvol_O(m^n) = n f/e · log p = (n/e)·log p,
    logvol_O(I_K) = (n0−e)/e · log p.                  (2.3)

e>p−1 时该值比 tame 的 (1−e)/e log p 增加 (n0−1)/e log p（注意 frac exponent n0−e 可正可负；作为理想指数是 n0−e，volume 按理想指数线性）。这是精确的尺度变化，不是任意权重。

## 3. 第二次、第三次 log-link 的定义域

必须区分「同一路径的迭代」和「新的单位路径」：

**3.1 同一 log-image 路径。** 第一次 log 把单位送到 m^{n0}（非单位），后接 III Def1.1(i) 的实际 Frobenioid 同构仍把它送到下一有限域的非单位。Rmk1.1.1(i) 要求下一条 log-link 的输入是单位。故对同一路径：

    h=1: 像在 m^{n0}；
    h≥2: 定义域为空（对所有 e，包括 e>p−1）。

e>p−1 不会让第二次 log-link 重新有定义，因为 log 的像层仍是 m^{n0}，不是 O^×。p^{-1} 归一化 shell I_K=m^{n0−e} 也不是单位群；即使 I_K 含 1 或含某些单位，log-link 的输入是 O^×，不是 I_K 的任意元素。故 h≥2 的“空定义域”分支对 e 的扩展保持不变。

**3.2 独立单位路径。** 若源在下一域另给出一条以单位 u∈D_K 开始的路径，则那是一条新的第一次 log-link，而不是前一条 log-link 的第二次迭代；其像同样在 m^{n0}。这并不改变 3.1 的同一路径结论。源数据若只给出一条 Kummer 零路径和一条 log 路径，不能把新单位路径当成原路线的复合。

**3.3 1+log(u) 分支。** 因为 log u∈m^{n0}，1+log u∈U^{n0}，所以 log(1+log u) 作为解析函数有定义。但这个单位不是 III Def1.1(i) 的 log-link 产生的；把它插入会在源之外新增一条「1+」箭头。tame 包已拒绝把这种任意插入当作源允许的迭代。e>p−1 时它仍可能产生新的 additive 元素，但必须由原 C 的源箭头明确给出；本包不采用，不能用作增益。

**3.4 第三次及以后。** 同 3.1；除非源另有独立单位路径，否则同一路径的 h≥2 均空。若使用 (b) 的 Teichmüller 零点，它们 log 为零，也不会给出下一步的非零单位输入。

结论：e 增大只**缩小**第一次 log 的真实定义域（从 U^1 到 U^{n0}），不会恢复第二次迭代；「h≥2 空」的边界对所有 e 保持，但其原因从「像为非单位」与「源 log 域不含低主单位」叠加。

## 4. Kummer 零路径的整数格

Kummer 零次路径携带原 O_K 的整数结构（tame 包 §1 的源构造；III Def1.1(i)、Rmk1.2.2(i)）。在 e≥p−1 时：

- Kummer 零路径仍是 O_K 的单位/整数格，不受 p 进 log 收敛域影响；
- 第一次 log 路径（在 D_K 上）的像为 J_K=m^{n0}⊆m⊆O_K；
- 因此零路径与一次 log 路径共同生成的 Z_p-整数格为

      L_K = O_K + m^{n0} = O_K.                      (4.1)

即**整数格结论与 tame 情形完全相同：仍是 O_K**；不会因为 e≥p−1 而扩大。改变的只是归一化 shell I_K=m^{n0−e} 的指数（比 tame 小 n0−1 级）。这对 C9 的含义是：log 域缩小时，任何由「外 shell 较大」得到的增量不能反推为实际单位像；实际积分格仍是 O_K。

若只取 (a) 纯解析定义域（不含 Teichmüller 零点），零路径中的根单位没有解析 log，但仍不贡献非零 additive；非零像仍在 m^{n0}；整数格结论不变。

## 5. 分歧/循环情形、Gaussian q 与 tensor 整数格

**5.1 q-pilot 是非单位，不直接进入 p 进 log。** 原 q=BPS 的 q 在 m 中（ClauseB 的 valuation_lt_one）；log-link 的输入是单位 O_K^×，不是 q 本身。Gaussian 因子 q^{j²} 的赋值信息保留在乘法/LGP 作用与 tensor 整数格中，不通过 log(q) 送入 log-link；这与 C9-BPS-THETA-REGION 的源读法一致。

若写 qhat=π^u·(unit)（u∈Z），则 Gaussian 因子理想为 π^{u j²}O_K；其积分性/分母指数由 u j² 的整数性决定，和 p 进 log 定义域无关。若 qhat 来自 q=p^b 的根并满足 qhat^{2l}=q 等，则 u 由该根决定；tame 包例中 q=p^{3240}, π^{41}=p, qhat=q^{1/82}=π^{1620}，故 qhat^{j²}=π^{1620j²}O_K。e 改变只改变 π^e=p 的尺度，不改变「log 域」这一独立限制；不能把 p 进 log 定义域缩小误当成 q 的指数改变。

**5.2 小单位域的 exp(pz) 仍安全。** 对任意 e，n0≤e（因 ceil(e/(p−1))≤e，p≥3）。故 pz（z∈O_K）满足 v_p(pz)≥1≥n0/e，属于 exp 的收敛域；exp(pz) 的单位像和 log(exp(pz))=pz 仍成立。这是 tame 包中「保守小单位域」在 e≥p−1 的直接有效部分；其归一化像仍为 pO_K，积分格不因 log 域缩小而改变。该结论只用 §1 阈值，不用 e<p−1。

**5.3 循环/野分歧的附加边界。** e=p−1 是 tame 边界；e>p−1 为野分歧。p 进 log 阈值只依赖 e/(p−1)，与 Galois 群结构无关，故 J_K=m^{n0}、I_K、整数格 O_K 仍成立。但 tame 包中 Kondo 的辛群像与 trace 公式（Kondo 2026 v2 Lemma3.3；2025 v1 Theorem1.3 的 ker Tr=<y_2,…,y_e>；2026 Theorem2.6 的 α_+ log(u)=log(α^×u) 交换图）在野分歧下的 π-幂基/trace 适配不能逐字沿用：

- Aut(G_K) 的加法自同构仍是 K_+ 的等距/线性自同构，保持 m^{n0} 与 I_K（归一化 shell 由 n0,e 决定，保持）；
- 但 trace 的 W=ker Tr 分解、π 幂基的指数计算、以及 tame 参数 b 的整数格下界，在野分歧时需要重新按实际 ramification filtration 推导；不能直接复制 e<p−1 的 floor(bj²/e) 公式。
- 这是**源级 gap**，不是 log 域本身失效；log 域结论（n0,J,I,O_K 格）对野分歧仍成立，但“辛群作用能否给出同一规模增量”的结论只对 tame 有现成公式。

**5.4 Teichmüller 零点与野分歧。** μ_{q_res−1} 的阶与 p 互素；按 (b) 约定 log=0。野分歧不改变这个约定；但若原 C 采用 (a) 纯幂级数口径，部分 Teichmüller 根不在收敛域，需按 §2 分支处理。不能把「Teichmüller 根 log 为零」当成对任意低主单位的 log 定义；U^1U^{n0} 在 e>p−1 时仍无解析 log。

## 6. 无穷处

**6.1 实地方。** K_v=R，K_v^×=R^×；log|·|_v: R^×→R 为满同态，ker={±1}，无 p 进收敛阈值。Teichmüller 类比是 ±1（以及更一般的有限根），log-modulus 为零。第一次 log 的像为整个 R（加法），但不能把 R 的任意元素当作下一 log-link 的单位输入；R 上的加法→乘法只有 exp，而 exp 是 log 的逆，不给出新的源箭头。故同一 log 路径的第二次迭代仍为空；不存在 e 型定义域收缩。

**6.2 复地方。** K_v=C，K_v^×=C^×；log|·|: C^×→R 满，ker=S^1（单位圆），无收敛阈值；Teichmüller 类比单位圆（所有单位模根，含 μ_∞）。第一次 log 像为 R；第二次 log 需要正实数单位输入，源没有从 R 到 C^× 的规范单位映射；exp 只是逆，不提供新分支。

**6.3 archimedean shell/volume.** 原 archimedean 归一化 shell 与 Haar/volume 规范由 IUT III Def1.1(ii)/Prop1.2(vii)、IV Prop1.5/Thm1.10(vii)、AbsTopIII archimedean log-shell/measure 给出；本包只指出其 log 定义域无 p 进阈值，不能把有限处 n0 收缩公式搬到无穷处。其精确归一化与全局权重仍按 C9-ARCHIMEDEAN-UNIFORM-20261025.md 处理；本文件不新增该包的结论，也不把 archimedean 区域当作补偿有限处 log 域损失的任意项。

## 7. 对 tame 包哪些结论改变、哪些保持不变

保持（对所有 e）：
1. 同一 log-link 路径的 h=1 像在 m^{n0}，h≥2 在同一路径上定义域为空；
2. Kummer 零路径的整数格为 O_K，一次 log 路径不扩大它：O_K+m^{n0}=O_K；
3. Teichmüller 零点（按源约定）log 为零；exp(pz) 小单位域对任意 e 安全；
4. Aut(G_K) 的加法像保持 m^{n0} 与归一化 shell；
5. q 本身非单位，不进入 p 进 log；Gaussian 指数与 tensor 整数性不由 log 域决定。

改变（精确）：
1. tame 的 e<p−1 条件应改为 e≤p−1；e=p−1 仍是 U^1 全域 log。
2. e>p−1 时 n0=ceil(e/(p−1))≥2；真实解析/Teichmüller log 域为 D_K=μ·U^{n0}（源约定）或 U^{n0}（纯解析），不是整个 O_K^×。
3. J_K=m^{n0}，I_K=m^{n0−e}，比 tame 的 p^{-1}m 小 n0−1 级；归一化 log-volume 由 (2.3) 精确给出。
4. 低主单位 U^1U^{n0} 没有 p 进 log；任何把这些单位送入 log-link 的陈述都是源外新增分支。
5. 野分歧下 tame 的 trace/辛群整数格下界公式不能逐字复制；log 域结论仍成立，但源作用规模增量需重做。

## 8. 已证 / 推断 / 未解

**本包自然语言已证（用标准 p 进 log 收敛与初等赋值估计）：**
- §1 的阈值 n0=ceil(e/(p−1)) 及 log/exp 在阈值上互逆；
- e=p−1 仍属 U^1 全域；e>p−1 收缩到 U^{n0}；
- §2 的 J=m^{n0}、I=m^{n0−e}、volume 公式 (2.3)；
- §3 同一路径 h≥2 为空；§6 实/复地方 log 域与第二次迭代边界；
- §4 整数格 O_K+m^{n0}=O_K；
- §5.2 exp(pz) 安全；§5.1 q 非单位不直接入 log。

**推断/依赖源约定：**
- Teichmüller 根是否属于解析收敛域（(a) 与 (b) 分支）；IUT 源采用根单位 log=0 的约定，但本包没有把 IUT III 的原文逐行重排成「解析域+Teichmüller 点」的形式证明；
- e>p−1 时 source log-link 是否按 U^{n0} 或按整个 O^× 的某种形式 log 定义；若原 C 另给形式 log/分支，必须按原定义重审，不能用本包的 n0 替换；
- 野分歧下 Aut(G_K) 的 trace/辛群作用、π 幂基与 tame 整数格公式的适配；
- archimedean shell 的精确归一化及全局加权；
- 完整 C9/P6 的 h_C<Q_C 全局比较未证明。

**明确 failure/branch boundaries：**
1. 对 e>p−1，若把整个 O_K^× 当作第一次 log 的解析定义域，则陈述为假：U^1U^{n0} 上幂级数发散；不能从「外 shell 较大」反推实际输出。
2. 若在同一 log-image 路径上声称存在第二次 log-link，则为假/源外：像在 m^{n0}，不是单位；除非新增 1+ 或 exp 型源箭头，而 III Def1.1(i) 没有该箭头。
3. 若用 Teichmüller 根为零把 U^1U^{n0} 的低主单位也当作 log 域，则为假：零点是 torsion 点，不覆盖整段主单位。
4. 若把 tame 的 Kondo trace/辛群指数公式直接用于野 e>p−1，则未证；需要新的源级计算，不能作为本包结论。
5. 若把无穷处 log|·| 的 R/C 加法像继续当下一 log-link 单位输入，则为源外：需要 exp/正实数单位转换；源 log-link 不提供该箭头。

## 9. 剩余任务

1. 固定一份 e>p−1 的实际局部 C，核对 III Def1.1(i) 对 O_K^× 的 log 定义是 (a) 纯收敛级数还是 (b) Teichmüller 扩展；这是本分支的第一个 source-level 判定。
2. 在该 C 中计算上一条实际 log 路径的单位像、n0、I_K=m^{n0−e} 与 tensor 整数格 O_K；与 tame 参数 b、floor(bj²/e) 对照，给出精确的 volume 损失 (n0−1)/e log p。
3. 只对原 C 明确给出的源箭头追踪 1+log 或 exp 分支；不得新增。若没有，第二/第三次 log-link 保持空。
4. 野分歧：重做 Aut(G_K) 的 trace/辛群作用在 ramification filtration 上的整数格计算；不能复制 tame π 幂基公式。
5. 无穷处：按 C9-ARCHIMEDEAN-UNIFORM-20261025.md 的实际 archimedean 区域/归一化接入，单独计算其全局权重，不把它当作有限处 log 域损失的任意补偿。
6. 最后才回到完整 C9/P6 的 h_C<Q_C；本包不提供全局矛盾，也不把局部整数格 O_K 当成全局输出族的存在性。

## 10. 源引用

- IUT I：Def3.1（field-of-moduli）、Def4.10（prime-strip/procession 组装）。
- IUT III：Def1.1(i)（log-link 与 log-shell）、Prop1.2（尤其 (vii)）、Rmk1.1.1(i)（下一步 log-link 的单位输入）、Rmk1.2.2(i)（归一化 shell）、Prop3.4/3.5（log-Kummer/积分域）、Thm3.11(i)-(iii)（输出/hull）、Rmk3.11.1。
- IUT IV：Prop1.5、Thm1.10(vii)（archimedean 归一化/上界）；AbsTopIII Def5.4(iii)、Prop5.8(i)(ii)（O^×/perfection/shell 重建）。
- Kaiji Kondo, *Lubin-Tate representations over nontrivial finite Galois extensions of Q_p are not Aut-intrinsically Hodge-Tate*, arXiv:2605.25428v2, 24 Sep 2026, Theorem1.2, Lemma1.3, Definition3.2, Lemma3.3（局部 HTML 冻结：tmp/sheaf/n8/closure/sources/Kondo-2605.25428v2.html，URL https://arxiv.org/html/2605.25428v2）。
- Kaiji Kondo, *Anabelian aspects of the outer automorphism groups of the absolute Galois groups of mixed-characteristic local fields*, arXiv:2512.09231v1, 10 Dec 2025, Theorem1.3（局部 HTML 冻结：tmp/sheaf/n8/closure/sources/Kondo-2512.09231v1.html，URL https://arxiv.org/html/2512.09231v1）。
- Kondo 2026 Theorem2.6 的交换图与 unit/reciprocity/perfection 匹配（tame 包 §2 引用；本包只沿用其 additive 等距性，不把 tame trace 指数外推）。
- 标准 p 进 log 收敛：J. Neukirch, *Algebraic Number Theory*, GTM 322, Springer 1999, Ch. II §5；J.-P. Serre, *Local Fields*, GTM 67, Springer 1979, Ch. IV；I. Fesenko and S. Vostokov, *Local Fields and Their Extensions*, AMS 2002, Ch. I。Legendre 估计 v_p(n!)≤(n−1)/(p−1) 与 p 进级数收敛判别为上述标准内容。
- 内部冻结：C9-TAME-LOG-DOMAIN-20261025.md（SHA256 23b3514b94972de511f1b17e23ab3da832ed5bc63e89daca3875adeb07961f06）、C9-FIXED-GLUING-SWAP-20261025.md、C9-EVALUATION-DEFECT-ATTACK-20261024.md、C9-ARCHIMEDEAN-UNIFORM-20261025.md。

## 11. 验收记录

- 本包为 C9 stage1 自然语言研究；仅写本文件。
- Lean/Project/kernel/comparator/独立审查：未运行（不适用本包）。
- target_accepted=false；完整 C9/P6 原目标未证明。
- 本包新增的精确结论：n0=ceil(e/(p−1))、J_K=m^{n0}、I_K=m^{n0−e}、volume (2.3)、整数格 O_K、第二次迭代空、e=p−1 边界、Teichmüller/解析域分支；野分歧与 archimedean 全局接入是明确的剩余 gap。
