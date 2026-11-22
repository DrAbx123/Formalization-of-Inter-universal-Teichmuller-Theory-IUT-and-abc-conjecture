# C9：全局不等式装配与剩余亏损（stage1）

任务 ID：task-151 / C9-GLOBAL-ASSEMBLY-20261025；owner：primespine；日期：2026-10-25。
消费者：n8-c9-output-region-source-route 的 P6；SHEAF stage1。
性质：自然语言研究；不改 Lean/Project，不改目标，不新增任意假设，不伪造全局闭合。

## 0. 冻结输入与版本

本记录只使用以下冻结研究文件，不重读全仓，不修改其字节：

- C9-TAME-LOG-DOMAIN-20261025.md
  SHA256 23b3514b94972de511f1b17e23ab3da832ed5bc63e89daca3875adeb07961f06（下称 TAME）；
  EVIDENCE SHA256 1850b6aa5004fba40d9f406910d65a6939ddd53082ff740631863a6f2505475a。
- C9-FIXED-GLUING-SWAP-20261025.md
  SHA256 f734bc7bd33d8aa605315ad7e16709908722186ac27eece0e5a5c10cb10b1b19（下称 GLUING）。
- C9-PROCESSION-ORBIT-20261025.md
  SHA256 b7a45e8c28bbe42461476ec0b4eb2acf889a0202a9439dde78b3410e34e329a5（下称 PROC）。
- C9-ARCHIMEDEAN-UNIFORM-20261025.md
  SHA256 d7138ca9dd8fcca88fda3d23ab251d06cddff01f0fb2ac796d9ddf54291e200f（下称 ARCH；状态仍为“研究中”，见 §5）。
- C9-SOURCE-SYMPLECTIC-SPAN-CERTIFICATE-20261025.json
  SHA256 8dad68c6d38fb89bd4cc1105a81484e5fb09f0ad7e9413b4c78d143344290db0（SYM）。
- 原文位置以 TAME/GLUING/PROC 已核页号为准：IUT I May 2020，§0 pp.33–34、Def4.10 pp.119–120、Prop6.9 pp.169–170；IUT III May 2020，Def1.1、Prop1.2、Rmk3.1.1(ii)、Prop3.4/3.5、Prop3.7(v)、Def3.8(i)、Prop3.9、Rmk3.9.5、Thm3.11(i)、Rmk3.11.1(iv)、Cor3.12，相关页 pp.94–95、102–106、110–117、127、131–134、152、154、162–163；IUT IV April 2020，Rmk1.7.1 pp.17–18、Prop1.5、Thm1.10 proof(iv)–(vii) pp.26–31；AbsTopIII 的实际 archimedean log-shell/measure。
- 外部文献仅按 TAME §2 使用 Kaiji Kondo, arXiv:2605.25428v2 的 Lemma3.3（真实 Aut(G_K) 辛群供体）；本记录不复述其证明。

本记录不把 TAME/GLUING/PROC 的局部结论升级为完整 P6。所有“已证”均指这些冻结文件中的自然语言证明/证书；Lean、Project、kernel、comparator、独立审查均未运行。

## 1. 全局对象、归一化与要排除的命题

固定一份原文合格完整初始 Θ-data C，以及固定的 native q、BPS/Θ-gluing、目标列、递增 normalization。记 F=F_mod，S_bad(C) 为有限坏地方集，S_good(C) 为补中的被选有限地方，S_∞(C) 为 archimedean 地方，α_v 为原行/Θ权重（§2）。

记 H_C 为完整最终输出族的 holomorphic hull，h_C=ν(H_C)；Q_C 为同一份初始数据中 native q-pilot 的全局校准 log-volume。原目标是

    ∀ 合格 C，h_C = ν(H_C) ≥ Q_C，                       (G0)

等价地排除严格亏损 h_C<Q_C。本记录不声称 (G0)，也不声称存在反例；只把局部已证下界装配成 G0 的精确剩余量。

F_mod=Q 的 uniform profile 是测试对象，理由见 TAME §7：I Def3.1(e) 的 V→V(F_mod) 是 section，每个有理 p 只有一个选定地方，坏质量只能是 0 或 1；不能把未选定的共轭地方改成新的 ρ=1/2 平均来回避 uniform 情形。

## 2. row/Θ 权重与全局归一化

按 III Rmk3.1.1(ii)、Prop3.9、IV Rmk1.7.1，对固定 rational p 及 v|p 定义地方权重

    α_v = [(F_mod)_v : Q_p] / [F_mod : Q]，   Σ_{v|p} α_v = 1.   (W1)

tuple w=(w_0,…,w_j) 的权重为 ∏_{i=0}^j α_{w_i}；K_v/F_mod 的额外次数由原 degree normalization 消去，不能再乘一次。对 F_mod=Q，α_v=1。

行指标 j=1,…,m，m=(ℓ−1)/2；Θ/坏质量权重为 ρ^{j+1}（TAME (15)；ρ 是该 p 上坏 profile 的原权重，uniform 取 ρ=1）。procession 读出是按 j 的加权平均，不是对全部 tuple 的未加权平均。全局 h_C 模板为

    h_C = Σ_{p∈S_bad∪S_good} α_p h_p + Σ_{v|∞} α_v h_v,     (W2)

其中 h_p 是固定 p 上按 (W1) 和行/Θ权重算出的局部 normalized log-volume，h_v 是 archimedean 局部读出。Q_C 是 native q 的有限处读出：

    Q_C = Σ_{p∈S_bad} α_p Q_p,   Q_p = -ρ_p b_p/e_p · log p.   (W3)

Q_p 只在坏地方非零；good finite profile 的 Gaussian 为单位，按原 normalization 其相对参考体积为 0。archimedean 处没有 native q-pilot 的同类 Q 项，故 Q_C 不另加 Q_∞；但 h_C 必须加 h_∞。对 F_mod=Q，α_p=1，ρ_p∈{0,1}；uniform 取 ρ_p=1 对所有 bad p。

状态：(W1) 来自原文权重定义（已核）；(W2)–(W3) 是本记录为装配写的精确模板，尚不是完整 C 上的已构造对象；h_∞ 无当前实际构造（§5）。

## 3. 局部已证下界（可直接引用的部分）

本节只列 TAME §3–§7 已证、且本装配实际消费的公式。均为固定局部 tame 类型；不把它们当成任意 C 的全局结论。

### 3.1 源辛群区域与 hull 增量

设 K/Q_p tame totally ramified cyclic，e=ℓ，O_K=Z_p[π]、π^e=p u，u∈Z_p^×；π^nO_K，n=se+t，1≤t≤e−1。真实 Aut(G_K) 的辛像给

    closed_span_Zp ⋃_{α∈Aut(G_K)} α_+(π^nO_K) = p^s m_K,      (T7)

其 field holomorphic hull 相对原区域的 normalized volume 增量为

    ((t−1)/e) log p.                                         (T8)

TAME §4 进一步给实际点见证：存在实际 γ 使 Hull(γ(π^nO_K))=p^s m，且 t≥2 时增量严格正；t=1 时为零。无枚举不可数个自同构；有限辛 transvection/模 p 证书见 SYM 的 72 个 finite span cases。

### 3.2 tensor order 与 symplectic 改善

对 r=j+1 个坏因子的实际 tensor order D_r，TAME (9) 的原 tensor-order/末端下界为

    ν(L^Sp_{r,n})/log p = −δ_r − s − e^{−r},
    δ_r = (r−1)(e−1)/(2e).                                  (T9)

完整 Ind1 源对齐（GLUING (11)–(13)，TAME §5）后在目标 hull 中得到不含 tensor-order 损失的 all-bad 下界

    ν(H_{C,j,p})/log p ≥ −s_j − 1/e.                        (T14)

对坏/好混合 profile，在 ρ 权重下 TAME (15) 给

    ell_j^aligned ≥ −ρ^{j+1}(s_j+1/e),                      (T15a)
    h_p^aligned/log p ≥ −(1/m)Σ_{j=1}^m ρ^{j+1}(s_j+1/e).   (T15b)

这里 b j²=s_j e+t_j，1≤t_j<e，m=(e−1)/2。uniform profile ρ=1 时 (T15b) 化为

    H_p^Sp/log p := −(1/m)Σ_{j=1}^m(s_j+1/e).               (T15c)

symplectic 相较 (T9) 的精确改善为（逐 j，再取原行平均）

    G_p/log p := (1/m)Σ_{j=1}^m[
        δ_{j+1} + e^{−(j+1)} − 1/e],                        (T16)

因为 δ_{j+1}+e^{−(j+1)}≥1/e（e≥3,j≥1；小 e 退化处单独检查）。G_p≥0 是实际源辛群带来的、hull 可见的改进；不来自任意 GL 或标签自由化。

### 3.3 两个可能的整数轨道分支

TAME §6 把固定 all-bad r-tuple、只允许原 Gaussian 整数区域、逐因子辛像和 factor permutations 的实际子族分类为两种（B=closed_span）：

    B=O_K 时： L_A=Σ_i p^s π_i D_r,
    B=I  时： L_B=p^{s−r+1} J^{⊗r},                        (T16b)

其中 I=p^{−1}J。对应目标 hull 的归一化值为

    ν_A/log p = −s−1/e,                                   (T17a)
    ν_B/log p = −s+(r−1)−r/e,                             (T17b)

差 (r−1)(1−1/e)。是否进入第二支是有限表示问题：实际 barΓ⊂GL_e(F_p) 是否把 O_K/J 的模 p 直线移走；不能通过枚举全部 GL_e(F_p) 直接选支，也不存在已证的实际输入必在第二支。

### 3.4 已证数值例子（仅局部 profile）

e=41，m=20，ρ=1，单位 log p。Q_p/log p=−b/41，H_p^Sp/log p=−(1/20)Σ_{j=1}^{20}(s_j+1/41)。

| b | H_p^Sp | Q_p | D_p^Sp=Q_p−H_p^Sp | B=O_K 分支 ν_A | B=I 分支 ν_B |
|---:|---:|---:|---:|---:|---:|
| 3 | −411/41 | −3/41 | 408/41 | −411/41 | 9/41 |
| 273 | −39156/41 | −273/41 | 38883/41 | −39156/41 | −38736/41 |

TAME §7 已报 b=3 的 −411/41、Q=−3/41，以及 b=273 的 B=I 值 −38736/41；H^Sp 与 D^Sp 是按 (T15c) 的直接算术。

### 3.5 已证有限处/procession 辅助事实

- 纯 capsule 置换的精确 hull 阈值为 j² min 而非 j² average；procession 平均公式和严格正增量见 PROC (1)–(3)。ρ=1/2、ℓ=41 例子中 seed=−287/4、hull=−629097/4194304、Q=−1/2；纯置换对任意深度不突破 −[ℓ(ℓ+1)/12]a log p < −a log p（PROC §4）。
- 共同保体积加性运输 T 下，有限批实际输出的闭 Z_p-生成格 L 满足 T(L)⊆H ⇒ ν(H)≥ν(L)（PROC (5)–(6)）；这是有限处下界，不适用于 archimedean 球（球不对加法封闭）。
- 固定 gluing 的同末端 packet 映射存在，完整 Ind1 轨道可送入同一目标容器（GLUING (8)–(13)）；这是 (T14) 能消去 tensor-order 损失的原因。它没有给出 native q 的全局体积类识别。

## 4. 全局装配：从局部下界到 h_C、Q_C 的剩余量

### 4.1 已证的有限坏质量下界

对 uniform bad profile（ρ_p=1）且每个 bad p 属于 §3 的 tame 类型，由 (T15b) 和 (W2)（good finite 项按原 normalization 为 0）有

    h_C ≥ Σ_{p∈S_bad} α_p H_p^Sp · log p + h_∞(C),          (G1)

其中 H_p^Sp 由 (T15c) 给出。这是已证局部公式的条件装配：只要该 C 的每个 bad p 都满足 §3 局部类型、行/Θ权重按 (W1)，(G1) 成立；不是对所有 C 的无条件定理。对 F_mod=Q，α_p=1。

同一 C 的 native q 读出由 (W3) 为

    Q_C = Σ_{p∈S_bad} α_p (−b_p/e_p) log p.                 (G2)

### 4.2 精确剩余亏损

定义每个 bad p 的 symplectic 后局部亏损

    D_p^Sp := Q_p − H_p^Sp log p.                           (G3)

代入 s_j=(b j²−t_j)/e、Σ_{j=1}^m j²/m=e(e+1)/12，得到恒等式

    D_p^Sp/log p
      = b(e+1)/12 − (b−1)/e − T_p,
    T_p := (1/(e m))Σ_{j=1}^m t_j,   0≤T_p<1.              (G4)

这是本包交付的“精确剩余量”：不是新假设，而是 (T15c)/(W3) 的代数等价。symplectic 改善量 (T16) 把 (T9) 的旧亏损 D_p^old 减为

    D_p^Sp = D_p^old − G_p.                                (G5)

因此全局（在 (G1) 的适用范围内）

    Q_C − h_C ≤ Σ_{p∈S_bad} α_p D_p^Sp log p − h_∞(C).     (G6)

若 (G6) 右端≤0，就得到该 C 的 G0；若 >0，右端给出已证下界不能排除的剩余亏损。注意 h_∞ 可能为负，故不能把 (G6) 右端直接当成全局亏损；也不能令 h_∞=0——见 §5。

### 4.3 F_mod=Q uniform 的数值剩余量

取 F_mod=Q、e=41、m=20、ρ=1、α_p=1、b=3：

    H_p^Sp/log p = −411/41,  Q_p/log p = −3/41,
    D_p^Sp/log p = 408/41 ≈ 9.9512195122.                  (G7)

若该 C 只有一个 bad p 且无 archimedean（或 h_∞≥0），则已证局部下界给

    Q_C−h_C ≤ (408/41)log 41 − h_∞,
    h_C ≥ (−411/41)log 41 + h_∞.                           (G8)

这不是全局反例：h_∞ 未计算，且 C 的完整构造未给出。它只说：在 B=O_K 支、该局部 profile，symplectic 改善后仍有 408/41 的局部亏损；要得到 G0 需要其他实际地方/无穷处的正补偿。

b=273 时

    D_p^Sp/log p = 38883/41 ≈ 948.3658536585,              (G9)

更大，不能靠 (T15b) 单独闭合。若进入 B=I 支，b=3 的局部值变为 ν_B=9/41，此时 Q_p−ν_B=−12/41<0，局部比较反而闭合；b=273 的 B=I 仍为 −38736/41，Q_p−ν_B=38463/41>0，局部仍亏损。因此：

- b=3,B=O_K：局部亏损支（可能成为全局反例的局部种子）；
- b=3,B=I：局部盈余支（不能作为反例种子，但全局仍需 archimedean/其他处）；
- b=273：两分支局部都亏损，若 G0 成立必须由其他实际源贡献补偿。

这些是分支分类，不是已构造的全局反例。

## 5. archimedean 处：当前实际缺口

(W2) 的 h_∞(C) 必须来自 IV Prop1.5/Thm1.10(vii) 与 AbsTopIII 的实际 archimedean log-shell/measure，而不是把实/复地方当作普通有限 Haar 块。ARCH 状态仍是“研究中”，没有给出：

1. 完整 C 在 S_∞(C) 上的实际可测区域 R_{C,v} 及其正有限质量；
2. 原 normalization 下的 h_v=log μ_v(R_{C,v}) 或 ν(H_C) 的 archimedean 项；
3. h_∞ 的符号/大小界，尤其是能否补偿 §4 的 D_p^Sp>0。

可用相关事实只有“archimedean 处不能直接套用现行 P6 Adm/Readout”：Wave18 的 P6ArchimedeanAdmNoGo 证明当基域有 infinite place 时，现行 Adm/P6Readout 在 archimedean native place 上不成立（单位球面 Haar 质量零、a.e. 零 local log 不可能有正质量），所以不能把 h_∞ 设为零或把 archimedean 地方塞进有限块读出。该审计是接口约束，不是 IV 原全局 archimedean 项的计算。

精确缺口：需补充一个与 (W2) 同一 normalization 的 actual archimedean readout h_∞^actual(C)，并证明其下界（或上界）足以代入 (G6)。在它缺失时，(G6) 只能写成

    Q_C−h_C ≤ Σ α_p D_p^Sp log p − h_∞^actual(C),          (G10)

而不能宣布右侧符号。若未来得到 h_∞^actual(C) ≥ Σ α_p D_p^Sp log p，则相应 C 的 G0 成立；若得到 h_∞^actual(C) < ...，才可能进入反例分支。两者都未证。

另有两个同层缺口，不能与 archimedean 混为一谈：

- 完整 C 的 S_bad 是否全部满足 §3 的同一 tame e=ℓ 局部类型；TAME §8 明确只处理特定 profile，F_mod=Q uniform 仍是测试对象；
- row/Θ 权重在全 procession 上的实际归一化：本记录使用 (W1) 和 TAME (15) 的公式，但“完整 C 的每个 row/column 权重均已构造并相加”未证；PROC 明确其纯置换轨道只覆盖实际子族。

## 6. 已证 / 推断 / 未证的分层清单

已证（冻结文件中的自然语言证明/证书，非 Lean kernel）：

1. 局部 tame log 定义域与 J_K=m、I_K=p^{−1}m（TAME §1）。
2. 真实 Aut(G_K) 辛像的轨道生成 (T7) 与 hull 增量 (T8)；有限 transvection 证书 SYM。
3. tensor-order 公式 (T9)、完整 Ind1 对齐后的 (T14)、混合 profile 的 (T15)。
4. 两个整数轨道分支 (T16b)–(T17b) 的分类及其模 p 有限表示判据。
5. procession 置换的 min 阈值/精确体积（PROC (1)–(4)）、共同加性运输下界（PROC (5)–(6)）、固定 gluing 的共同末端运输（GLUING (8)–(13)）。
6. 数值表 e=41,b=3,273 的局部值（TAME §7；本记录只做 (G4) 的代数复算）。

推断（本记录装配，不是原文定理）：

7. (W2)/(W3) 的全局加权模板及 F_mod=Q 的 α_p=1,ρ_p∈{0,1} 代入。
8. (G1)、(G6)、(G10) 的“局部下界→全局剩余量”装配；它们依赖每个 bad p 都落入 §3 类型这一未逐项验证的条件。
9. 若 h_∞≥0 则 (G8) 的符号判断；h_∞ 的实际符号未定，故不登记为证明。

未证（不能用于闭合 P6）：

10. 完整合格 C（尤其 F_mod=Q uniform）的实际坏集/行权重全构造；
11. 实际 h_∞^actual(C) 及其界；
12. 完整 h_C、Q_C 的等式/不等式 (G0)；
13. 第二支 B=I 是否由实际源发生（有限 barΓ 是否移动 O_K/J）；
14. 任何完整全局反例；本记录没有构造，也不把局部亏损支冒充反例。

## 7. 结论与可执行下一步

本记录完成条件性全局装配：在 §3 局部类型和 (W1) 权重适用时，uniform bad profile 的已证有限下界为 (G1)，其相对 native q 的精确剩余亏损为 (G4)/(G6)，symplectic 改善为 (T16)。F_mod=Q,b=3,B=O_K 仍有 408/41 log41 的局部亏损；b=273 更大（38883/41 log41）。B=I 只在 b=3 局部转正，b=273 仍负。全局 G0 仍未证明；archimedean h_∞^actual、完整 C 的权重/坏集构造和第二支判据是三个明确缺口。

下一步（按优先级，不新增任意假设）：

1. archimedean 实际 readout：按 IV Prop1.5/Thm1.10(vii) 与 AbsTopIII 构造 R_{C,v}、h_v 和 h_∞^actual(C) 的上下界；先做 F_mod=Q 的实/复地方，保持 IV 原 normalization。
2. 完整 C 的局部类型清点：在 F_mod=Q uniform 测试对象上，逐 bad p 核验 e_p=ℓ、b_p、t_{p,j}、权重 ρ_p，把 (G1) 适用条件写成表；不与未核验 profile 混合。
3. 有限支判据：只计算实际 barΓ 在 GL_e(F_p) 中对 O_K/J 直线的像，决定 (T16b) 的 B=O_K/B=I；不枚举全 GL，不用“非 Hodge–Tate/大 Out”替代。
4. 若 1–3 完成后 (G10) 右端仍正，才把该 C 登记为 candidate 全局反例；在此之前只保留为局部亏损支。

没有 target_accepted、kernel_closed、完整 P6 或 ABC 结论。
