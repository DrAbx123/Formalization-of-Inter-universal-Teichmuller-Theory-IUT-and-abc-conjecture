# C1：跨日期复用、单侧数值见证与 hull/carrier 核查

日期：2026-10-26；owner：当前 chat root；阶段：SHEAF stage 1。
消费者：`n8-c9-final-evaluation-capsule` / `n8-c9-output-region-source-route` 的论文 signed `Q(C) ≤ h(C)`。
本包由 root 单人执行；没有唤醒旧 agent，没有新增 Lean 定义或接口。

## 任务与证据边界

数学目标是对每一份论文合格的 initial Θ-data、固定 gluing、原 procession 权重及读数证明 `Q(C) ≤ h(C)`。不改变原目标；只研究可用于它的单侧下界。不要求 exact output attainment，不把抽象接口非蕴含称为完整 IUT 独立性。

读：既有 10 月 16–21 日 source/arithmetic/hull 记录，10 月 23–25 日自然语言路线、纠偏、TC lower/upper 审计和算术运输源码。继承前次摘要，不重做 A1/A2/A3 调用审计。

写：本记录及同名 evidence JSON，既有两个 C1 节点的复用补充，`AUDIT_LEDGER.md`、`coord/STATE.md`、`coord/queue.md` 追加。所有生产 Lean 文件与目标定义保持原版本。本轮仅复跑五个窄范围 Lean 文件；未运行 comparator、Project build 或独立审查；旧证据仍按各自版本标复用。

statement dependencies：原目标的 allowed possible-image family、有限地方实际 tensor carrier、holomorphic hull、signed normalized log-volume。
proof dependencies：既有 arithmetic hull / Haar transport；源 branch 的 allowedness 与目标接入仍须逐箭头证明。

## 已核对的纠偏

1. `C9-TC-EQUALITY-20261025.md` 已明确：选定子族只给目标 hull 的下界；upper/exact equality 另需证明。故单侧路线不是新发明，必须从该记录与 `C9-BI-REGION-CONSTRUCTION-20261025.md` 接续。
2. `C9-P6-CAN-NATURAL-PROOF-V2-20261025.md` 的 A3 直接引用 xi-f 的目标 membership，不能充当独立的 C1 证明。`C9-REVIEW-THREE-TRANSPORT-20261025.md` 已拒绝将该 membership 填入 Theorem 3.11。
3. `PaperP6ComparisonActual.lean:140–162` 证明负 q-log 小于非负 canonical reference-hull log。此算术定理可复用，但并未识别论文 Θ-output hull。
4. `C9-TARGET-CONTAINER-NEW-20261025.md` 把一般线性/affinoid map 的 hull 交换与 ring/代数同构混用，并说 Qp-代数同构可任意改变行列式体积。须用实际 finite local-field product 的 integral closure 与既有 transport 定理核实，不能沿用这条泛称作为新阻塞。
5. 显式构造完整数值 C 是源忠实数值实例/反例的要求；研究全称 C1 时可以固定任意合格 C。不得把“未构造一个数值 C”升级为全称自然语言证明的先决条件。

以下为续查结果。算术运输的自然语言证明已经展开；没有证明完整 C1，也没有新建一个把兼容性作为字段的 capsule。

## 1. 跨日期检索实际改变了哪些判断

本次用 `rg --files` / `rg -n` 查 `logs/coordination`、`tmp/sheaf/n8`、`LeanFormal/IUT`、`papers`、`dag`、`coord` 和 `AUDIT_LEDGER.md`。按关键词命中后阅读相应章节，未把搜索命中当作全文审查。继承上一轮摘要，不重跑 A1/A2/A3 的依赖或编译调查。下面列的是复用链，不是新增成果数量。

| 日期 | 证据 | 本包采用的结论 |
|---|---|---|
| 10-16 | `logs/coordination/iq-carrier-alignment-20261016.md`、`hull-determinant-log-volume-20261016.md`；前轮已核 | 数值 dictionary 与 source realization 分开；determinant 代数不生产 source 比较 |
| 10-17 | `source-polyisomorphism-gap-20261017.md` | 当时六文件的缺失审计有明确范围，不能扩成“全仓无 arithmetic carrier” |
| 10-17 | `integral-log-shell-index-arithmetic-20261017.md` | shell/reference 的指数和 Haar 比值已有精确算术供体；没有任意选择的校准常数 |
| 10-18 | `n8-distilled-06-hull-degree-comparison-20261018.md`，A–D、O–R | possible images 先有实际环境；signed log 不可截成 ENNReal；任意精度下逼近早已是可用路线 |
| 10-20 | `theta-link-evaluation-sync-20261020.md` | evaluated theta 是根单位轨道中的 qhat^(j²)，qhat 是 Tate q 的 2ell 次根；整张 evaluation 图与逐 label 的根单位歧义不同 |
| 10-21 | `l04-implementation-playbook-20261021.md`，1–4 | 用已有实际 unit-log/shell 自然性；同一拓扑不等于同一范数，p 与 ell 不可互换 |
| 10-22 | `tmp/sheaf/n8/Group6Normalization.lean` | `rawLog = degree * normalizedLog + referenceLog`；不是两种 volume 同名就相等 |
| 10-24 | `C9-CONTRADICTION-ATTACK-20261024.md` | BPS 保留抽象 pilot；到原生度量尚有校准责任。小单位 log 校准不能提前穿过 hull |
| 10-24 | `C9-LOCAL-GLOBAL-DESCENT-ATTACK-20261024.md` → `C9-MARKED-IMAGE-DESCENT-20261024.md` | cQ3 collection 对象存在不够；实际局部比较满足 h−Q=S−kappa。后续用户纠偏明确：只需证明 S≥kappa 或实际 escape，不能强迫所有比较 kappa=0 |
| 10-24/25 | `C9-STRICT-DEFICIT-LOOP-20261024.md`、`C9-JH-OUTPUT-REGION-20261025.md` | J_H 是实际非零数；代回理想保留 j²，正确 determinant/power 不会凭空产生补偿 |
| 10-25 | `C9-PROCESSION-ORBIT-20261025.md`、`C9-FIXED-GLUING-SWAP-20261025.md` | 加性 span 给单侧下界；选定子族的能力不能当完整 H_C 的上界 |
| 10-25 | `C9-TAME-LOG-DOMAIN-20261025.md` → `C9-IND1-GLOBAL-20261025.md` → `C9-GLOBAL-ASSEMBLY-BINDING-20261025.md` | 原 TAME (11)–(14) 的“已接入目标”被撤回；必须保留 source donor、实际目标分支和 reference 条件 |
| 10-25 | `C9-ADJUDICATE-HAFULL-20261025.md` | `ker Tr` 是 Qp 空间，不是整数格；`w ∈ ker Tr` 不推出 `w ∈ m`，两个 B 分支仍未决定 |
| 10-25 | `C9-TC-EQUALITY-20261025.md`、`C9-NL-MASTER-20261025.md` | `h_C >= lowerCertificate` 只给亏损的上界；正的上界既非反例也非正性证明 |
| 10-25 | `C9-REVIEW-THREE-TRANSPORT-20261025.md` | 把 q-pilot membership 填进 “Theorem311Full” 是循环；不沿用这种 A3 |
| 10-25 | `C9-CAN-A3-COMPATIBILITY-DERIVATION-20261025.md`、`C9-REVIEW-COR312-LOOP-20261025.md`、`C9-REVIEW-PAPER-XIF-20261025.md` | 不能把 cQ3/cQ4、closed loop、xi-f 三个不同层次互相当作证明；本次另指出早期 derivation 中单位商与平凡化的具体错误，见 §4.2 |

因此，不能用早期缺口清单抹掉后来的算术定理，也不能跳过后来的撤回而引用早期“source 已证”。更正链应当随引用一同保留。

## 2. 已可完整证明的算术 hull-carrier 兼容性

以下是实际局部域定理，不是 C1 的假设包装。复用生产源码：

* `LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/LocalFieldProductHullTransport.lean`
* 同目录 `LocalFieldProductLogVolumeTransport.lean`
* `LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceArithmeticTupleHullTransport.lean`
* 同目录 `FinitePlaceArithmeticIQHullTransport.lean`

固定素数 p。令 E、E' 为非零有限 étale Qp-代数，写成有限局部域之积。令 O_E、O_E' 为各分量整数环之积；`f : E ≃_{Qp-alg} E'` 是实际代数同构。设 S 的闭包紧，且每个 field 分量有一个来自 S 的非零投影。这些是假设范围，不是所有 final outputs 已具备这些条件的声明。

把 Hull_E(S) 定义为包含 S 的所有可逆 lambda 所给 `lambda O_E` 的交。该紧且逐分量非退化的情形，hull 是一个非退化紧开 fractional ideal。取任意加法 Haar 测度 mu、mu'，令 d=dim_Qp(E)=dim_Qp(E')，定义有符号读数

    nu_E(A; O_E) = (log mu(A) - log mu(O_E)) / d,

其中 A 是正且有限测度的可测区域。此处 `log` 前先有正有限性，没有 ENNReal.toReal 的无穷/零塌缩。

**命题。**

    f(O_E) = O_E',
    f(Hull_E(S)) = Hull_E'(f(S)),
    nu_E'(Hull_E'(f(S)); O_E') = nu_E(Hull_E(S); O_E).

**证明。**

1. O_E 恰为 E 中在 Zp 上整的元素。f 固定 Qp，故固定 Zp；将整方程逐项作用 f，得到 `f(O_E) ⊆ O_E'`。对逆同构重复，得到相等。f 及其逆是有限维 Qp 空间上的线性映射，因而连续。
2. 对每个可逆 lambda，乘法相容给 `f(lambda O_E)=f(lambda) O_E'`。逆同构给出所有这类区域之间的双射，并保留“包含 S”。双射保交，因此将定义 hull 的整族相交后得到第二个等式。这一步没有用任意线性映射代替环同构。
3. f 把 mu 运输成 E' 上的 Haar 测度。Haar 唯一性给一个有限正数 c，使所有相应可测区域满足 `mu'(f(A))=c mu(A)`。同一个 c 也满足 `mu'(O_E')=c mu(O_E)`。两式取比、取 log、除以共同的正 d，c 精确抵消。
4. 对每个 field 分量，紧集 closure(S) 上的绝对值有非零最大值；选达到该值的 lambda 分量。这些坐标球的乘积包含 S，且每个包含 S 的 fractional ideal 必包含该乘积，故它正是 hull。非零半径的局部域球紧且开，所以乘积有正有限 Haar 测度。将第三步应用于第二步的 hull 即得第三式。证毕。

源码中的 `normalizedLogVolume` 在这一层是 `log mass - log unit mass`；额外的 `/d` 属于 degree-normalized 层。上述证明明确保留了这个区别。实际 tuple 的两种 field decomposition 的复合就是这种 f，所以已有 `arithmeticTupleFieldHull_addHaar_logVolume_decomposition_change` 正好可用。

若原 procession 各块的 j、place 和正权重由实际映射保留，逐块等式乘原权重再求和，仍得相等。若这些标签/权重没有证明对齐，则只能使用局部结论。无穷处不从此非阿基米德定理推出。

这修正 `C9-TARGET-CONTAINER-NEW` 与 `C9-IND1-GLOBAL` 中过宽的担忧：**真正的有限 Qp-代数同构不会任意扭曲单位相对的 Haar log-volume。** 对两边未经归一化的任意 Haar 测度，当然不必逐点等测度；上面证明的正是本题有用的相对读数不变性。纸面 source 是否给出这样一个 f、其参考对象是否真是这些 O，仍是另外的问题。

## 3. 为什么“保体积线性映射”还不够，以及剩余校准到底是什么

为说明第二步的适用范围，取真实代数 `E=Qp×Qp`、`O=Zp×Zp`，取

    T(x,y)=(x+p^(-1)y,y).

T 的行列式为 1，所以 `mu(T(O))=mu(O)`。但

    Hull(T(O))=p^(-1)Zp × Zp,

其体积是 O 的 p 倍。各分量投影的最小 fractional ideals 直接给出这一等式；例如 `(p^(-1),0)` 在该 hull 中，却不在 T(O) 中。因此 `T(Hull(O)) != Hull(T(O))`。这是一般线性运输的明确反例，不是 IUT 反例。正面的环同构定理和这个反例应同时保留。

若实际 source/reference 用的是满 Zp-格 R、R'，而不是 O_E、O_E'，同一 Haar 计算给出更一般的精确式：

    nu_E'(f(A); R') = nu_E(A; R) + delta,
    delta = (log mu'(f(R)) - log mu'(R')) / d.

取满格 `L=f(R) ∩ R'`。它在两者中都是有限指数，由陪集分解有

    delta = (log [f(R):L] - log [R':L]) / d.

若这两个指数分别为 p^a、p^b，则 `delta=(a-b)log(p)/d`。这是实际整数格决定的数；不能按所需 gap 选 a、b。若 `f(R)=R'`，则 delta=0。10 月 17 日的 shell-index 算术和 10 月 22 日的 normalization 等式正是这里可复用的供体。

对满格 Lambda 与参考格 R，取 Qp 基后相对 determinant 的绝对值是 `mu(Lambda)/mu(R)`；f 同时作用于两格时，分子分母中的 det(f) 抵消。对相对 determinant line 取 M>0 次 tensor power，log 读数乘 M，再按 M 归一化即恢复原读数。故更换 Haar 测度、换 field decomposition、共同取 tensor power，都不能制造补偿。`C9-JH-OUTPUT-REGION` 的实际计算已经验证：把 Gaussian 用 J_H 重写仍保留 j²。

**不能由这个算术证明填写的源等式是**：论文的 evaluation/Kummer 所得 R、R' 是否就是上面实际 f 运输的那两个参考格，以及 inverse-reference determinant 与原 procession 归一化如何对应。xi-d 特别要求校正 1-column 的 vertical shift，不能将该项删掉。

## 4. 对源 gate 的实际证明尝试：在哪里停下

复用 `C9-FIXED-GLUING-SWAP` / `C9-TAME-LOG-DOMAIN` 的候选：固定原 C、目标列、core/gluing，记原 packet 运输为 T、实际原始输出区域为 R_C。若有同源同靶且同 core 的 procession 同构 Phi、Psi，令 beta=Phi^(-1)Psi，并令 f=T beta_+。

在这些对象真正给定后，以下**重编号证明**完全有效：若 G 是固定 C 允许的源作用群、beta∈G，且目标族确实包含所有 `T(gamma R_C)`（gamma∈G），则

    T(beta gamma R_C) = f(gamma R_C)

仍是同一族的输出。若 f 是第 2 节的代数同构，目标 H_C 包含它们的并，从 hull 最小性得到

    f(Hull(union_gamma gamma R_C)) ⊆ H_C.

再应用第 2 节的读数运输，即有实际单侧下界。这里不需要证明 f 是目标 H_C 的自同构，也不需要把 H_C 认同为这一子族的 hull。

**但不能反向把这段证明当作其源前提已经构造。** 本次重读 III Thm3.11(i) 的 (a)(b)(c)、Ind1 和 functoriality，以及 `C9-IND1-GLOBAL` 的 SD1–SD4 / TC-A…H，得到的边界为：

* Theorem 3.11 确实对整份 (a)(b)(c) 给出 procession functoriality；不能说论文完全没有允许作用。
* `T=kappa_1^(-1) Q(Phi) kappa_0` 是 packet 运输。还需证明用于下界的 R_C 真是原 Theta-pilot 的 evaluation/integral-region 像，且重编号后仍处于同一 C 的最终输出族；仅从两个局部域同构不能得到这一点。
* `f=T beta_+` 作为复合等式不保证 f 是前述代数同构，也不保证所选 Psi 与实际 Kummer representative、固定 q/BPS、unit 域及参考格相容。Poly-isomorphism 是同构集合；随意在不同集合中各选一个代表不会自动组成所需交换图。
* 即使区域接入成功，论文的局部/全局读数还要用第 3 节保留参考项，并保留原 place/label 权重。正面的 arithmetic transport 不能自行认出 q-pilot 的原读数 Q。

故本包没有闭合最关键的箭头：

    实际 final evaluation 的允许分支
      → 同一固定 C/目标列里的实际区域 f(gamma R_C)，
      → 原 reference/determinant 读数。

这正是旧 TAME (11)–(14) 后来被撤回的地方。算术 TC-C 的单位相对部分可直接复用；不能因此恢复已撤回的 source TC-A/B/E/F。也不能因 Lean 尚未定义这个 family 就断言完整数学理论不可证明。

另须纠正旧 `C9-HULL-CARRIER-HISTORY-PROOF` 第 4 节(iv)的表述：IPL 的关联和 final evaluation 的各种 rigidification possibilities 并没有在本包被证明包含指定 q-rigidification。该步仍是 C1 责任，不能写成“于是”后当作完成。LANA (9-1) 也未提供此证明。

### 4.1 最后一次原文接合：保留 10 月 24 日已经得到的更强纠偏

直接核对本地 May2020 IUT III 文本：cQ3/cQ4 在 8404–8499 行；closed loop 在 8525–8574 行；Remark3.10.2 的实际箭头在 9067–9147 行；IPL/evaluation/further rigidification 在 9683–9739 行；xi-d–xi-f 在 10823–10898 行。原文确实同时保留 local 和 global Frobenioids 及 localization；不能将它描述成仅有若干局部映射。原文的闭环也明确是在 formal quotient indeterminacies 意义下，不能直接改成原区域或原线对象上的恒等映射。

尝试按对象执行：固定任意合格 C，反设 h_C<Q_C；用原输出并集的 hull 和 Ob3 的权重、inverse reference、共同 M，得到目标列中的 determinant 线对象 D_H。q 给出线对象 L_q。cQ3 的局部对象必须带到 D_H,v 的 linear structure poly-morphism；pullback 将**已有**结构态射运输，并保留局部 Galois/单位作用。IPL 运输的是抽象 pilot 的同构类。要在固定目标 holomorphic realization 中据此排除 h_C<Q_C，仍必须识别实际算法给出的比较及其数值读出，不能仅把 transported abstract pilot 命名为所需局部子格。

这里必须接续 `C9-LOCAL-GLOBAL-DESCENT-ATTACK`，不能停在较早 `CONTRADICTION-ATTACK` 第6节：cQ3 的 local-global collection 列出了局部结构态射、全局对象及 localization 同构，却没有仅凭这个对象清单自动产生同一条全局有效 linear 态射。旧文的具体检验是在 Q 上取

    L_3=3 Z_3, H_3=9 Z_3；其他有限处均为 Z_p；无穷处均为 [-1,1]。

各处有局部 linear 同构（3 处乘3，其他处恒等），但不存在同时满足有限处积分条件及无穷处范数条件的非零全局乘子：它须是非零的 3 的整数倍且绝对值 ≤1。这个例子只否定弱接合引理，没有实现完整 IUT 输入/算法；不能反驳原文完整闭环。

同一旧文已经给出实际可计算的账本。将所有数据放入同一标准算术 realization，记 native q 与 determinant/reference 端点的除子为 alpha、beta；给定局部 linear 乘子 a_v 的有效余量为 Z_v≥0，采用旧文符号约定：

    alpha_v + Z_v = beta_v + div_v(a_v),
    A=(div_v(a_v))_v,  kappa=deg(A),  S=deg(Z)≥0,
    h_C - Q_C = S - kappa.

这是实际局部包含式逐处取 degree 的结果，不是对 kappa 的任意赋值。共同 M 及 degree normalization 要同时除回。若乘子确实来自一个全局实化有理函数，product formula 给 kappa=0；但 `C9-MARKED-IMAGE-DESCENT` 已按用户要求撤下了“必须先证 kappa=0”的强要求：原标量比较只需从实际源算出 S≥kappa，或者构造另一项真实源输出越过坏容器。精确 q-output attainment、每条原始分支保体积、所有局部比较全局下降，都不是该不等式的必要前置。

所以最后的原文核对没有补出 C1。本包能明确排除的循环是：先用任意局部同构把 L_q 装进 collection，再把 collection 的存在当作原全局 inequality。真正的 full-strip 等价若能在同一标准全局/局部模型中识别，可能提供额外约束；FrdII Remark5.6.3（3371–3378 行）在全部局部系数群为 Z 时确实给 degree=1。但目前没有把实际 sQ3/sQ4 的 formal-quotient 返回比较证明为这个定理所要求的等价，不能直接调用。该适用性责任与 10 月24日旧文第8节一致。

### 4.2 一处此前“自然语言已推导”的具体错误

`C9-CAN-A3-COMPATIBILITY-DERIVATION` 的 cQ3 Step3 声称：局部线丛平凡化后，单位作用便经过主单位的商、成为根单位作用。这不成立。已经平凡的 Z_3-线 Z_3 上，单位4仍以乘4作用；取任意正 M 次 tensor 后作用为乘 4^M，仍不是恒等。线丛平凡化不使单位表示平凡。并且 `O^{×mu}` 是单位模根单位的对象，不能替换成单位模主单位的有限商。因此不能复用该文件的 “cQ3: derived” 作为完整证明。

其 cQ4 Step2 将 vertical shift 当作 log-shell 中的普通平移，同样没有从原文构造得到；10 月24日的小单位探针已经说明 pointwise log 的迭代域会出问题。原文 cQ4 是带 log-Kummer correspondence 和允许迭代 indeterminacy 的结构相容性，不能用这个平移说法替换。本次没有据这些旧草稿的错误否定原论文的 cQ3/cQ4。

LANA 原报告 §9.2 的 (9-1) 要求对适合的**实际** integral structure S 比较 eta^q 与 eta^anab_S；§10.3 要在同一侧、取 degree 前比较构造。其目标已经按等体积区域取商，不要求点集相等。§10.5 明确尚无证明，也不判定为显然错误。因此 LANA 与本仓库源 gate 指向相近的对象/读出相容责任，但未经双方对象和 normalization 的逐项对接，不能宣称“(9-1) 与当前 Lean C1 已证等价”，更不能称完整 IUT 中的 C1 逻辑独立或不可判定。

## 5. 用旧数值作单侧证书，是否真能补 gap

原目标只要求 `Q_C <= h_C`。为了得到下界，**不必先证明 q 区域本身是一个输出**；可以找别的实际允许子族，使它的最终 hull 读数已达到 Q_C。这条路线早已在 10 月 18 日与 `C9-TC-EQUALITY` 中出现，本包直接复用。

若一个真正源允许的子族在原目标 hull 内给出

    h_C >= L_fin(C) + h_inf(C),

那么 `L_fin(C)+h_inf(C) >= Q_C` 就足以完成该 C 的比较。若有任意精度的同类下界，则用 epsilon=(Q_C-h_C)/2 的反证即可。证明中只消费一侧包含；不要求该子族穷尽所有输出，也不要求 exact attainment。

但这里的 L_fin 不能自由指定。下表**只复用旧 uniform-profile 的同一局部数值约定**，不把它标成已识别的论文全局 Q/Theta，也不混用 C9Paper 的 canonical/normalized 因子。设 p=12301、e=41、m=20，`b j²=41 s_j+t_j`，1<=t_j<=40：

    Q_p/log p = -b/41,
    L_A/log p = -(sum_j s_j)/20 - 1/41,
    L_B/log p = L_A/log p + 420/41.

| b | Q_p/log p | L_A/log p | L_B/log p | (Q_p-L_A)/log p | (Q_p-L_B)/log p |
|---|---:|---:|---:|---:|---:|
| 3 | -3/41 | -411/41 | 9/41 | 408/41 | -12/41 |
| 273 | -273/41 | -39156/41 | -38736/41 | 38883/41 | 38463/41 |

这些数字可以对应真实**局部**元素：沿旧 Tate 构造，取 `K=Qp(pi)`、`pi^41=p`，取普通 Tate 参数 `q_Tate=p^(2b)`，则 `qhat=pi^b` 是其 82 次根。b=3 或273均有 3|b、41不整除b；p−1 被 6、4、41 整除，故这些局部 Tate 曲线有相应根单位、全 6-torsion，41-torsion field 是 K。这里没有构造完整 global initial Theta-data，也不改变全称目标的原任意输入。

**b=3 的具体答案。** 如果较大的 B=I 分支真正来自同一 C 的允许作用，并且 source-to-target / reference 条件已核实，则 L_B−Q_p 是

    (12/41)log12301 = 2.7563226845... .

因此在这个已认证子族的其余加权贡献满足 `h_rest >= -2.7563226845...` 时，下界确实填上这一实例的 gap。若只讨论旧的一坏素数简化，则 h_rest 就是该简化中保留的 archimedean 项。这是精确充分条件，不是本包已构造的分支或无穷处下界。`C9-ADJUDICATE-HAFULL` 已说明 full Out 是否移动 `O_K/J` 的直线未决定；不能任选 B=I。

**b=273 的具体答案。** 同一子族即使取较大分支，仍需补

    (38463/41)log12301 = 8834.703284644... .

它只说明这一候选证书不够。由 `h_C >= L_B+h_inf` 得到的是 `Q_C-h_C <= Q_C-L_B-h_inf`，正的右边不证明左边为正。不能恢复旧“b=273 反例”。

进一步，在同一公式内 b→b+41 时，每个 s_j 增加 j²，故 L_A、L_B 都下降 `(287/2)log p`，Q_p 仅下降 log p，证书亏损增加 `(285/2)log p`。更换 Haar 常数和多取共同 tensor power 均不改变这个差。这里直接利用既有公式，不重复大规模 p=12301 枚举；它也不控制完整输出族的其他分支。

附带保留一处原记录更正：`C9-NL-MASTER` Corollary 5.2 中将 `h_C <= Q_C-epsilon` 写作 P6 proof 所需条件的句子方向相反。这一式会证明失败；P6 需要足够的下界 `h_C >= Q_C`。同文件 Theorem 2.1/其余正确方向继续复用。

## 6. 收束与下一项

1. A1/A2/A3 的 Input-boundary 证明保留，已豁免的 OriginalInput→Input 不恢复为本任务前置。没有证明完整 IUT 中 C1 的逻辑独立性。
2. 完整 C1 尚未解决。本文给出了 arithmetic hull/Haar/reference 运输的完整自然语言证明，修正了“环同构仍可任意改变相对体积”的说法；没有把它冒称 final-evaluation compatibility。
3. 不再寻找把整个 degree-faithful value-monoid hull 同一化为有限 IQ hull 的映射；已有 top-volume 障碍排除这个特定任务。论文的无穷值分支应在正确扩展读数中单独处理，不能转成 toReal=0。
4. 下一包沿既有 `IND1-GLOBAL` SD4 / TC-A,B,E,F 接续，不把较早 `CONTRADICTION-ATTACK` 的 collection 出口恢复成充分条件。对已有 uniform-profile 子族，首先核实 B=I 能否由固定 C/gluing 下的真实 procession/Kummer/evaluation 分支实现：写出原算法诱导的局部区域、比较乘子和 reference，使用现有 arithmetic transport 计算 delta，并按 `LOCAL-GLOBAL-DESCENT` / `MARKED-IMAGE-DESCENT` 保留全局 S、kappa 与无穷处贡献。若该分支不能实现，不再使用其数值余量。对全称目标须证明这些真实数据给 S≥kappa，或构造坏容器下的实际 escape；不能以定义差值重写成这条式子充当证明。若输出/q的秩不同，使用原相对 determinant line，不强迫它们是同一向量空间的点集。这个源任务尚未完成，本文不把重新定位它计作关键突破。
5. 这是一个现有 source 箭头的证明任务；不新增 `FinalEvaluationCapsule` 的自由字段，不再证明 `membership + readout + bound => Q<=h` 的包装。登记在同名节点仅为追踪现有缺口。

本次验收：自然语言算术证明做 root 自审；五个窄范围 Lean 文件复跑均 exit 0，`C1FiniteHullObstruction` 复现标准三公理。没有运行 comparator、Project build 或独立审查；没有新 Lean/生产定义改动。证据路径和 SHA256 见同名 EVIDENCE JSON。C1 的 `stage1=open`、`target_accepted=false`。

## 7. 自然语言证明路线：用完整 prime-strip 闭环过 hull/carrier gate

本节是一次新的、固定对象的证明尝试；它不把 xi-f 当作证明前提，也不把任意局部 maps 拼成全局 map。要证明的实际标量式固定为：对原文任意一份合格完整配置 `C`，保留原 `q_C`、Theta-gluing、procession、行列权重和 normalization，令 `P_C` 为该配置真实 multiradial evaluation 输出的并集，`H_C=phi(P_C)` 为原文 holomorphic hull，`h_C=nu(H_C)`、`Q_C` 为原 q-pilot 的 signed log-volume；证明 `Q_C <= h_C`。不把输出换成另一份 C，也不把 q 的线丛换成一个人为选取的等体积对象。

### 7.1 对象与局部 hull

1. 固定 `C` 及原始各处分解。实际局部载体是 IUT III Theorem 3.11(i)(a) 的
   `IQ(S^±_{j+1}; n,◦D^vdash_{v_Q})`，即实际有限张量/乘积局部域上的 `Q`-张量包；它带原文给出的 mono-analytic integral structure `I(...)`、procession-normalized log-volume 和局部 `O`-作用。它不是 Lean 里的整个 degree-faithful value monoid，也不需要从那个无界载体造有限等价。
2. 对真实输出并集 `P_{C,v_Q,j}`，按 Remark 3.9.5(i) 定义 `H_{C,v_Q,j}=phi(P_{C,v_Q,j})`：若并集相对紧，`H=lambda O` 是包含它的最小 holomorphic hull；若非相对紧，原定义就令 hull 为整个 `IQ`。在反证 `h_C<Q_C<+infty` 的分支，后一情形有无限 Haar log-volume，故只能落在 `lambda O` 分支。于是实际 integral carrier 和 hull 都已由原文对象给定，没有再加一个自由的“共同 carrier”字段。
3. `H=lambda O` 对 `O` 的乘法稳定，因此可取原文 Ob3 所需共同正整数 `M`，把 hull 的相对 determinant 送入 rank-one arithmetic line/Frobenioid 对象；q-pilot 一侧取同一 `M` 次 tensor power。这里是 determinant 的函子性，不是假定两个不同秩向量空间有点集双射。逆 reference、每个 `j` 的权重和 procession 平均都继续使用 C 的原数据。

### 7.2 全局兼容箭头

4. 先保留 prime-strip 全结构，不先取 log-volume：从固定 q-pilot 的 `F^⊩▶×μ` prime-strip 出发，沿 Remark 3.10.2 的 evaluation/Kummer 方形和 Theorem 3.11(iii) 的 IPL 合成走。`sQ1/sQ2` 是实际 evaluation/Kummer full poly-isomorphisms；`sQ3` 是上述 hull determinant 与 `⊼` formalism；`sQ4` 是通过 log-Kummer 在同一 vertical column 调整 shift。Remark 3.9.5(ix) **单独断言**这条含 `sQ1`--`sQ4` 的链闭合到 formal quotient；本证明不声称仅由 cQ3+cQ4 推出闭环。
5. cQ3 的关键作用不是“有一个 local-global collection 所以存在全局箭头”。它把 hull determinant 的结构态射保留为局部 Frobenioid 中的 linear-morphism orbit，并在 collection 中同时保留 global realified Frobenioid 对象及每个 place 的 localization isomorphism。沿第4步使用的是同一条 full prime-strip 链的 global component，再由 pullback/determinant 函子性运输这些既有 localization squares；所以候选是一个由固定 C 的 source arrows 诱导的兼容 collection/morphism。10月24日反例排除的只是“任取各地局部箭头，再随便配一个全局对象”的推理，不排除这条确有 global component 的闭环。
6. cQ4 说明 `sQ4` 的 vertical adjustment 由 log-Kummer correspondence 自身实现；允许原文所说的任意 log-link iterates 后，单位/Galois 结构仍在同一 quotient-compatible diagram 中。随后用 Ob9 的实化半简化：log-link 两端 hull 的 log-volume 有自然双射。因此该步骤只传输标量读数，不宣称原始区域或线丛在两个 column 中相等。

### 7.3 degree 与不等式

7. 由第4--6步，所需的具体 source lemma 应是：固定 C 的 q-pilot 全局 line，经同一个闭环和 `det^{⊗M}` 后，得到一个**真实** hull-side Frobenioid 对象 `D_C` 及与所有 localizations 相容的结构态射 `D_{q,C} -> D_C`；它的 Frobenius degree、global degree 和 reference 都由这条 full equivalence/arrow 计算。它不是任意新假设：构造必须逐项使用上述 sQ arrows、Ob3/cQ3/cQ4 的 pullback squares 以及 source q object。FrdII Remark 5.6.3 在实际相关标准 poly-Frobenioid 的所有 `Lambda_v=Z` 时给 global degree 比例 `1`；若该适用条件成立，`M` 次 tensor 后两边 degree 同乘 M，除回 M 的 procession-normalized 读数不变。Proposition 3.9(iii) 再把 global degree 识别成各处原权重 log-volume 的和。
8. 若两端在选定的原参考下写成局部除子账本，不能略去 reference 修正：逐处包含给 `alpha_v + Z_v = beta_v + div_v(a_v)`，全局化后

       h_C - Q_C = S_C - kappa_C,   S_C=deg(Z)>=0.

   第7步的**同一个全局 morphism/equivalence**决定 `a_v`、全部参考和 degree 因子；故可以实际计算并证明 `S_C>=kappa_C`。若它来自一个全局实化有理函数，product formula 可给更强的 `kappa_C=0`；本路线不把 `kappa=0` 当必要条件。任意局部 `a_v` 则不能引用 product formula。
9. 第5步的结构态射方向是 hull-side inclusion/有效 Frobenioid morphism，因此它给出的 q-side datum 是 hull 中的真实 structured object/approximant。依 Remark 3.9.5(iii)，每个允许的 hull approximant 都包含于 canonical hull，log-volume 单调，故其读数不超过 `nu(H_C)=h_C`。第6--7步把 q 的读数保到该对象上，得到 `Q_C<=h_C`。若 source 只给任意精度近似，取 epsilon=`(Q_C-h_C)/2` 即与反设矛盾；此时须有实际输出见证和 signed 误差，不能只用抽象 supremum。

### 7.4 此路线的状态，不隐藏证明责任

上面是一条有数学内容的、非循环的证明路径：它绕开“把整个 value-monoid hull 映成有限 IQ hull”，也绕开从 cQ3 collection 对象任意拼全局箭头；它用的是实际 IQ carrier、full prime-strip global component、determinant functor、degree 和 hull 单调性。它说明 A1/A2/A3 不是该标量比较的先决条件；已接受的 Input 边界仍可固定为 C1 的源边界，不重开 `OriginalInput -> Input`。

但第7步 `D_{q,C}->D_C` 还须在论文对象上逐项验证，才能把路线报成已证。当前仓库的 `SourceFTimesMuPrimeStripPolyIsomorphism.lean` 与 `SourceKummerEvaluationArrows.lean` 明说 provenance/source-link factorization 是 reduced conditional interface；它们没有构造完整 global realified Frobenioid 与 actual output hull determinant 的同一兼容 collection。因而本节给出的是**可直接检验的自然语言证明候选**，不是对既有 Lean 接口的完成声明。最小验收就是：从 Theorem 3.11(i)(c) 的 global component，沿 Remark 3.10.2 / IPL / sQ3,sQ4 构造该 morphism；核对 localizations、degree、M 与原 reference 后得到 `S_C>=kappa_C`。如果只能提供逐处箭头和一个无关 global object，则本证明在此处失败，10月24日的局部—全局反例仍适用。

因此纠正此前“缺少 source-to-IQ carrier”的过宽说法：**原论文已定义真实 IQ/O carrier、hull、determinant 和 degree 读数；Lean 侧未构造它们与 q/full-strip output 的忠实接合。** 数学目标 C1 仍 open，`target_accepted=false`。xi-f 可作原文结论的引用，但不能代替第7步的独立箭头核验；cQ3+cQ4 也不能单独当作 full-loop 证明。本轮没有添加 Lean 代码或运行编译。

### 7.5 本节候选的自审：不能把第5、8、9步读成已成立的 source 推导

本节首次写下的“由同一 full global component 运输已有 squares，所以候选有 global morphism”仍须区分**范畴之间的等价**与**范畴内部两个指定对象之间的态射**。等价可以运输一个已给定的态射；它不从无到有产生 q-line 到 hull determinant 的态射。第5步只有前者的函子性成立；后者仍是第7步要核验的责任。第8步的“故可以实际计算并证明 S>=kappa”和第9步的 q-side datum 读数也是该待证构造的后果，不是已经完成的证明。即使是 degree-one 的范畴等价，也还要识别其携带的 pilot 标记与实际 hull-side 输出之间的关系。

因此这条全局态射路线是原 C1 的一个**充分方案**，不替换原目标，也不恢复“必须先证 kappa=0”的旧强要求。单侧源下界、有限分支共同 hull 或实际 escape 继续是可用出口。尤其不把“若接受 xi-f 则闭合”算作 C1 的解决：xi-f 已含待证结论。

有限 packet 的表述也需守住范围：上述局部代数证明在选定有限维块上适用；原文同时使用 ind-topological objects 及 Remark3.9.7 的 inverse systems。不能仅由逐块有限体积推出全系统的统一界。无穷处另用实际度量区域，不能套用 p-adic 格公式。下面的结论没有要求把完整 APT 变成一个线性映射；Remark3.11.1(iv) 明确排除这种一般解读。

## 8. 实际尝试：单位作用能否强制 hull-carrier 兼容

任务仍是 `n8-c9-final-evaluation-capsule` 的阶段1；root 单人。消费者是 §4/§7 候选 source arrow 的局部 hull/reference 检验。写本记录、两个既有节点与 evidence，STATE/queue/AUDIT 只追加；不改 Lean。复用 `C9-NEW-TANNAKIAN-TRACE`、`C9-U-LINE` 中对 trace/固定线的纠错，不再把对称 trace form 当 symplectic form。以下 elementary proof 为本次 root 自推，不宣称论文或 Mathlib 已提供源实例。

### 8.1 可完整证明的局部命题

设 E、E' 是有限 étale Qp-代数，O、O' 是它们的整数闭包；T:E→E' 是 Qp-linear bijection。对 x∈E，记 m_x 为“乘 x”的线性算子。选 n>=1。假如对每个 u∈1+p^n O，T m_u T^{-1} 都是 E' 上的某个**乘法算子**，那么存在唯一 Qp-代数同构 sigma:E→E' 和 a∈E'^×，使

    T(x)=a sigma(x),   a=T(1).

注意前提是乘法表示的交织；“有抽象单位群同构”或“对 Galois 作用等变”不是此条件。

证明如下。

1. 对 x∈O，有 u=1+p^n x∈O^×，且 m_x=p^{-n}(m_u-Id)。因此 T m_x T^{-1} 也是乘法算子，因为乘法算子的集合 m(E') 是 End_Qp(E') 的 Qp-子代数。每个 x∈E 经一个 p 的整数幂缩放都属于 O，故此结论对全部 x∈E 成立。
2. 共轭算子 B↦TBT^{-1} 是 endomorphism algebras 的同构；它把 m(E) 单射地送入 m(E')。两者的 Qp 维数都等于 dim(E)=dim(E')，故其像正好为 m(E')。乘法表示 x↦m_x 是单射，所以共轭唯一给出一个保持加法、乘法、1 和 Qp 标量的同构 sigma。
3. 令 a=T(1)。对任意 x，T(x)=T(m_x1)=m_{sigma(x)}T(1)=a sigma(x)。因 T 和 sigma 都满射，乘 a 满射；在有限乘积域中这意味着 a 每个分量非零，即 a∈E'^×。式子也证明唯一性。
4. sigma 保持 Zp 上整性，故 sigma(O)=O'；由 §2 的 hull 最小性，sigma 运输 holomorphic hull。乘 a 同样双射地运输 fractional-ideal hull，因此对本命题涵盖的实际区域 A，

       T(Hull_O(A)) = Hull_{O'}(T(A)).

5. 设 d=dim_Qp(E)。按单位参考作 signed Haar 读数，有

       nu(T(A);O') = nu(A;O) + log|N_{E'/Qp}(a)|_p / d.

   理由是 sigma 的单位相对 Haar 因子抵消，而乘 a 的 determinant 是 norm。若用实际参考格 R、R'，则统一使用 §3 的 delta_T=log(mu'(T(R))/mu'(R'))/d；不再重复加同一个 a 修正。证毕。

此命题排除了 §3 那类不交织乘法表示的剪切，却**没有**令 a 成为单位。a 在所有乘法算子的中心化子里；即使 T 与全部单位乘法都交换，也允许 T=p^k Id。因此“完整单位作用”在这个严格的线性模型中至多恢复 sigma 加一个乘子，仍未固定绝对参考格和体积。

这不是对完整跨 Theta-link APT 的线性模型假设。它仅测试一个已经构造的局部线性比较是否有足够信息；不能因 lemma 正确就给原 APT 强加它的前提。原 cQ3 通过 pullback 给对象的 Galois/单位作用，且 O^{×mu} 是模根单位的对象；从这些结构提取此处真实乘法表示及其 T，是尚未验证的应用条件。需要选取深的无 torsion 单位子群时，也须证明 quotient 表示的实际 lift，不能把 quotient 自动当成乘法表示。

### 8.2 即使局部单位兼容全部成立，旧全局缺口仍在

直接加强 10-24 已有例子：在 Q 的3处令 L_3=3Z_3、H_3=9Z_3，T_3(x)=3x；其余有限处 L_p=H_p=Z_p、T_p=Id，无穷处均取单位区间及恒等。每个 T_p 都与该处**全部**单位乘法交换，并是其局部线对象的线性同构；Galois 标量作用也相容。可是

    Q=-log3,   h=-2log3,   h-Q=-log3.

不存在使全部这些局部比较同时成为原全局线比较的非零有理数：有限处要求它是非零3的整数倍，无穷处要求绝对值<=1。若取实际全局乘子3，无穷处必须同时出现乘3的贡献，原单位区间便不能保持。这个补偿不能省略。该例仍然只反驳弱局部准则，不是完整 IUT 数据的反例。

因此 §8.1 确实解决了一个局部 hull 运输引理，但它无法独自关闭 C1；它把可以检查的残量精确留在 a、reference 及全局 localization 上。继续重复证明单位/局部 Kummer 等变，没有控制这项残量，就不能填 gap。

## 9. 原文中的标度检验：为什么“full strip 有全局部分”还不是结论

本次额外逐项读到的源定义：IUT II Definition4.9(viii)，本地文本 10293 起，pilot 由坏处 splitting-monoid 的生成元**连同 rho_v** 决定；morphism 是整份数据的同构。III Remark2.4.2(ii)--(vi)，本地文本 5123--5275，进一步给出 ordered Picard monoid 与 pilot 的重构。以下计算在这份明确的源子数据上进行，不把它扩大成完整 IUT 输入反例。

固定原文 r_v^triangleright（它们由原 C 的 places 和 q 数据给定）。令 M=R 为 ordered additive group，eta<0 为 pilot；原文重构的局部 N-单子为 N eta，而局部化为

    rho_{v,eta}(n eta)=r_v^triangleright n eta.

对任意 c>0，令 eta'=c eta。全局映射 x↦cx，局部映射 n eta↦n eta'，使全部这些局部化方形交换：

    c rho_{v,eta}(n eta)=rho_{v,eta'}(n eta').

它们保持顺序、单子结构和抽象 N 的生成元，但全局数值乘 c。故“局部单子抽象同构于 N/其群化抽象同构于 Z”本身并未校准 c=1。FrdII Remark5.6.3 所需的是 Example5.6 的**标准算术 poly-Frobenioids 及原局部化**，其中实际系数群为 Z；不能把上述随 pilot 变动的嵌入 n eta↦r_v^triangleright n eta 仅按抽象群类型认成该标准输入。这不否定 FrdII 的 degree-one 定理，也不证明完整带单位/Kummer 的 source 结构允许任意 c；它准确显示须在何处验证更强结构。

还有第二个责任：即使已证明某 full-strip 范畴等价 degree=1，它运输的是这份 strip **携带的 pilot**。必须证明经过实际 sQ3/sQ4 后，这个 transported pilot 位于原实际输出的 hull-side family；仅有同一个 ambient Frobenioid 不保证这个事实。III Remark2.4.2(vi) 明确说同一 common container 中可以比较不同的负 pilot；III Remark3.11.1(iii) 的最后 evaluation 又引入各种 further rigidifications，不能未经核对将其中一个直接命名成固定 q 的刚化。

若实际源计算确实给出 transported pilot 的读数 r=cQ，且其到 H 的真实扩大余量为 S=h-r>=0，则

    h-Q = S+(c-1)Q = S-(c-1)|Q|   (Q<0).

这说明所需条件是实际源给出的 S>= (c-1)|Q|，而不是必须 c=1。该式只是对已给 source arrows 的数值检查；不能反过来定义 c=r/Q 或 S=h-r，再假称已经由源证明了比较。例如 Q=-1、r=h=-2、c=2、S=0，交换的缩放方形本身与失败的不等式完全相容。这里只是源子数据的标度诊断。共同 tensor M 和同时运输参考不改变该差的符号。

### 9.1 已经可以消掉的箭头，以及第一个不能消掉的箭头

给 Remark3.10.2 三个下横箭头依次命名 L0,L1,L2，上横箭头命名 U0,U1,U2，四个竖箭头命名 K0,...,K3，按从右向左的函数复合记号，交换方形给 `U_i K_i=K_{i+1} L_i`。IPL 指定的复合因此满足

    U2 U1 U0 K0 L0^(-1) L1^(-1) = U2 K2.

逐次用第0、第1个方形消去即可；在 full poly-isomorphism 语言下读作相应允许同构类的相等，不凭空独立选互不相容的代表。II4.9(viii) 的 pilot 是 splitting generators 与 rho 的函子性构造，故这些**实际 full-strip 同构**运输对应 pilot 的同构类。这项自然性可以复用；它不提供从输出 hull 中选出该 pilot 的新箭头。

| 源步骤 | 实际对象/箭头类型 | 本次核验到的边界 |
|---|---|---|
| Remark3.10.2 / IPL | full prime-strips 之间的同构、其交换方形 | 上式消去成立；pilot 同构类由完整结构运输 |
| sQ3 / Ob3,cQ3 | 区域取 hull、determinant；局部 linear structure maps；local-global collection 与 formal quotient | 已构造对象可比较；仍须把固定 q 的 transported pilot 与实际 hull 的结构 maps 接起来 |
| sQ4 / cQ4,Ob9 | 同一 column 的 log-Kummer 调整及 quotient 层读数比较 | 未制造前一行缺失的内部态射；source 允许的迭代/读数必须保留 |
| sQ5 / Prop3.9(iii) | 已识别对象的 degree/log-volume | 可读已有比较的数值；不能反过来创造比较 |

沿全局态射这条充分路线，第一个具体待填的方形是：实际局部结构 map `u_v:D_{q,v}->D_{H,v}` 及原 localizations `lambda_{q,v},lambda_{H,v}` 要满足

    loc_v(g) lambda_{q,v} = lambda_{H,v} u_v

其中 `g:L_q->D_H` 的 global component 必须是源构造出来的同一个 map，且使用原 degree、共同 M 和 reference。cQ3 给出了何谓这样的兼容 morphism，未凭定义给每一个 collection 一个到 H 的 global map。若采取较弱的单侧路线，不必构造 g，但仍须用真实输出区域/乘子证明足够余量；不能把这个方形再包装成新输入。

方向性判断：已证明的 A1/A2/A3 wrapper 无需重做；一般局部 hull/Haar 兼容已有证明；下一项只展开上表 **sQ3 接合**：把 II4.9(viii) 的同一个 splitting generator 与 rho_v 从 IPL 的 `U2 K2` 输出带到实际 hull determinant，分别标出“输入 q 携带的 pilot”与“按输出重新重构的 further rigidification”。在取 degree 前构造这两者的实际比较，或从源允许扩大得到足够下界。sQ4 随后保留原校准；不再泛查 sQ1/sQ2 或数值调参。这与 LANA 要在同一侧、取 degree 前比较的责任相呼应，但未建立两种完整陈述的等价。

本轮最终状态：§8.1 局部自然语言 lemma 完整；§8.2--§9 排除了两项不充分推理，并固定了下一条须展开的标记/局部化方形；**没有**得到原任意 C 的比较、反例、独立性或不可判定性。C1 继续 stage1=open、target_accepted=false。root 自审；此次无 Lean 编译、公理检查、comparator、Project build 或独立审查。之前五个文件的 compile 证据保持原范围，不当成本节验收。

## 10. 单 agent：把 carrier 路径实际跑到第一个断点

本节直接回答“能否自然语言跑通 hull-carrier compatibility gate”。结论必须分两层：**论文 carrier 与 determinant 的对象级兼容已经由原文构造；固定 q-pilot 的读数进入这份输出 hull 的 source-marked 兼容性仍未由前述构造推出。** 后者是 C1 所需的关键内容，不能因为前者已建立便报告 gate 关闭。

### 10.1 从原文对象得到同一比较范畴

固定一份原文合格配置 `C`，保留其 q-pilot prime-strip、Θ-link、procession、权重、参考对象和 normalization。对每个 `v_Q,j`，Theorem 3.11(i)(a) 给实际的局部 IQ tensor packet 及 mono-analytic integral structure；算法的 possible images 是这些 packet 中的区域，而不是当前 Lean `SourceVolumeIndex` 的任意非单位缩放单子。

令 `P_{v_Q,j}` 是这些实际输出区域的并。按 Remark 3.9.5(i)，若它相对紧，`H_{v_Q,j}=phi(P_{v_Q,j})=lambda O` 是包含它的最小 holomorphic hull；若不相对紧，定义的 hull 是整个 IQ packet。于是有限 `h` 的分支使用原文的 `lambda O` hull；无穷读数分支不伪装成有限 `ENNReal.toReal`。由 Ob1--Ob2，有限 hull 对 `O` 作用稳定，因而定义 arithmetic vector bundle。Ob3-1/2 取与原权重相容的共同 `M`，并按原文以 `O(-)` 的 determinant 作 inverse-reference 校准；得到 rank-one arithmetic line object。cQ3 的 pullback 给出其局部 Galois/unit action 及 localization 数据。这个构造把 hull-side object 放进 q-pilot 所在的 codomain local/global Frobenioid 体系，所以两者可比较；它**没有**说两个对象相等或存在 q 到 hull 的态射。

再按 Remark 3.10.2 的交换图沿 IPL 复合。以图中记号，复合约化为 `U2 K2`；Definition II.4.9(viii) 的 splitting generators 与 `rho_v` 对 full-strip 同构自然，所以固定 q-pilot 的同构类确实随之运输。Ob8/cQ4 随后在原允许的 log-Kummer 迭代下调 vertical shift；Ob9 和 Proposition 3.9(iii),(iv) 只在这些已识别对象之间运输 hull log-volume / global degree。有限地方的 arithmetic-algebra 同构保持整数闭包与 hull，Haar 缩放在以 `O` 为 reference 的 signed log-volume 中抵消；reference 改变时保留 §3 的精确有限指数修正 `delta`。这条链证明了“对象在哪里、采用何种 determinant/reference、哪些标量读数相容”，没有把不同秩 bundle 当成同一向量空间的点集。

### 10.2 要推出标量比较，还差哪一箭

把固定配置的实际允许输出读数记作 `R_C`，完整输出 hull 的上界记作 `h_C`。由 hull 单调性和正确校准，只能先得

```text
    r <= h_C  for each r in R_C.
```

要推出 `Q_C <= h_C`，还须证明 `Q_C in R_C`，或给出真实的 source-allowed 读数 `r_epsilon` 使 `Q_C-epsilon <= r_epsilon <= h_C`。在局部除子记账路线，等价的足够证据是从实际 source arrows、references 和 weights 算出 `h_C-Q_C=S_C-kappa_C` 并证明 `S_C>=kappa_C`；不必强求 `kappa_C=0`。也可交付真实 hull 扩大/escape。不能从“同属一个 Frobenioid”推出以上任一结论。

### 10.3 唯一性/范畴论路线的核验

尝试的捷径是：full-strip 同构运输 pilot；pilot 由 splitting generators 和 `rho_v` 唯一决定；于是固定 q-pilot 必属 final evaluation 的 further-rigidification 输出。第一、二句成立，第三句没有从定义跟出。Remark 2.4.2(v)--(vi) 说的是：给定一个负 pilot element 后，可重构同一个 global realified Frobenioid 的相应“进一步刚化”，且不同负 pilot 可在共同容器中比较。它没有定义 final-evaluation 的允许刚化集合为全部负元素，也没有说 q-pilot 是该受限集合的成员。Rmk 3.11.1(iii) 说 evaluation 产生“各种”由 pilot/Indeterminacies 决定的可能刚化；从“各种可能”到“包含这个指定 q-mark”仍是所需接合，不能用唯一性消去。

同理，cQ3 给局部带 structure-poly-morphism 的对象及 local-global collection 的结构；它不为任意 collection 产生一条同源的全局态射。10 月 24 日 `LOCAL-GLOBAL-DESCENT` 的 `Q/3` 算术例只排除这个弱推理，不是完整 IUT 反例。完整闭环另由 Remark 3.9.5(ix) 在 source 中断言；xi-f 又单独断言 q-readout 落入 `R_{<=h}`。若把 xi-f 作为已接受的源结论，则顺序/集合定义立即给 `Q_C<=h_C`；但这时是引用兼容性目标本身，不是从 cQ3、IPL、唯一性独立证明该 gate。不能把它说成新推导，也不能据此否定原文。

### 10.4 结论与唯一下一步

自然语言证明实际跑通到：

```text
固定 C
 -> 原始 IQ/O 输出 carrier 和 hull
 -> det^M + inverse-O(reference) line in the q-codomain Frobenioid
 -> full-strip IPL 运输 q-pilot 同构类
 -> sQ3 的 hull structure-poly-morphism / local-global data
 -> [此处未证：固定 q-mark 落入 final-evaluation 允许刚化/同一 structure-poly-morphism]
 -> sQ4 读数校准
 -> signed degree/log-volume inequality
```

因此，**paper-carrier 类型兼容这一子问题已由原文定义和 cQ3 解决；完整 hull-carrier compatibility gate/C1 尚未解决。** 当前 Lean 的 `sourceHullVolume=top` 诊断仍只排除该 value-monoid encoding，不能外推为论文 IQ/O hull 不存在；也不应为了通过 gate 再造整个 value hull 的等价。

下一实际动作只做一件事：对同一个固定 `C`，从 II.4.9(viii) 的 `eta_q` 沿已核实的 IPL 复合 `U2 K2` 追踪至实际 evaluation 的 further-rigidification 集合及 sQ3 的 structure-poly-morphism，写出其真实局部化方形、共同 `M`、`O(-)` reference 和读数；证明 q-mark 是该**受限 source 输出**的成员/有符号逼近，或给出达到 `Q_C` 的真实单侧输出见证。若该 source object/箭头在原文现有定义中没有构造，再报告这一个具名缺口；不重新证明载体 arithmetic，不使用 xi-f 作前提，不改 C1 的量词。

本节仅为原文对象和既有记录的单 agent 自审；没有 Lean statement/proof/kernel、comparator、Project build 或独立审查。C9 child node stage1 继续 open，`target_accepted=false`。
