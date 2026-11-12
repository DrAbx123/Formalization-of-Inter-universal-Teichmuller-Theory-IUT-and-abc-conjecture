# N8 目标与输入定稿：源输入、实际区域、有符号读出

日期：2026-10-23。依据用户要求继续闭合 N8，本文件决定当前目标/输入的修正方向，不再等待旧候选 A/B 选择。数学目标仍是原文源 3.11、IPL/SHE/APT、实际 hull/degree 比较与源 3.12；不退为结构闭合或单地方条件模型。

**决定：采用 C0/C7/C9 职责分层，但同时更换旧输入入口、旧 hull/volume 载体和 C9 读出。拒绝继续在旧 `OriginalInput` 上要求无条件 `SourceInputBinding`，也拒绝以 `SourceHullLogBound` 修补旧 0/top 模型。**

本文冻结的是实施规格和数学范围。新的 Lean 总签名尚未实现/编译，`target_accepted` 和机器目标 `locked` 不能据此置为 true。执行者可以按下列规格重建，不需再次询问这两条路线选哪条；改原文结论强度则仍需另行决定。

## 1. 旧 C0 退出活动目标，新总目标保留全部数学内容

旧 `N8TargetOutput` 绑定 `sourceHullVolume`，同时要求有限与正。生产定理 `sourceHullVolume_eq_top_iff_exists_pos_logDegree` 和全非正时等于零的定理，确认了这个值模型的 0/top 边界。此结论保留为反例/模型审计，不再给旧 `n8_targetOutput_nonempty` 填证明或 sorry。

不采用候选里的 `SourceHullLogBound` 替代：它仍在同一个旧幺半群 hull 上限制 degree；即使界成立，也没有变成论文的实际 Haar log-volume。有限相会落到旧零值分支，不能据此取得源 3.12。

新职责是：

| 层 | 定稿职责 |
|---|---|
| C0 输入 | 原文合格初始 Θ-data，以及在它之上的真实、依赖索引正确的 theater/log-theta-lattice |
| C1 | 从该输入读取地方和真实局部对象；证明需要的 strip/局部表达比较，不再读取一个任意外部 V |
| C3/C4/C5 | 构造源 pilot、实际允许选择及算法输出，证明 IPL/SHE/APT 与 Ind 相容 |
| C7 | 实际源可能像的 holomorphic hull，及必要局部块的 Haar 质量正有限性 |
| C6/C8 | 同一实际区域的有符号归一化 log-volume；独立定义的 arithmetic degree 与该值比较 |
| C9 | 实际 q-pilot 数值在源算法输出中的实现/逼近，以及到 theta hull 的上界 |
| C10 | 从 C0 合格输入构造全部结果，证明 `Q ≤ Θ`；不得把 C1/C2/C3/C5/C7 等待证结果全部留作最终定理参数 |

C0 不必承载所有体积字段，但 N8 总目标不能因此删去有限性、实际 3.11 内容、算法相容或 degree 比较。模块职责拆开不等于削弱最终命题。

## 2. 输入定稿：从原文的选定地方开始

原文 I Definition 3.1(e) 的 `V` 是 `K` 的地方子集，是限制到 `F_mod` 的一个 section，并与 `V(F_mod)` 双射。它不是任意 `Type`，也不是 `K` 的全部地方。

现有可复用入口是 `SourceNativeInitialThetaData l`：

- `S.arithmetic` 给出算术塔；
- `S.tuple.source.V : Set (NumberFieldPlace S.arithmetic.K)`；
- `V_section`、`V_eq_section`；
- `V_mod_bijection : NumberFieldPlace S.arithmetic.Fmod ≃ {v // v ∈ V}`；
- `V_place_comap` 证明上述双射符合地方限制；
- `V_mod_bad_nonempty` 给指定坏地方的非空性。

这些字段见 [SourceDefinition31Quantifiers](../LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean)，特别是 605–618、1640–1648。它们是已经存在的输入定义；本轮不声称整份 native contract 的所有几何语义已经验收。

### 新输入的形状

拟议新输入以这份 `S` 为根：

```text
S : SourceNativeInitialThetaData l
V(S) := { v : NumberFieldPlace S.arithmetic.K // v ∈ S.tuple.source.V }
L : 原文在 S 上的 theater / log-theta-lattice
```

`L` 必须依赖同一个 `S` 和 `V(S)`；所含对象/箭头按原文给定结构逐项定义。上述是规格，`L` 的完整 Lean 类型仍需落地，不能用任意 `Type` 或 `SourceInputBinding` 别名充当实现。

保留原文已经给定的合格初始数据和 lattice；不要求为了证明 3.11，先从任意弱算术记录构造它们。当前 `SourceHodgeTheaterFamily` 的抽象字段，尤其 q-preserving 的旧 `HodgeTheaterLink`，不能自动认作原文水平 Θ-link。

### C1 如何分解

1. `V(S) ≃ NumberFieldPlace F_mod` 直接复用 `V_mod_bijection.symm`。到旧 `NumberFieldPlaceIndex` 的适配另做有限/无穷地方表示转换；它不再是任意 V 的存在问题。
2. 全局结论量化所有所需地方。局部定理显式接受实际 `v`；若需一个坏地方，从原文坏地方非空性选取。不能用单个 selected place 代替全地方结论。
3. 局部完成域取正确塔层的地方，例如选定 `v` 给 `K_v`，并记录到 `F_v`、`(F_mod)_v̲` 的限制/扩张关系。不能默认它们是同一个完成域。
4. 从实际局部结构构造 strip 分量或其规定的商/群化/实化，再证明比较。旧 `.Mon v ≃* Multiplicative ℤ/ℝ` 不能原样塞入输入：先确定 `.Mon` 究竟是整个乘性幺半群还是已经取了单位商的值群。
5. `selected_realization : I.SourceImageRealization selected` 从新输入边界移除。它是旧逆向实数值模型的接口，不是原文 Definition 3.1 的输入。

新到旧的忘却/适配可以在需要复用旧定理时构造；**不要求先证明任意旧 `OriginalInput` 都能提升到新输入**。原有 native→legacy 总桥不是新 N8 输入的先决门槛。

## 3. C7 定稿：正性作用于 Haar 质量

对源构造确定的实际局部区域 `H` 和 Haar 测度 `μ`，证明：

```text
0 < μ H
μ H < ⊤
```

然后定义并使用：

```text
Vμ(H) = (log ((μ H).toReal) - log ((μ O).toReal)) / D.
```

参考格子 `O` 同样需要正有限质量，`D` 是实际局部块的正维数。这是有符号实数；不要求 `0 < Vμ(H)`，也不要求 `0 < ENNReal.ofReal Vμ(H)`。

### 当前 actual-IQ 也必须改的一处

`SourceHolomorphicHullData.logVolume_pos` 当前要求 `B.iqInterface.logVolume ... > 0`。该 IQ 接口在有限质量时使用 `ENNReal.ofReal (log μH)`，负 log 会被截断为零；此正性依赖 Haar 尺度，不是论文所需性质。

例如 `μ(ℤ_p)=1`、`H=pℤ_p` 时，`μH=1/p` 正且有限，但 `log μH=-log p<0`，截断值为零。因此**不能把 C0 里的错误正性要求原样搬进 C7**。

actual-IQ 的局部域、张量块、Haar 定理可以保留；对论文的有符号读出不再通过上述非负 log 接口。

### H 必须来自源可能像

当前 `commonHull := B.hull`，而 `C6ActualIQData.actual.hull` 是仅由 places/tuple 决定的 canonical hull；它并不按 C4/C5 的源可能像求 hull。

新目标使用：

```text
U(S,L,n,...) := 源算法全部许可选择的实际像
H(S,L,n,...) := paperHolomorphicHull U(S,L,n,...).
```

canonical hull 可以作为容纳区域。如果要用它替代 `H`，必须证明本包需要的等式/比较；不能先定义二者相等再宣布 source hull 已构造。可继续复用 `LocalFieldProductHull` 的最小 λO-region、相对紧性和质量定理。

## 4. C3/T11 定稿：实际值先于实数读出

新链的方向是：

```text
实际源曲线 / theta section / Kummer 数据
  → 在正确局部域或代数闭包中的值/类
  → 实际张量落点或区域
  → norm / valuation / signed log-volume.
```

不再把“构造一个 Real theta → completion 的字典”作为必要研究目标。实数尺度已经忘掉单位/根等信息；应先构造实际值，然后证明其规范化读出与 theta packet 对应。旧 `FiniteThetaPacket` 是待比较的尺度摘要，不是局部元素的来源。

`qUnit ^ gaussExponent j` 可保留为候选表达式；其与实际源 theta 特殊值、列参数和允许歧义的比较仍须证明。当前 T11 的 `thetaScale_eq` 与 `thetaImage_eq` 没有把 completion 元素的数值读出与 `thetaScale` 联系起来；`Nonempty SourceThetaIQInterface` 因而不关闭源 theta 比较。

### 另外必须修正 roots 的域

当前 C3 把 `NatRootSystem qUnit` 放在原数域地方的完成域内。`NatRootSystem.pow_self` 要求每个正整数次根都存在。对离散 valuation 的有限局部域和 `ord(q)=r>0`，这要求 `N * ord(root N)=r` 对所有正整数 N 成立；取 `N>r` 即不可能。

所以根系应在正确的代数闭包/原文规定的扩张中构造，q 从基域映入；随后给出实际 Galois action、Kummer cocycle 和 root-change，再处理需要的下降。现有 `AlgebraicClosureRootSystem.rootSystemOfAlgClosed` 已提供正确域上的通用根系供体。

此处给的是离散赋值的数学诊断，本轮未新增 Lean no-go 证明。无需继续为旧完成域内的全阶根系找 inhabitant。

`FinitePlaceQCandidate` 只保证非零且收缩；真实 Tate/source q 的曲线识别责任保留。不能把任意 uniformizer 当成所需 q。

## 5. C6/C8/C9 定稿：Q、Θ 和 Values 各有独立来源

### C6/C8

保留已经证明的局部定义恒等式：

```text
normalizedLogVolume(H)
  = normalizationWeight * (signedHullLog(H) - unitReferenceLog).
```

让其作用在 C7 实际 `H` 上，复用一般定义，而非固定 canonical hull 的别名。C8 当前 `rfl` 完成的是这个恒等式；原文 arithmetic line bundle 的 degree、相对 determinant、权重和 tensor power 必须有独立构造及比较定理，不能把 `iqDegree := normalizedLogVolume` 当作 Ob3-3 已证。

局部归一化、IV Remark 1.7.1 的地方/tuple 权重、III 的 procession 平均全部保持。局部、全局、标签索引不得混成一个 `finrank`。

### C9 的两个端点

- `Q(S,L)`：由实际 q-pilot 的区域、原文权重和同一归一化计算。
- `Θ(S,L)`：由实际 theta 可能像的 hull、同一套权重和归一化计算。

原文 q 侧 `−|log(q)| < 0`。当前 C9Actual 的 `-log ‖q‖` 在 `0<‖q‖<1` 的约定下是正的局部高度；不能未经符号/尺度定理直接当作这个 signed Q。源 q 区域的 signed log 及其与局部 norm 的关系必须单列证明。

### Values 与总不等式

当前 `iqSignedHullLogAt ... n := B.signedHullLog`，故当前 `Values = range muLogAt` 是单点集，且 `actual_q_approximated` 使用同一 hull 的 degree 而非实际 q。它不是原文的 q 逼近问题，旧定理停用。

新 `Values` 必须是源算法允许输出/允许输出区域的数值像，保留真实见证，独立于最终结论定义。固定同一配置后证明：

```text
∀ y ∈ Values(S,L), y ≤ Θ(S,L)
∀ ε > 0, ∃ y ∈ Values(S,L), Q(S,L) - ε ≤ y
```

由此推出 `Q(S,L) ≤ Θ(S,L)`。若直接得到 Q 的实际成员见证，可取代逼近。禁止定义 `Values := {Θ}` 或 `Set.Iic Θ` 后用自由假设满足它；也不预设 q 点属于 theta hull 作为输入。

当前上界写成“任意 n 的值都 ≤ 每一个 n 的 hull log”还会强制所有这些值相等。新的每个配置有自己的 `Values` 和 `Θ`；只有证明列间值相同后才重索引，不能靠全称量词抹平列差异。

## 6. 索引与最终总签名

严格区分：

- theater 列/竖直层 `n,m : ℤ`；
- 原文有限标签/符号商标签 `j`；
- finite procession 前缀、tensor factor、地方 tuple 的各自类型。

`ThetaPilotCarrier l` 的有限索引不能代替所有 `n,m : ℤ`。标签使用有限集合及其置换作用；不把人为 `AddGroup Label` 作为论文原输入。

新总目标的数学规格为：对原文合格的 `S,L`，构造实际源 3.11 输出和 IPL/SHE/APT，构造所需实际区域、degree/log-volume 比较，证明 theta 值有限并得到源 `Q ≤ Θ`。涉及所有原文地方/标签/列的量词保留。

辅助 `assemble` 可以显式接受已证 C1–C9 数据；最终定理必须在其证明体内由 `S,L` 调用构造/存在性结果。现在 C10 的 `n8Assembly_closure` 仍接受 C1/C2/C3/C4/IPL/C5/C7 参数，应保留为条件装配供体，不作为无条件 N8 最终定理。

## 7. 输入边界清单：什么可以给定，什么必须证明

| 项目 | 放在哪里 |
|---|---|
| 原文 Definition 3.1 的合格数据、V section、坏地方条件 | 新 C0 合法输入；用实际依赖类型表达 |
| 原文 3.11 所处的给定合格 lattice/theater 结构 | 新 C0 合法输入；不得用旧 q-preserving family 偷换 |
| 由 V section 读出地方双射、选坏地方、建立正确完成域 | C1 构造/推论 |
| 具体 strip 与局部表达的算术比较、必要商/群化识别 | C1/C2 证明义务，不能仅为补旧类型放进输入 |
| 实际 log/Kummer 动作、根系和 source q/theta 比较 | C2/C3/T11 构造与定理 |
| possibleImage、IPL/SHE/APT、Haar 质量界、degree/log-volume 比较、Q≤Θ | 输出/证明义务，禁止移入新输入 |
| 任意较弱算术数据都能产生上述合格输入 | 另一项更强构造任务，不作为当前论文条件定理的额外门槛 |

每项输入约束必须指向原文定义，不设自由 `Prop` 加一个 proof 字段代替明确含义。native 的局部供体可直接复用，但整个 native+family 的语义仍按本表逐项核对。

## 8. 接下来执行的修正包

1. **C0/C1 owner：**建立以 native selected places 为索引的新签名，读出地方双射，撤掉外部任意 V 和旧 selected_realization。先编译这一个接口切片；不等所有源证明完成。
2. **C3/T11 owner：**把根系改到正确扩张，实际 q/θ → 张量 → 实数读出；使 theta 的读出比较成为明确命题。不要再证明弱 `Nonempty` 接口。
3. **C7/C6 owner：**从实际 `U` 定义 `H`，改证 μ(H) 正有限，signed log 取相对参考格子；固定 canonical hull 仅作有证据的容纳对象。
4. **C8/C9 owner：**保留一般归一化定理，分开真实 degree 比较；用实际 q 和允许输出重写 Values/逼近目标。
5. **C10 owner：**消费新源结果，保留全部原文量词，生成总目标依赖清单及实际调用；编译、逐项原文审查后冻结新的 Lean target 版本。

旧 C0/C1/C3/C7/C9 定理和错误目标保留 no-go 历史，停止作为新目标依赖。旧接口的正确条件供体不删除；旧编译成功不能转移为新版本的验证。

这几个包按文件及稳定接口并行，不需要先把整个 Layer0 重做一遍。独立的源数学证明继续；受错误类型影响的叶子重定目标，不在旧假命题上循环。

## 9. 本次证据与状态

本轮检查了 [TargetSignature](../tmp/sheaf/n8/closure/TargetSignature.lean)、[SourceInputBinding](../tmp/sheaf/n8/closure/SourceInputBinding.lean)、[C7](../tmp/sheaf/n8/closure/SourceHolomorphicHull.lean)、[C8](../tmp/sheaf/n8/closure/SourceDegreeComparisonIQ.lean)、[C9](../tmp/sheaf/n8/closure/SourcePilotApproximationIQ.lean)、[C10](../tmp/sheaf/n8/closure/N8Closure.lean)、[T11](../tmp/sheaf/n8/closure/SourceThetaToIQ.lean)。根系供体在 [NatRootSystem](../LeanFormal/IUT/IUTII/Kummer/NatRootSystem.lean)。

原文定位：[IUT I](<../papers/motizuki_corpus/text/Inter-universal Teichmuller Theory I.txt>) Definition 3.1，特别是 3123–3226；[IUT III](<../papers/motizuki_corpus/text/Inter-universal Teichmuller Theory III.txt>) Theorem 3.11、Remark 3.11.1、Corollary 3.12；[IUT IV](<../papers/motizuki_corpus/text/Inter-universal Teichmuller Theory IV.txt>) Proposition 1.4(i)、Remark 1.7.1。原文比较含糊处回核 PDF，不用摘要代替公式。

实施方向：**已决定**。新 Lean 签名、存在性及全部源证明：**待相应包实施和验收**。本 chat 仅修改决策/路线记录，没有改其他 owner 的 Lean 源码、没有重新编译，也没有宣布 N8 闭合。
