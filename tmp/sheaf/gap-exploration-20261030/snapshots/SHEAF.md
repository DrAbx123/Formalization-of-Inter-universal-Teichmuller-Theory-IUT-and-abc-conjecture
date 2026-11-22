# IUT 项目的 SHEAF 工作方法

生效：2026-10-22。来源：[frenzymath/SHEAF](https://github.com/frenzymath/SHEAF/tree/6e5abd804e1b0c8d4626349e3508103c97452711)，Scalable Hierarchical Engine for Autonomous Formalization。本文是针对现有 IUT 仓库的中文适配，不是上游脚本已安装的声明。

## 1. 从目标向下找路，从定义向上写陈述，从目标向下证明

SHEAF 把三种不同的工作分开：

| 阶段 | 方向 | 交付 | 进入条件 |
|---|---|---|---|
| 1：自然语言 DAG | 从目标向下 | 对象明确的命题、来源、完整证明步骤、依赖及 Mathlib 查找结果 | 与目标有可解释的关系；未知关系先核对 |
| 2：陈述形式化 | 沿陈述依赖自底向上 | 真实定义、可编译的完整定理陈述、目标快照 | 本节点阶段 1 完成，陈述依赖已形式化 |
| 3：证明与剪枝 | 从目标向下 | 证明体、实际依赖更新、删去无用 imports、闭合验收 | 该目标已锁定，所用证明依赖已有准确声明 |

这三个阶段按节点推进，可以重叠。不需要先画完整个 IUT 的图才做一处明确工作，也不需要先证明所有底层猜测才检验上层是否需要它们。已有证明直接复用，不先改回 `sorry`。

**旧的“前置没有全部证完就禁止写上层证明体”不再是活动规则。** 新规则允许在显式待证定理上尝试上层证明，借此检验接口和剪枝；这样的结果仍是带缺口的形式化，不计为闭合证明。

例：目标 `T` 的陈述需要对象定义 `D`，原计划证明要用 `A`、`B`。先把 `D` 定义准确，把 `A`、`B` 写成准确陈述，再尝试证明 `T`。如果 Mathlib 的 `C` 直接给出 `T`，删掉不再使用的 imports，`A`、`B` 离开这条目标的证明队列。无需先把 `A`、`B` 全证完。

## 2. 目标锁定必须包含定义的含义

[GOAL.md](GOAL.md) 区分最终目标、原文目标候选和局部里程碑。每个目标要记录完整变量、量词、假设、结论、原文位置，以及定义到 Mathlib 的对应。

锁定过程：

1. 找现有声明，核对实际定义；不复制同义目标。
2. 核对原文的所有全局假设和结论，记录在 [coord/targets-review.md](coord/targets-review.md)。
3. 陈述可编译且语义无已知缺陷时，建立目标快照 `coord/targets/Challenge.lean` 和仅导入目标实现的 `coord/targets/TargetsCheck.lean`。这两个是将来应生成的文件，本轮未伪造空快照。
4. 快照只引入陈述所需定义；最终证明闭包不得导入带 `sorry` 的 Challenge。记录目标 elaborated type 和定义依赖版本。
5. 修证明可自由换路线；改变最终目标需要用户指令。改变目标引用的定义，即使 elaborated type 文本不变，也重新审查语义。

仅将目标写成 `SomeCard → Result` 不能消掉构造 `SomeCard` 的义务。但原论文本来允许的初始数据是合法假设，不要反过来强迫证明更强的“从任意弱输入构造全部初始数据”。

单人完成的包可以做有记录的自审，但不能冒称独立审查。需要独立语义复核时，给审查者冻结目标和定义版本，按文件交接/稳定快照审查；记录审查者与限制，不因此暂停其他可独立推进的节点。

## 3. DAG 中的两类边

一节点一个 JSON；布局和状态见 [dag/README.md](dag/README.md)。

- `statement_dependencies`：没有这些定义/声明，目标的类型就无法准确表达。例如有限 étale 覆盖范畴的定义。
- `proof_dependencies`：证明路线实际要用的结果。例如用不变量代数构造商。

每条边记录依据和状态。自然语言路线中的边标为 `planned`，现有源码可见调用标为 `observed_source`，真正核对 Lean 依赖后才标为 `verified_lean`。候选关系保留在节点的 `candidate_connections`，不当成已确认依赖。

不能把以下东西当依赖证明：文件名、Source/Actual 后缀、Project 的 import、相同术语、一个汇总合取。也不能因为文本检索未命中，就宣布某数学结果必然无用。

每个非叶子命题在阶段 1 完成前，必须有完整自然语言证明步骤，逐步标明所需节点或初等推理。只写“标准”“用下降”“由刚性”仍是缺口。找不到证明时记录 `gap` 或 `statement_disputed`，不凭空生成可供下游使用的卡片。

依据实际读到的论文/引用写证明，记录版本、页码和本地或网络位置；先复用已有文献。未取得原文时注明缺失，agent 自写的证明明确标注来源，不把记忆或摘要当作逐项原文核对。文献存在也不等于 Lean 依赖已证明。

Mathlib 叶子要保存准确声明、适用对象/假设、搜索记录和版本。现有项目定理是可复用供体，但不能仅凭过去编译成功把它标成 Mathlib 叶子或当前版本已验收。

## 4. 陈述阶段允许什么样的缺口

允许：**具名定理**的 `sorry`，配有来源、完整陈述、自然语言证明及 DAG 节点。它表达一个已确定的证明责任。

不允许：

- 用 `sorry` 随意制造实际域、曲线、覆盖、theta section、作用或 fiber functor；
- 把“构造需要的对象/等价/自然性”直接写成自由字段，再将可 inhabit 当成源忠实性；
- 把缺口变成新 `axiom`、弱化量词、附加不具备的假设；
- 用没有证明方案的 conjecture 填充库，制造虚假的阶段 1 完成状态。

真实定义可以引用一个准确具名的未证定理，例如从待证双射性定义逆映射；必须登记这项证明依赖，所有下游一并保持未闭合。定义的数据含义不能由任意 inhabitant 决定。

本仓库适配：新增陈述阶段内容先在 `tmp/sheaf/<任务>/` 的明确文件中试验，使用独立 namespace；复用现有生产定义和定理，不复制整套库。正式进入生产库须连同目标闭包、缺口登记及依赖影响一起审查。已有验证通过的证明不因迁移被退回 `sorry`。

区分四种事实：

| 状态 | 可以说什么 |
|---|---|
| `statement_compiles` | 陈述在当前定义下可编译，可能含 `sorryAx` |
| `proof_body_checked` | 本定理的证明体检查通过；传递依赖仍可能未闭合 |
| `kernel_closed` | 对当前完整依赖版本完成构建/公理检查，仅允许 `propext`、`Classical.choice`、`Quot.sound` |
| `target_accepted` | 还通过锁定类型比较及源语义审查 |

不把源码中搜不到 `sorry` 等同于 `kernel_closed`；不把 `kernel_closed` 等同于论文命题已忠实形式化。合法条件定理可以闭合，但其条件的实际构造状态另列。

## 5. 如何选择下一项，避免大量无用基础工作

每个执行者维护其任务需要的局部图，组负责人审查相关接口，维护者汇总 DAG 和就绪队列。root 负责目标和全局策略，不逐个重新派发 worker 的后续任务。优先处理：

1. 会使当前目标本身错误的陈述/定义争议；先反例和范围核对。
2. 当前可执行目标附近的证明尝试，尽早判断哪些下游分支可删。
3. 为这些目标准确陈述所必需的定义和局部证明缺口。

“离目标近”指依赖关系，不指文件夹名。给一个现有消费者，说明该结果消掉其什么前提；尚未确认的连接先做一次有界调查，不能据此展开整个基础理论。

开始一包前填 [任务模板](coord/TASK_TEMPLATE.md)：目标节点、实际对象/量词、消费者、原文位置、陈述/证明依赖、精确文件和验收出口。已有记录包含的内容直接链接；不要重写长篇背景。只有对象、量词、原依赖或版本变化时才重查旧结论。

没有目标可达的数学保留为离线储备，不分配证明任务。DAG 不可达性只能据已核实的图判断；当前局部图未覆盖的文件标 `unclassified`，不能一律判成无用。

## 6. L0.3：按实际 G2 消费者切分

当前相关里程碑是实际所需基底 `S` 上：

```text
∀ G [Group G] [Finite G],
  HasColimitsOfShape (SingleObj G) (FiniteEtaleCover S)
```

这是数学规格，正式冻结时必须用现有声明的完整 universe、范畴实例及基底范围。对每个有限群的**任意作用图**构造余极限；regular、free、trivial action 不足以完成它。

目标拆分围绕如下证明用途，不按已有文件夹逐个“补齐”：

| 节点用途 | 需要交付 | 剪枝机会 |
|---|---|---|
| 原作用图的商 | 同一覆盖范畴中的 Cocone、投影和 IsColimit | 仿射底已有足够强的普遍性时，不额外证明 all-Scheme-target |
| 仿射商的代数核 | 实际截面作用下 `Spec(Γ(X)^G)` 有限 étale | 复用 general invariants/M1；不重新堆 rank decomposition 的替代版本 |
| 源消费者连接 | 实际 scheme/orbicurve 覆盖范畴及几何 fiber 的自然比较 | 已有真实等价可直接运输；不复制 G2 证明 |
| 上层使用 | 填实际源基本群证书所需字段 | 不新建仅合取旧结果的 ProjectLayer 包装 |

若 `S ≅ Spec R` 已有真实证明，优先尝试：实际 cover `X` 的截面作用 → 不变量代数 → 原 `X` 到商的投影 → 在原 cover 范畴的唯一分解 → `IsColimit`。因子分解的 over-base 方形可用已有对 `Spec R` 的唯一性比较两条复合，未必需要一般 scheme epi 理论。

这条短路线只适用于它实际覆盖的基底。源 sign quotient 可能是非 scheme 可表示的 orbicurve；不能因 scheme 的 G2 通过就删掉该对象的下降/范畴比较。

现有核对证据：[consumer_trace.md](tmp/l03-direct-consumer-audit-20261022/consumer_trace.md)。那里已区分：

- `y²=x³−x` 是已定位的测试模型，不再反复审计；generic 商理论不依赖这个方程。
- `SourceOncePuncturedGeometry` 的 signature 条件不构成实际源曲线识别。
- `ProjectLayer03Consumer` 的合取输出不构成源 GaloisCategory 的接入。
- scheme G2 → 源 orbicurve/fiber，以及 native → 旧 3.11 contract，是两条不同连接。

因此下一包应在已有实际范畴上完成一项可调用的商/比较，不把 L0.3 扩成“构造所有源输入”。具体哪一项先做由当前代码和原文的缺口决定；本迁移没有宣布这些数学已经完成。

## 7. L0.4 / L0.5 按相同规则处理

L0.4 的目标节点写实际 `B ≃ C`、实际未缩放 log、全体单位/元素的自然性方形，再按消费者添加 `e_L`、同一剩余素数的缩放和 log 像限制。`Q_l` 与 concrete `Q_5` 的模型条件必须出现；不能让“保范数同构”成为未构造自由字段。已有路线有用，但不是已证状态。

L0.5 的 source Theta-link 仍有陈述阶段之前的工作：实际 `AΘ`、divisor/单位、`Mq → MΘ`、根/deck 歧义、tempered 同步要先从原文固定对象、作用和量词。把这些登记为阶段 1 的精确缺口；不先填一个 ThetaLink card 再向上推。

Point uniformization 的目标保持自然参数乘法和原曲线群律；`X(u)=x` 只要求对实际曲线点 `(x,y)`。不以搬运定义的群律、常数 action 或全域 X 满射替换原目标。

原数学笔记继续作为证据入口：[N8/source Theta 交接](logs/coordination/n8-theta-link-handoff-20261020.md)、[L0.4 指导](logs/coordination/l04-implementation-playbook-20261021.md)、[较短路线草稿](logs/coordination/l0-shorter-routes-20261021.md)。其中历史流程规则已被本文替代；事实和未证草稿不被抹除。

## 8. 实作、构建和剪枝

先复用 [低级任务自动化](tools/LEAN_AUTOMATION_USAGE.md)。相同版本错误不重复入队，大模型不承担读重复日志、路径修复和缓存判断。实际证明任务按 [SHEAF 分组调度](coord/SCHEDULING.md) 并行：维护者管理队列/集成，各组认领并续领任务，没有固定 agent 或组数上限；足够多的独立任务可以支持数百执行者。可变文件、审查/构建吞吐和真实资源决定当次规模。本次 chat 的单线程要求仅约束此次文档编辑，不是项目规则。

已有 `lean_auto.py` 是闭合证明/机械检查工具，可能把 `sorry` 作为 policy failure；这不等于 SHEAF 的陈述非法。陈述阶段使用真实 Lean 编译并单独记录 `statement_compiles`，不能改工具输出把它伪装成 `green`。具体命令与边界见 [SETUP.md](SETUP.md)。

证明落地后：

1. 核对证明实际用了哪些声明，更新 proof edges；自然语言图中的猜测边不是 kernel 证据。
2. 删除该证明不需要的 imports，检查实例、notation 和传递导入是否仍被下游使用。
3. 编译受影响文件/消费者；陈述或定义变化时检查所有受影响的已登记消费者，必要时扩大构建。
4. 从 `TargetsCheck.lean` 的 imports 计算阶段 3 候选队列；再用声明依赖和语义复核缩小范围。当前未生成 TargetsCheck，队列只能明确标为手工初始队列。
5. 不再从任何已登记目标可达的节点退出活动队列，保留节点及退出原因。不自动删除旧证明文件；撤下 import 后仍需检查其他目标。

若现有模块同时含需要和不需要的声明，模块可达不意味着其中所有 `sorry` 都应优先证明。先精确识别目标用到的声明，必要且有收益时才拆分；不要为规避验收只隐藏 import。

批次末由唯一构建负责人做约定的完整构建。构建失败记录真实原因；不要把已通过的生产证明改成 `sorry` 只为让树变绿。多个数学任务可以并行，共享构建产物仍须统一管理；采用隔离快照并行构建前，先实际落实产物与发布隔离。

超时先区分资源、依赖重建、elaboration、tactic 搜索和定义展开。上游的 60 秒预算可作调度参考，不是“超时一定是定义错误”的数学事实。

## 9. 完成标准与交接

最终接受要求同时满足：

- 对应源码/依赖版本的绿色构建；
- Lean comparator 对锁定 Challenge 的实际验收，记录版本、命令、退出状态和产物；
- 目标的传递公理仅为 `propext`、`Classical.choice`、`Quot.sound`；
- 原文目标及其引用定义的语义审查仍有效。

比较器未运行就写未运行，不能用正则匹配或 `#check` 代替。当前没有安装或验收比较器，本轮只有方法论迁移检查。

每包结束更新 [coord/STATE.md](coord/STATE.md) 的当前状态、节点和 [coord/queue.md](coord/queue.md)，在 [AUDIT_LEDGER.md](AUDIT_LEDGER.md) 追加一次有信息量的记录：实际消掉的缺口、精确证据、仍缺什么、剪掉了哪些分支。研究中发现反例、有效捷径或失败路线时及时追加，不等到上下文丢失才回忆。

节点 JSON 保存当前事实，不复制历史；历史保留在 git 和追加日志中。交接不以文件数、行数、agent 数或 `sorry` 减少量计进度。

## 10. 相对上游的适配与替换范围

保留上游三阶段、两种依赖、目标锁定、证明剪枝和最终双重验收。作以下明确适配：

- 现有工程就在 `D:/lean`，不迁到嵌套 `lean/`，不升级 Lean/Mathlib。
- 保留 SHEAF 的总协调、维护者、组负责人、执行者分工；规模小可合并角色，规模大按独立任务扩组。没有固定 agent 人数、组数或五层树，也不强制所有 worker 扁平挂到 root。简单文档编辑不分派，局部单线程要求不成为项目限制。
- 不为每个旧声明拆一个 Lean 文件；DAG 可以逐声明映射到既有模块，只有实际收益时拆分。
- 先在隔离的陈述试验文件使用具名 `sorry`；不破坏已有证据，不把修复失败自动改成生产 `sorry`。
- 复用现有机械工具，队列先手工维护；不声称上游 claim/landing/build/comparator 工具已经部署。
- 活动日志沿用 AUDIT_LEDGER；不另造一套重叠历史库。

上游参考：[DAG](https://github.com/frenzymath/SHEAF/blob/6e5abd804e1b0c8d4626349e3508103c97452711/template/stages/1-dag.md)、[陈述](https://github.com/frenzymath/SHEAF/blob/6e5abd804e1b0c8d4626349e3508103c97452711/template/stages/2-statements.md)、[证明剪枝](https://github.com/frenzymath/SHEAF/blob/6e5abd804e1b0c8d4626349e3508103c97452711/template/stages/3-proving-and-pruning.md)。旧活动方法论已原字节归档，见 [迁移清单](coord/sheaf-migration-20261022.json)。
