# Working Principles for This Project

## 1. Work Incrementally

- Do not repeatedly re-audit the same ground. Inspect what is needed for the current task and move the proof forward.
- The IUT project is very large. No single agent can hold the entire project in mind or control it globally. Work through focused, concrete patches that improve the current area.
- Keep changes as small and local as the task allows. Preserve working code and avoid unnecessary rewrites.

## 2. Keep an Append-Only Research Log

- Take notes frequently and record research as soon as it produces a useful fact, decision, failed attempt, or proof result.
- The purpose of notes is to know exactly what was changed and why. Do not erase earlier notes and replace them with a new summary; that destroys history.
- Treat the notes as an external memory. Do not rely on being able to remember complex investigations later. Before starting related work, consult the existing notes and reuse their conclusions.
- Add new entries to the existing record. Correct an earlier conclusion only when there is clear evidence, and preserve the superseded entry with an explanation of the correction.

## 3. Respect Verified Mathematics

- Reuse previously established lemmas, definitions, and proof strategies whenever possible.
- Minimize overturning earlier conclusions. In Lean, code that compiles is a proved theorem; do not disturb such code without a specific mathematical or engineering reason.
- Prefer a narrowly targeted patch over a broad refactor, especially in code that already compiles.

## 4. Follow the Steps Completely

- Work in an explicit sequence: understand the local context, state the next subgoal, make the smallest useful change, compile it, record the result, and then proceed.
- Do not skip difficult steps or hide unfinished work behind presentation. When a step is hard, investigate it and overcome the difficulty directly.
- The goal is clean, completed mathematics and maintainable Lean code. Either do the requested work or state plainly that it cannot be done; do not substitute decorative process for progress.

## 5. Use Deliberate, Distinguishable Names

- Every definition, theorem, lemma, proposition, structure, namespace, variable, and supporting declaration must have a meaningful and distinguishable name.
- Choose names that communicate the mathematical object or result and fit the naming conventions already established in the surrounding code.
- Do not use arbitrary, vague, disposable, or collision-prone names such as `foo`, `bar`, `test`, `tmp`, or unexplained numeric suffixes.
- Before introducing a name, check the local namespace and nearby files for existing declarations and choose a name that cannot be confused with them.
- If a temporary name is unavoidable during exploration, replace it with a precise permanent name before considering the work complete.

## 6. State Claims Precisely and Proportionally

- Never expand a theorem, method, hypothesis, or project result beyond what has actually been proved or tested. State the exact assumptions, objects, and scope.
- Be honest about whether a conclusion is strong or weak. Do not present a local, conditional, or partial result as a general, definitive, or project-wide result.
- Treat generalization as a mathematical claim that requires a valid, reusable argument. Do not claim broader applicability merely because a proof works in one instance; if the method is not known to generalize, say so.
- Research notes must be factual and proportionate. Record evidence, limitations, open cases, and failed attempts instead of using emphatic language or overstating progress.
- Do not use absolute progress statements or predictions such as "this is the final verification" or "all changes are complete" without concrete evidence that supports that exact claim.
- Describe status with verifiable facts: identify the files or theorems checked, the commands that passed, the cases that remain, and any uncertainty. Update the statement when new evidence changes the scope.

## 7. Do Not Build on Unproved Foundations

- Do not use an unproved theorem, placeholder declaration, `sorry`, fabricated axiom, or merely promised interface field as the foundation for later mathematics.
- An absent theorem is a real proof gap, not a component that can be made to look ready by reserving fields for it. Do not describe such scaffolding as progress toward a proved result.
- Prove every required theorem before using it as a dependency for the next step, and compile the dependent code against that actual proof.
- If the required theorem cannot yet be proved, record the precise mathematical gap and do not advance the dependent argument on a fictitious basis. Continue only with work that is genuinely independent and clearly separated from that gap.

## 8. Build Theorems from the Bottom Up

- Construct the theory in dependency order, starting with the definitions, propositions, and lemmas on which later theorems rely.
- Before proving or using a theorem, verify that every required assumption is stated precisely and has itself been proved or otherwise validly established in the current context.
- If any required assumption is false, unavailable, or unproved, stop the dependent line of work immediately. Do not continue by treating the assumption as if it were true.
- Prove or repair the missing assumption first, compile that result, and only then resume the higher-level theorem.
- Never build an upper-level theoretical model while any part of its mathematical foundation remains unsecured; keep independent work clearly separate from blocked dependent work.

## 9. 持久协作协议：启动与恢复前必须检查

协议标识：`iut-agent-tree/2026-10-13-v1`。

用户要求先安排全部层级与文件白名单，再开展项目工作。当前默认逻辑树为五级：
总协调 → 领域主管 → 模块主管 → 文件负责人 → 原子任务工人。
可以按实际职责增加主管层。GPT 主要承担上层判断，DeepSeek 可以接收明确的简单子任务。
逻辑节点不需要同时运行；尽可能并行，资源不足时持久化状态并轮流执行。

新会话、上下文压缩、重启、模型更换或恢复任务后，不能仅凭记忆或旧摘要开始工作：

1. 默认状态为 `NOT_READY`，先恢复协议及任务状态。
2. 根协调的默认启动白名单仅为 `D:\lean\agents.md`、
   `D:\lean\MULTI_AGENT_ARCHITECTURE.md`、`D:\lean\AUDIT_LEDGER.md`，
   以及第 13 节明确登记的根节点状态库。
   根协调读取本协议、架构细节及有关的最新追加记录；不因此获得其他文件权限。
3. 非根 agent 只能从唯一直接上级收到规则包和本节点状态包；
   不自行打开这些公共入口文件，不继承含其他 owner 源码的完整对话。
4. 在继续前，明确当前 `run_id`、稳定 `agent_id`、唯一 `parent_id`、角色、
   精确文件白名单及权限、任务/目标签名版本、已证依赖版本、检查点、待回复请求。
   此前没有登记的任务，由协调层先登记完整层级与权属后再启动。
5. 区分稳定的逻辑身份和当前执行实例代次；恢复前确认旧实例停止或失去执行权限，
   同一逻辑节点不能双活。更换模型不能只靠复用 agent_id 获得原 owner 权限。
6. 信息缺失、版本冲突或上次处于等待状态时，暂停受影响任务，向直接上级反馈；
   根节点在其权限内处理登记。不能通过全仓扫描、猜测或复读别人文件补齐信息。
7. 子节点回报恢复摘要，由父级核对持久登记并明确发送 `RESUME` 后才能继续；
   原先等待的任务仍需匹配请求的答复。根节点依据已记录的授权与状态恢复。
   授权变化先持久记录再生效，崩溃时结果不明的操作标记 `UNKNOWN`，不能猜测已成功。
   不得把尚未实施的设计当成已经可用的工具。

本文是持久规则入口，架构文档记录方案，审计日志记录历史事实。未来执行器应每次注入
并检查协议版本；不能只依赖模型自动记住，也不能假定每种客户端都会自动加载本文。

## 10. 唯一上级、文件独占与阻塞反馈

- 每个 agent 有且只有一个上级；根协调的上级是用户。跨分支联系沿父链经最近共同祖先路由。
- 每个文件在一轮协作中最多由一个 agent 读取或写入；上级无权复读下级源码来验收。
  白名单为少量精确路径，允许空白名单，不能使用目录通配符替代。
- 暂停、重试、失败、时间片结束都不释放文件所有权；不能通过新建 agent、更换模型、
  复制文件、转发全文/diff 或重建源码的片段绕过独占。跨轮交接另行明确登记。
- 同一文件的多个小任务由唯一文件负责人集成。原子工人可仅根据目标与已证接口返回新候选；
  需要实验文件时，先登记其独占路径，不能读取父级源码。
- 一旦需要其他 owner 的信息或变更，保存检查点并进入 `WAITING_FEEDBACK`，停止该 agent
  的实质工作。收到版本匹配的明确答复后再恢复；超时不是答复，也不是额外授权。
- 等待中的节点保留逻辑身份及所有权，但释放运行名额。其他独立节点可由主管调度。
- 所有日志遵守独占；子节点逐级报告，由指定日志 owner 追加，禁止所有 agent 共同写总日志。

## 11. 验收不能替换命题

- 任务先冻结完整变量、量词、假设、结论、依赖与版本。缺失前置证明时停止依赖分支。
- DeepSeek 或任何工人生成的内容均为候选；由文件负责人在冻结目标下集成与验证。
- 改前提、换对象、削弱结论后证明同名命题不算原任务完成。
- 编译证据须对应实际文件版本，检查公理与依赖边界；编译成功不自动证明论文忠实性。
- 上级通过精确接口与可信验证证据验收，不通过重新读取下级源码验收。

## 12. 当前实施边界与禁止虚报

截至本协议首次登记，交付的是架构及持久规则文档。DeepSeek API、自动调度器、
强制文件权限网关和隔离构建服务尚未实现；不得向后续 agent 宣称已经部署。
后续实际实施结果只能用新的验证事实追加到审计日志，再据此更新实施状态。

提示词不是强制权限控制。后续执行器必须在模型之外校验每次读取、搜索、修改与提交，
未登记或状态不符默认拒绝；不能给执行 agent 任意 shell 来绕过白名单。
编译器读取传递依赖的权限必须与模型可见权限明确区分；Lean 元程序及诊断输出也需要隔离。
在这个边界落实前，不能悄悄把全项目或所有依赖当成公共可读文件。

## 13. 第二层已实施：恢复入口与当前边界（2026-10-13）

第二层现已实现为 Python 标准库 CLI 加 SQLite：角色树、唯一上级、文件独占登记、
冻结任务契约、私有检查点、待回复请求、执行代次、事务事件及请求去重均已落盘支持。
独立黑盒检查 60 个断言通过；另验证了事务提交前强杀进程后的回滚与并发版本冲突。
第 12 节“首次登记时尚未实施”的记录保留；自动模型调度、DeepSeek、身份认证和
第三层源码/工具权限网关仍未实施，不能据第二层的状态检查宣称已经强制隔离。

根协调独占的交付状态库为 `D:\lean\logs\coordination\agent-state.sqlite`。
SQLite 内部旁文件仅允许同路径加 `-journal`、`-wal`、`-shm`，同属根协调的运行工件。
这些路径加入根启动登记；通过固定 CLI 操作状态，不让其他 agent 直接读取数据库。
程序加载其实现模块属于非模型执行，不授权调用者查看这些模块源码。

新上下文首先用以下只读调用取得最新 revision、generation、run_id、协议和契约指纹：

```powershell
'{"op":"inspect","actor_id":"@user","generation":0,"agent_id":"root"}' |
  python -B D:\lean\tools\agent_state.py --db D:\lean\logs\coordination\agent-state.sqlite
```

不得把日志中的旧 revision 或 generation 硬编码为当前值。随后按公开契约执行
`begin_recovery` → 唯一上级明确 `resume` → `start`，再进行已获授权的任务。
根上级的 `@user` 是可信本地操作员标识，不能当成新用户授权或真实身份认证；
依据现有用户任务授权操作。缺失数据库、协议不符或请求被拒绝时，先核对记录并反馈，
不得自动重新初始化、删除数据库或绕过检查。

交付 run_id 为 `coordination-state-handoff-20261013`。稳定 ID 与协作角色对应为
`root` → `state_supervisor` → `persistence_owner` → `scenario_owner`；
实际协作路径在审计日志中登记。源码 owner 分别为：state_supervisor 独占
`tools/agent_state.py`、`tools/AGENT_STATE_USAGE.md`；persistence_owner 独占
`tools/agent_state_store.py`；scenario_owner 独占 `tools/test_agent_state.py`。
上级获取接口与验证报告，不打开这些下级文件。

本状态库是已验证实现的交付/恢复记录，不代表未来任务已获授权或所有子节点已唤醒。
当前版本的角色树、文件归属、provider 和任务契约在一个 run 内冻结；若目标或权属
需要变更，先明确登记新 run 和独立库，保留旧库，不能直接改 SQL 或复用旧证据。
细节由模块 owner 根据 `tools/AGENT_STATE_USAGE.md` 的公开接口说明逐级提供。

## 14. 真实派发层级与压缩交接（用户明确纠正，2026-10-14）

根节点不得直接组装、启动或续接下级 DSH / DeepSeek 数学任务；“根仅作技术转发”
不能成为越级例外。任务必须由其实际直接上级拟定、经 DSH 派发并接收结果，再逐级
汇报。根只负责总目标、权属与资源协调、全树登记和主管公共证据汇总。

上级不读取下级源码、完整 diff、完整工具日志、私有检查点或用于重建实现的大量片段。
源文件唯一 owner 保留完整代码上下文。逐级上报压缩为所需对象/定义域、精确公开
签名、量词和假设、依赖版本、proved/candidate/gap状态、编译/公理/语义证据，以及
一个明确的版本化接口请求。不得因压缩而删去决定命题含义的假设或扩大已证范围。

所有 DeepSeek 委派使用现成 DSH；不要恢复自制API问答器。当前配置为
@deepseek-ai/dsh0.2.0-rc.2、deepseek-official/deepseek-flash（官方V4.1-Flash别名），
权限 danger-full-access、审批 never。全权限不取消层级、文件独占或反馈等待规则。
当前原生工具额度已经实际报告9（含root），不是旧4；应让已登记的独立分支实际
并行工作，等待节点释放名额，而不是只列一张团队名单。

最新纠正run为 hierarchical-lean-dsh-20261014。root独占其状态库
D:\lean\logs\coordination\hierarchical-lean-dsh-20261014.sqlite及SQLite旁文件。
完整树、各原生节点与外部DSH节点、精确文件归属及跨run日志移交见AUDIT_LEDGER.md
对应条目和状态服务公开元数据。其他节点仅调用获准公共API，不直接打开数据库。
先前根误派发的数学pilot已经退出；其三个结果日志已显式移交harness_supervisor独占
审查，根不得再读结果正文。新任务不得据旧pilot成功推断任何Lean命题已被证明。

## 15. 分叉、逻辑节点与执行名额（用户再次纠正，2026-10-14）

五层描述汇报深度，不是五个 agent；每层可以有多个独立分支，按真实任务继续扩展。
九个是当前原生同时执行名额（包含 root），不是逻辑节点总数，也不是 DSH 工人总数。
先登记全部已知树与精确白名单；后续发现新任务，先登记扩展，再启动受影响分支。
不得以旧树已经创建过九个节点作为持续并行的证据。

主管每次接收结果、进入等待、释放名额或恢复上下文时，必须检查本分支的可运行任务。
将任务状态与依赖逐项登记：可运行、执行中、等待哪个版本的答复、已验收、结果不明。
单个叶子缺接口不自动阻塞无依赖关系的兄弟任务；主管需要等待的事项应成为独立任务，
其其他新任务另立契约。不得在 WAITING_FEEDBACK 中偷偷继续同一被阻塞任务。
结束节点保留源码权属；新任务沿合法 owner 和父链登记新 run，不复开 FINISHED 契约。

根只收主管压缩报告和调度元数据；不得为了补位直接指挥孙级或 DSH。DSH 由直接上级
使用已配置 Flash4.1 调用，可以承担有充分上下文的证明探索、语义分析与复杂诊断；
不再把 DeepSeek 限定为短分类器，也不沿用旧自制调用器的 1024 token 限制。
任务多不等于实际 API 并发无限；按真实执行结果、容量和可验收工作逐批扩展。
汇报必须分别列出逻辑登记、实际执行、等待及完成情况，不虚报无人值守调度器已实现。

递归派发补充（2026-10-14）：subagent明确有权自行创建和调度自己的subsubagent，
后者继续遵守同样规则递归分叉。根先登记全部已知父链和权属，主管制定下级任务并启动，
不要求根亲自调用所有spawn；新增未知节点由主管提出并沿父链完成登记后自行启动。
用户随后报告已取消并发上限；实际可用容量以当次工具接受/拒绝为证，不把历史九名额
硬编码成永久限制，不以配置文字宣称已验证无限。

## 16. 分叉执行波的最新恢复入口（2026-10-14）

最新数学执行run为branching-lean-wave1-20261014，完整18逻辑节点的树/契约/精确文件
列表已在AUDIT_LEDGER登记并由状态CLI成功初始化。root独占以下新工件及SQLite旁文件：
- D:\lean\logs\coordination\branching-lean-wave1-20261014.sqlite
- D:\lean\logs\coordination\branching-lean-wave1-20261014-queue.jsonl（仅追加调度事实）

根恢复先对此库执行@user/root inspect取得当前值，不从文档硬编码revision或generation。
各下级只从直接parent收取规则和本节点状态；自行恢复，parent明确resume，再开始。
结构是root→math_supervisor→foundation/source_theorem/semantic三个模块主管→多个
文件owner→DSH工人。最后代数核值分支须等待前置实际证明，不得先写承诺字段。
旧hierarchical-lean-dsh-20261014与其他库保留历史等待，新的run不等于旧缺口已解决。
源码owner跨run延续，新实例启动前旧实例已停；父级仍不得读下级源码或日志。

状态CLI输入注意：本机曾将PowerShell UTF8管道按Python GBK/surrogateescape解码，
生成孤立surrogate使摘要计算失败。使用ASCII转义JSON（例如json.dumps默认ensure_ascii）
或显式python -X utf8，保留原目标内容。等值ASCII输运已通过18契约编码与init实测。
递归spawn已实测成功；超额恢复也实测收到agent thread limit reached，仍按实际反馈补位。

## 17. 数学困难时的文献补充策略（用户更新目标，2026-10-14）

仍尽可能复刻IUT原路线，目标不缩为条件模型或零散基础引理。可顺利推进的内容直接做，
不为检索而检索。遇到确切数学缺口时，可查近期OpenAI数学成果，或重点寻找较冷门、
较少被讨论的论文及边缘结论；不能把模型记忆当作穷尽文献的证据。
检索前由数学主管给出缺失命题、完整假设/对象/量词、原文定位及已失败路线，按唯一父链
登记文献分支及精确文件owner。原论文与外来结论都需核对适用条件，再以Lean证明接入；
存在论文或候选模型输出不等于已证明依赖。局部编译或类型错误不自动构成数学研究缺口。

## 18. 核心缺口优先、事件唤醒与机械恢复自动化（2026-10-14）

用户指出不能让一人实作、许多主管常驻观看。后续从IUT核心结论倒排必要依赖，
每项基础工作说明具体消费者、缺失接口及已核实的依赖链；未验证的路线不冒称必要前提。
产出按核心数学/工程缺口闭合衡量，不按agent数或局部编译数量衡量。
DeepSeek接一组相关引理或一个完整修复/证明问题，不能默认拆成若干几行候选。

逻辑父链和文件独占保留，主管完成派发并确认直属child真正RUNNING后退出本次原生调用；
逻辑RUNNING保留，不为释放名额提前FINISHED。子级有结果或真实请求时，使用followup_task
唤醒非root的唯一实际parent（这是上行事件，不改变任务授权）；root父级收send_message。
不要只往idle父级邮箱send_message后让root逐层轮询；不新建常驻watcher。

已交付机械工具 D:/lean/tools/agent_bootstrap.py，固定代理现有状态CLI：
python -B D:/lean/tools/agent_bootstrap.py --db EXACT_REGISTERED_DATABASE
只执行程序，不授权调用者读取该脚本或其使用说明源码。其源码owner为state_supervisor。
stdin采用ASCII转义JSON，schema=agent-bootstrap/v1，关闭stdin。
共同字段：mode,ticket,actor_id,context{run_id,protocol_version,contract_digest},
limits{timeout_seconds:1..60,max_cas_retries:0..8},continuation（首次null）。
mode=child另需parent_id,from_generation,recovery_generation=from+1；
mode=parent另需自身generation,children[{agent_id,context,recovery_generation}]。
每个child以本人身份调用一次；实际parent以本人身份一次批量校验并resume直属child。
中间恢复/确认/启动由程序完成，不再逐节点消耗模型对话；root不能代替后代调用。

回执continuation须原样续原输入。ready退出0，rejected1，blocked/timeout2，unknown3。
非法parent/context/generation整批拒绝；真实受阻child单独返回，合规兄弟继续恢复，
不把部分成功称为整批成功。未解决反馈、未结操作、FINISHED不能被自动消除或复开。
源代次自动恢复限NOT_READY/PAUSED；目标代次RECOVERING/READY/RUNNING允许续接。
root的@user确认仍使用原状态CLI。程序不派发模型、不改变owner、不提供强隔离。
等待只在原因或generation/state变化时输出，避免以重复日志替代重复对话。

helper已由独占实现owner与独立黑盒checker验证，最终SHA
476a51bee0d506384e6fbe301ecd69a961e556461fc67c2febf9fad1c8beed7b。
12场景跨版本通过；最终版三项定向复核通过。未声称最终版本全套一次运行通过，
也未确定性验证“提交后、回执前”强杀。原服务与真实等待边界不变。

当前数学主run是ledger-core-repair-20261014；root独占
D:/lean/logs/coordination/ledger-core-repair-20261014.sqlite及SQLite旁文件。
完整只读类型查询已完成，当前由原DSH source owner在新契约中独占读写SourcePacketDegreeLedger，
一次完成原命题冻结、最小相关错误组修复、编译和公理审计；root不逐项批准范围内编辑。
bootstrap-automation-20261014已FINISHED，其状态库及本规则发布库亦由root独占恢复检查。
wave1的root/math已PAUSED，Tate核值支线D停止展开；已有M+A+B+C保存，但尚未证明它们
闭合pointEquiv/Galois接口，或位于3.11→3.12→ABC的必要依赖链。整个IUT/ABC目标仍未完成。


## 19. 整包授权与实际并行（2026-10-14 再次纠正）

层级的价值是分担工作与压缩接口，不是让许多主管陪一个工人等待。
以下约束适用于后续恢复，不因换会话或模型失效：

1. 登记时交付可独立验收的完整问题包，并明确范围内决定权。文件负责人可自行完成
   已冻结命题下的证明体、策略、局部类型应用修复和验证；不得每一行都向根申请。
   需要改变命题、对象、假设或文件权属时才提交整包变更，不能暗中替换目标。
2. 源码只有唯一 owner 执行；并行来自独立文件/问题，以及基于完整公共接口的独立工作。
   不复制同一源码给多个 agent，也不为了凑人数制造监督节点。
3. 原生主管派发并确认实际执行后释放本次名额；有结果或真正接口请求再沿唯一父链唤醒。
   外部 DSH 没有已验证的原生回调，实际直接 parent 必须保留必要 I/O，不能一并消失。
4. 某一叶子的等待只阻塞它的依赖后继。主管调度已登记的独立兄弟；不得把旧受阻契约
   伪装成仍可执行，亦不得因一个依赖缺失暂停整棵任务树。
5. 先列下一批完整层级、精确路径、目标与验收标准，再由各实际 parent 自行派发。
   根不替后代构造 DSH 提示或调用，亦不读后代源码。机械恢复使用已交付 CLI/helper。
6. 汇报首先说明实际消除的错误/数学缺口、原论文命题卡、验证证据和真实剩余阻塞。
   登记节点数、启动回执、论文中的断言、旧缓存成功都不能替代数学或当前编译结果。

当前执行入口是 delegated-core-work-20261014，根独占
D:/lean/logs/coordination/delegated-core-work-20261014.sqlite 及其 SQLite 旁文件。
完整树与冻结任务见 AUDIT_LEDGER 最新登记。root 的两个直属主管为 math_supervisor
和 paper_supervisor：前者负责原 ledger 同一 owner 的最小等变性应用修复与其余固定命题
证明体；后者逐级派发互不依赖的 IUT I 输入、IUT III 过渡、IUT IV 算术结论三个整包。
论文工作是精确陈述/依赖核对，不等于 Lean 证明；旧 core-map 等待及违规保持未解决。
恢复时读实时元数据，不能硬编码本条的运行状态或假定这些任务已经完成。


### 公开运行接口速查（2026-10-15，原实现 owner 提供，已实用）

以下只授权调用既有程序，不授权查看其实现或下级私有数据。根保存这份公共说明，恢复后
不必再次唤醒实现 owner 询问相同字段；下级只由直接 parent 注入所需部分。

状态程序：python -X utf8 -B D:/lean/tools/agent_state.py --db 精确登记库。
stdin 使用 ASCII 转义 JSON。初始化恰好六字段：
op="init", request_id, expected_revision=0, run_id, protocol_version, agents。
agents 一次包含完整已知树；每节点恰好 agent_id,parent_id,role,provider,model,files,contract。
每 file 为 path/mode，mode 为 read/write/read_write/append；每 contract 恰好
version,target,variables,quantifiers,assumptions,conclusion,dependencies。
dependencies 每项为 dependency_id/version/evidence。不得覆盖旧库或自行改 SQL。

通用变更字段：op,request_id,expected_revision,actor_id,generation,agent_id,context；
context 恰好 run_id/protocol_version/contract_digest。inspect 后使用真实 revision/generation。
self 的 begin_recovery 无额外字段；实际 parent 的 resume 添加 recovery_generation；
self 的 start 无额外字段。新节点初始 generation1 NOT_READY，恢复后进入下一代次。
根 parent=@user 仅代表执行现有用户授权，不是新授权或身份认证。

- checkpoint：self，添加 checkpoint 对象（私有）及 summary 字符串（公开），两者都必需。
- wait：self，添加 feedback_id 和非空公开 message；实际缺失接口才使用，不用于让出名额。
- reply：实际 parent；actor/generation 属于 parent，agent_id/context 属于子级；
  添加 feedback_id,target_generation,response 对象。成功 WAITING→READY，由子级自行 start。
- begin_operation：self，添加 operation_id/非空 description；只登记 PENDING，不执行外部动作。
- resolve_operation：self，添加 operation_id,operation_generation,outcome,非空 evidence；
  outcome 仅 SUCCEEDED/FAILED/CANCELLED，必须使用原操作代次与证据。
- finish：self，无额外字段；无未结操作/反馈、直属 child 全 FINISHED 时才能完成契约。

checkpoint/wait/resolve_operation 要求 RUNNING/PAUSED；begin_operation/finish 要求 RUNNING。
准确的同一请求可按原 request_id 重放；只在明确 revision 冲突后刷新并用新请求重试。
bootstrap helper 仍按第18节使用；parent 自己有 PENDING 操作会阻碍自动恢复，不能虚报成功，
应先按真实 launch-only 范围结清启动回执，再 resume 子级，另跟踪最终终止与业务验收。
原生 turn 结束不等于逻辑 finish，纯让出名额无需写 wait/pause/finish。

已安装 DSH 的公开 --help 已由实际 dispatcher 核对：
dsh.cmd --profile headless --json - 的 stdin 是纯文本任务；--json 表示事件输出。
模型调用仍必须由实际直接 parent 组装、启动、收回。退出0还须核对 turn_end /
completed / 有效公开 final；turn_start 与 PID 仅说明启动。凭据不写入任务或日志。


### 当前并行恢复入口补记（2026-10-15）

以下是分别冻结的并行任务，不要把最后出现的一个 run 误当成全部任务，也不要复开已完成契约：

- delegated-core-work-20261014：原 ledger owner 的局部修复及剩余类型卡；论文分支已完成。
  根库 D:/lean/logs/coordination/delegated-core-work-20261014.sqlite。
- abc-rational-dictionary-20261015：独立证明实际 ABC 三元组、有理点、Mathlib 标准高度和素数支撑关系。
  根库 D:/lean/logs/coordination/abc-rational-dictionary-20261015.sqlite。
- arithmetic-prerequisite-definitions-20261015：沿已取得的实际 imports 核对五份底层定义文件。
  根库 D:/lean/logs/coordination/arithmetic-prerequisite-definitions-20261015.sqlite。

这些库和同路径 -journal/-wal/-shm 旁文件均由 root 独占，已在 AUDIT_LEDGER 登记。
恢复先按各库实时公开元数据核对本人/直属子级的契约、代次和状态；上列任务可能已有更新，
不能据这段文字假定仍运行或已经成功。原始调用句柄、完整公共论文卡和源码版本证据在追加审计中。
算术接口首包 arithmetic-realization-interfaces-20261015 已完成至 root revision25，保留历史库，
不把它当成新五文件任务复开。core-construction-map 旧等待/范围违规/未知覆盖历史仍保留。
当前五文件原生 owner 与 ABC 原 source owner 的跨轮精确移交均已明确登记，不能据此开放其他文件。


## 20. 用户即时覆盖：直属原生执行，停止 DSH 与多级调度（2026-10-15）

用户明确要求：“自己作为总指挥，直接指挥下面的 agent 干活，然后给你验收，不要 dpsk 了，也不要层级了”。
此指令覆盖前面关于五级树、DSH 派发、多级恢复和逐层状态审批的执行要求。
当前方式为 root 直接分派给原生执行 agent，执行 agent 直接向 root 交付；不再创建主管链或启动/续接 DSH。
停止旧执行时保留源码和历史，不删除或伪造旧状态。旧 SQLite 等待是历史事实，不是新直接任务的恢复前置门槛。
继续遵守少量精确文件白名单、同时唯一文件 owner、追加研究记录、命题与论文忠实性、依赖先证明和实际编译验收。
新分派只需先记录直接负责人、精确文件及完整任务；无需为普通任务再扩建调度工具或反复进行旧多级握手。
当前已发现 D:/lean/Iut 与 D:/lean/LeanFormal/IUT 并存；先比对已有工作，避免重复。根可读取这两个目录的文件名元数据，不因此读取下级源码。
parallel-abc-bridges-20261015 两个新生产包在派发前停止，未创建源码/探针/DSH；不按旧等待自动恢复。
完整 IUT/ABC 目标继续，停止的是旧协作方式，不是数学目标。


## 21. 最新用户补充：扁平混合执行，仅推进目标证明链（2026-10-15）

用户在第20节停止旧层级之后重新明确：DSH仍可使用，但必须直接向root负责，由root直接安排；原生agent也直接向root负责，彼此尽量少交叉。第20节的禁用DSH被本条覆盖，停止多级主管链的要求继续有效。使用已配置Flash4.1，不恢复旧父链或原自制API。
用户进一步强调“不是只是真实数学内容，是和证明相关的内容”，无关结论没有意义。每个任务必须指明IUT→ABC/原论文更强结论的具体消费者和缺口；有既有成果先复用，不为行数做重复定义、无关定理、空壳接口或日志。千万行是项目规模方向，不是证明正确或任务完成的证据。
root直接验收实际命题、前提、依赖和编译证据。少量精确文件独占、追加研究记录与不偷换概念继续；普通任务不再经过旧SQLite恢复、主管审批或多级回传。


## 22. 用户最新批次策略：集中实现，批次末验收（2026-10-15）

用户要求以十万行证明相关源码为批次规模目标，避免逐段审计及反复与Lake交互。本条覆盖前面“每个小步骤都完整编译/公理审计”的频率要求，扁平直属协作继续。
先围绕IUT→ABC及原论文更强结论的实际依赖，成批实现互不重复的模块；不按行数拼凑无关结论、空壳、重复定义或日志。开发中只保留解除真实依赖/类型阻塞必要的局部检查；全项目构建、完整公理扫描及统一验收移至批次末。
未集中验收的完整证明源码称为候选，不能宣称已证或把sorry/自造axiom/空承诺字段当依赖。已证明依赖尽量复用，源码仍按直接owner独占。新工作不恢复旧主管链或SQLite审批。
root已停止本轮顺序重试构建，保留已有成果和真实结果；完整Project构建未通过，不能以局部通过替代。

## 23. 用户指令：从公理出发、前置优先、root 去重调度（2026-10-17）

用户要求全员改为自下而上的依赖纪律：任何定理若依赖未证明的前置（① sorry/admit/自造 axiom；② 只声明结构/卡片而无实际 inhabitant；③ 条件定理的未闭合前提），先停止对该定理的推进，转去证明前置；前置证毕后才恢复原目标。
防重复：发现未证前置时先向 root 反馈（精确名称＋文件＋消费者），不得自行开证；root 汇总去重后指派唯一 owner（自证／等接口／已证），再回执执行者；同一前置禁止两线并行证明。
机械支撑（root 工具，只读）：D:\lean\tmp\frontier-probe-20261017\FrontierProbe.lean 扫描 LeanFormal.IUT.Project 闭包内 Supply/Card/Frontier/Clause 等命名义务与 Prop 义务，输出 inhabitant 最小不动点、blockedBy、消费者数；结果用于 root 调度去重。四件套验收、文件独占与追加记录等既有规则不变。


## 24. 当前 N8 交接入口与唯一待定方案（用户更新，2026-10-20）

用户要求持久更新交接，避免反复复制聊天。N8/source Theta-link 相关任务启动或恢复时，root先读当前交接：
[D:/lean/logs/coordination/n8-theta-link-handoff-20261020.md](D:/lean/logs/coordination/n8-theta-link-handoff-20261020.md)。
该文件属于root公共交接读入口；向直属执行者提供所需精确目标和已证接口，源码权属规则继续有效。

最新判断：**目前唯一尚未形成完整方案、可能构成真正研究卡点的是Theta-link精确形式化命题**，包括实际source覆盖AΘ、单位比较/theta divisor、Mq→MΘ的表示独立/保乘/可逆/基变换自然性、单位根/deck歧义、tempered π₁刚性与conjugate synchronization。先从原文固定一组完整可核验命题，再开展相应证明；不能用任意card字段或有限模型代替。

此前“两个半卡点”和task-134单独卡点的记录保留。inverse-j系数/求值/压缩包、log实际载体比较等已有具体数学路线，按真实依赖继续；**有路线不等于已证，task-134的variable-q系数定理和实际求值桥不能跳**。本判断不宣称整个IUT/ABC只剩一条未证定理，也不改变未验收工作的状态。

后续先查上述交接和其中的具体指导，不要求用户重贴背景；新事实与纠正追加记录，不覆盖历史，不据旧运行状态自动恢复数学任务。


## 25. 低级任务先走确定性脚本（2026-10-21）

用户要求减少所有大小错误都走大模型的浪费。已提供零模型调用入口，详见
D:/lean/tools/LEAN_AUTOMATION_USAGE.md。对已获授权的精确文件，编译、错误归类、依赖缺失、重复任务和结果落盘先用：

```powershell
python -X utf8 -B D:/lean/tools/lean_auto.py repair EXACT_FILE.lean --build-deps
```

普通路径先复用同版本证据；资源等待/超时交执行层，缺失或疑似过期依赖最多定向构建一次，剩余错误输出有来源及限长上下文的候选包。同版本相同失败不反复编译或入队；版本改变重新入队，外部输入变化用--fresh。只有文件owner可以加--apply执行已验证的重复import清理；自动化不改证明命题或假设。

批量使用lean_queue.py与lean_worker.py --max-tasks N；worker默认只回报简短状态，完整任务包按result_file取用。先看状态和错误包，不让大模型重复读完整构建日志做机械分类；local_repair只是廉价worker候选，不把复杂未解目标自动认作小错。脚本不自动调用DSH/大模型、不启动常驻进程；仍由现有owner决定数学工作如何处理。单agent任务不因使用队列而派出新agent。

build/promote有独立执行分支。promote只认证目标文件并标记promoted_pending_batch/staged，全Project构建仍放在批次末。源码词法检查和局部编译不替代公理审计或论文忠实性验收。保留现有文件权属、追加日志与前置证明纪律，不恢复旧多级状态握手。

## 26. 以实际证明消费者约束工作范围（用户纠正，2026-10-22）

用户要求优先做对项目证明直接有裨益的内容，减少“数学上有用但未接项目”的工作。
本节细化第21、23节，并纠正以一般性、难度、行数或Project导入数量安排优先级的做法。
L0.3执行方法见 [面向项目证明的L0.3实施方法](D:/lean/logs/coordination/l03-proof-focused-methodology-20261022.md)。

1. 每包先固定已有消费者、完整目标、实际对象及假设来源、已证供体和验收出口。已核对的必要前置可以先做，不要求未完成的消费者已编译；仅凭文件名、注释、import或“将来可用”不足以扩展任务。
2. 先按项目关联和实际缺口筛选，再在有把握完成的问题中优先处理重要难项。机械问题先走第25节脚本；不为了增加成果数量扩写特例、同义接口、合取汇总或数据字段。
3. 用户已授权使用保持原对象、量词、假设和结论强度的更短路线。新路线可以先交数学草稿、现成供体和精确剩余接口；未证草稿不能作后续Lean证明基础，也不新增承诺字段伪装完成。
4. 通用结果已有则直接复用，不为source专用再复制证明；只有实际消费者需要时才新增一般性。原G2要求的∀finite G/∀作用图必须保留，不得换成regular、free或trivial特例；更强的all-Scheme-target或任意底粘合不默认开展。
5. 发现偏离目标的旧分支，先停止把它当主线供体或进度；没有真实消费者时不为修成完整框架投入。保留旧源码和研究记录，不自动删除或大改已验证数学。
6. 同文件的固定曲线实例不限制其generic范畴定理；测试曲线已有定位后不反复审查。真正source接入须核对实际对象/范畴/纤维比较，不能只靠signature、alias或Source名称。
7. 分别报告“数学核心已证”和“实际消费者已接入”。验收写清消掉了哪个原前提、对应版本的编译/公理证据及剩余桥；Project绿色不自动代表源对象忠实或上层定理完成。
8. 给定合格初始数据的论文定理，与从较弱算术数据构造全部初始对象，是不同证明责任；不得擅自把后者新增为前者的前置。前置受阻只停止受影响分支，保留真正独立且相关的工作。

以上为方法论和范围约束，不新增用户逐项审批、调度工具或多级恢复流程。用户当前单agent偏好继续；本次只更新文档，不更改Lean代码。
