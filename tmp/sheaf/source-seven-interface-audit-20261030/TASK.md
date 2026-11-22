# 七项 actual/exact 接口核对

任务：source-seven-interface-audit-20261030；owner：root-current-chat-single-thread；日期：2026-10-30。

目标节点：xif-source-construction 的 IPL algorithmic provenance 消费者；SHEAF 阶段 1，附局部接口反证试验。以用户最新七项清单为范围，核对当前源码，纠正此前探索报告已被新代码超过的状态。不修改目标定义、共享 Lean 源码或其他 owner 的文件。

读取：SourceOutputPrimeStripInterpretation、S1221/S1225/S1231/S1232/S1233/S1234、ParametricCarrier、MultiradialOutputKernel/ProfileKernel、SourceKummerEvaluationArrows 及其 S1187/S1188/S1195 供体；已有补充路线报告和必要原文摘录。工作树 HEAD 9399e9fab4d62ea5f78a4a0d56ceecb84525a3ee；具体字节以本包 evidence.json 快照为准。

写入：本目录的新任务、证据、隔离 Lean 试验；coord/reports/source-seven-interface-audit-20261030.md；独立 DAG 节点；AUDIT_LEDGER、STATE、queue 仅追加本包结论。共享接口只读，不启动其他历史任务。集成/构建负责人：本 chat root，仅局部试验，不构建 Project。

数学核对：对任意原有合格 I : OriginalInput l V，Choice = I.family.index。区分实际索引对象与原文 Ind 操作语义、theta 标量像与全允许像族；核对同一 Carrier/箭头上的连接。检查 level 保持的 Ind1 是否与严格增层的 Ind3 重合。对于固定实际 upperEnv，方形须绑定该箭头，其余边也须有源来源。

statement_dependencies：xif-source-construction；上述准确类型与当前字节。
proof_dependencies：已有供体仅按已核对声明复用；本包不新增 xi-f 证明依赖。

自然语言论证：若 ind3 1 c = ind1 g c，Ind1 的 level 不变与 Carrier.ind3_level_eq 联合推出 level c = level c + 1，矛盾。只否定这组操作/接口的组合，不否定其他源实现或 IUT。Profile 的可组装性与强 Carrier/原文像族的实现性分别记录。

复用调查：优先 S1231/S1232/S1233，不再寻找已出现的 stripOfChoice；必要时直接用 Core/Profile 的 route 消费者检查是否需要强增层。无需新的全仓或全 mathlib 审计。

验收：冻结供体版本；记录七项实际范围、可组合部分和阻塞等式；若运行 Lean，用零模型自动化并保存日志、公理输出与结果。编译、kernel 闭合、源语义、最终 target 分别报告。停止于一个具体下一步及其数学条件，不把新的 record 声明当缺口消除。
