# 局部证明 DAG

遵循 SHEAF 的单图、两类依赖原则。本目录当前只登记 6 个已知锚点，**不是全 IUT 的完整图**。节点间无边不代表现有 Lean 文件之间无依赖；`dependencies_complete: false` 明确表示尚未展开。

## 节点文件与字段

一个节点对应一个定义、命题或目标，ID 不复用；节点只存当前状态，历史记 git / AUDIT_LEDGER。

| 字段 | 含义 |
|---|---|
| `id`, `kind` | 稳定 ID；definition / statement / target |
| `root_role` | final_target / milestone / null；里程碑不自动是最终目标的已证依赖 |
| `statement`, `source` | 自足命题/定义说明及准确来源 |
| `lean` | file、declaration、type、status；未锁定时可以缺完整类型，但不能进入陈述阶段 |
| `statement_dependencies` | 陈述依赖的节点 ID |
| `proof_dependencies` | 证明依赖的节点 ID |
| `edge_evidence` | 每条边的依据与 planned / observed_source / verified_lean 状态 |
| `dependencies_complete` | 依赖是否已完整展开；false 不是“没有依赖” |
| `natural_language_proof` | provenance、完整 steps；未知时 null 并填写 gap |
| `mathlib_search` | 查询/工具/日期/结果；未做写 not_run，不虚构搜索 |
| `stage1` | open / complete / mathlib_leaf / statement_disputed |
| `proof_status` | open / existing_unrevalidated / statement_compiles / proof_body_checked / kernel_closed |
| `semantic_status`, `locked` | 语义审查状态与是否锁定 |
| `candidate_connections` | 尚未核实的连接；不是 DAG 边或必要性证据 |
| `gaps`, `evidence` | 精确缺口、现有文件版本/证据及局限 |

例如 `abc-target` 的表层证明计划需要条件桥和桥输入的实际构造。后者尚无完整证明，不能据此前者报告完成；这个初始图只暴露缺口，不承诺接口路线最终符合原文。

`cor312-bridge-construction` 的类型示意使用与实际 carrier 一致的 universe `u`；它只是暴露现有条件桥的输入义务，不预先规定源载体，也不另加“所有模型皆可构造”的要求。正式冻结前须固定实际构造的 universe、输入和原文比较。

## 手工维护步骤

1. 修改节点前检查是否已有同一原文结果/同一 Lean 声明，避免重复。
2. 拆分节点时新建准确子命题，两种依赖分开；补边的依据。
3. 所有依赖 ID 必须存在；两种边合并后无环。循环通常提示定义/命题层次错误，不能相互用 sorry 掩盖。
4. 阶段 1 的证明写完且 statement deps 已声明，才进入阶段 2。
5. 阶段 3 前 proof deps 已声明即可；尚未证明的依赖显式保留，不阻止顶层证明体探索，不计闭合。
6. 证明落地时按真实使用更新边和 imports，再刷新 coord/queue.md。
7. 无目标可达的节点退出队列但不删除；合并节点保留旧 ID 的 `merged_into` 和原因，所有使用者改指保留节点。

## 当前真实性限制

6 节点尚未达到 SHEAF 阶段 1 的完成条件：没有完整原文证明分解，也未逐节点完成 Mathlib 匹配。所有节点均未锁定；本轮未做新的 Lean 编译。

目前没有自动 DAG/队列脚本。编辑者负责 JSON 合法性、引用存在性、无环和状态一致性；迁移时已经执行一次结构检查，结果见 AUDIT_LEDGER。将来增加自动化应复用现成工具，只解决真实机械负担。
