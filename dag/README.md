# dag/ — 全仓库 Lean DAG（可复现、可核销）

本目录是按用户要求构建的完整 DAG，分三层：

## Layer A — 文件级 import DAG（机器生成，完整）
- 节点 = 工作区**每一个 .lean 文件**（当前 123,411 个）
- 边 = Lean `import`（根感知解析：importer 所在 root 优先，再 repo root；其余记为外部 import，如 Mathlib）
- 当前：123,411 节点 / 36,618 边 / **0 个 import 环** / validator ok=true
- 文件：`generated/nodes-files.json`、`generated/edges-imports.json`、`generated/imports-external.json`、`generated/summary.json`、`DAG-VALIDATION.json`
- 工具：`tools/dag_build.mjs` + `tools/dag_validate.mjs`

## Layer B — 声明级路线 DAG（人工校准 + 可核销，路线/方法/论文/反例）
- 节点 schema：`{id, kind, title, status, files, declarations{path:[declName]}, note}`
- kind: target|theorem|interface|tree_asset|bottom|conditional|bridge|named_input
- status: PROVED|BOTTOM|CONDITIONAL|NAMED|TREE_ASSET|DEF|GAP
- 边 schema：`{from, to, kind}`，from=依赖者→被依赖者；kind: statement|proof|interface|gap
- 当前：**63,606 节点 / 1,519 边 / 0 conflicts**；proof+interface 子图无环；statement/citation 子图存在论文引用环（informational）
- 输出：`declaration-dag.json`；校验：`DECLARATION-DAG-VALIDATION.json`
- 工具：`tools/dag_merge2.mjs`（合并 fragments，按 section 加 id 前缀）+ `tools/dag_validate_decl2.mjs`

### Layer B 的 fragments（合并来源）
| prefix | 内容 |
|---|---|
| （main） | Lead 主目标链（ABC→3.12/3.11→IUT IV→bottom→named） |
| foundation: | B1-B7 bottom、C StepProvider'/CVCompositionF/F0/degree、D bridge 对、HOLD、gate |
| e-deep: | E1-E5 深输入与路线 |
| iuti-ii: | IUTI/IUTII 节点（Hodge theater/Frobenioid/EtTh/log-shell/Tate） |
| iutiii: | IUTIII 190 文件节点（Thm311/Cor312/StepXI/hull） |
| iutiv-abc: | IUTIV+ABCBridge 178 模块（含 ABCFrontier 替代路线，**pointwise 路线被证伪**） |
| legacy-dag: | 早期 89 个 SHEAF DAG 节点（`dag/nodes/*.json`） |
| paper-routes: | 官方 Stage1-5 + §4 四三角 + IUT III/IV 原文步骤（46 节点/76 边） |
| paper-theta: | EtTh/GenEll/AbsTopIII/NCBel/Hodge-Arakelov/Explicit estimates 的 paper 节点（383/1082） |
| route-mentions: | **42,770 条路线/尝试/反例/障碍提及**（来自 9,515 个 md/txt 文档，含 AUDIT_LEDGER 3.4MB） |
| paper-labels: | **20,091 个 paper 定理/定义/引理标签**（257 篇 corpus） |
| web-routes: | **12 条外部（网络）路线**：LANA 项目/中期报告、IUT Validation、Bridge Certificate（4 applications）、IUT Comes Home、Joshi FAQ、Scholze-Stix 报告、Hayashi impossibility、Mochizuki Formalization 报告、LeanForm ZFC、autoformalization、IUAni 动画 |
| theta-etth: | Foundations/Theta + EtTh + AbsTopIII 实节点（32/26） |

## Layer C — 声明宇宙索引（机械，供查询/核销）
- `generated/declarations-index.json`：**1,572,263** 条声明（theorem/def/structure/... name→file:line），覆盖 123,410 文件（273MB，机械抽取）
- 工具：`tools/dag_declarations.mjs`
- 用途：任何 curated 节点的 declarations 都可在此索引中定位；validator 用文件内 substring 校验

## 运行
```powershell
cd D:\lean
node tools/dag_build.mjs            # Layer A
node tools/dag_validate.mjs         # Layer A 校验（SCC/环/重复边/覆盖）
node tools/dag_merge2.mjs           # Layer B 合并 fragments
node tools/dag_validate_decl2.mjs   # Layer B 校验（proof 子图无环 + 文件/声明存在性）
node tools/dag_declarations.mjs     # Layer C（可选，较慢）
```

## 解读与纪律
- Lean 禁止循环 import：Layer A 的环即源代码缺陷（当前 0）。
- Layer B 的 `statement` 边是论文引用关系，允许成环（报告为 informational）；`proof`/`interface` 边必须无环。
- `declarations` 只写已确认存在的声明名；validator 逐个 substring 校验；任何改动会使校验失败。
- 只有 `PROVED`/`BOTTOM` 节点可作为已证路由；`CONDITIONAL`/`NAMED`/`GAP` 如实保留（不得冒充 closure）。

## 动态维护（DAG watchdog，替代 queue）

- **入口**：`tools/dag_watchdog2.mjs`（后台常驻；当前由 pwsh 进程守护）
- **循环**：
  1. 每 5 分钟重建 Layer A 图（`dag_build.mjs`+`dag_validate.mjs`）并合并 Layer B（`dag_merge3.mjs`+`dag_validate_decl2.mjs`），再计算运行时证据（`dag_status.mjs` → `runtime-status.json`/`RUNTIME-MISMATCH.md`）
  2. 生成 dirty 计划（`dag_plan.mjs`+`dag_plan_deps.mjs`）：源文件比 olean 新、或多个 PROVED/BOTTOM 节点的证据不新鲜（mismatch）
  3. **按 import 依赖拓扑序**编译 dirty（依赖先）；并发上限 **12 个 lean 进程**（`DAG_MAX`，用户要求最多 12）
  4. 每个文件结果以 `EXIT=n FILE=rel` 追加到 `tmp/xif_guarded_results.log`（兼容既有 checker），并写入 `dag/watchdog/logs/`
  5. 失败文件记录在 `state.json`，同一源版本 10 分钟内不重试；源变更后自动重试
- **不再使用 queue**：`xif_guarded_queue`/`xif_watchdog_forever` 已停止；DAG watch dog 是唯一编译调度器
- **产出**：`dag/watchdog/{plan,order,runtime-status,heartbeat,state}.json`、`watchdog.log`、`stdout.log`、`RUNTIME-MISMATCH.md`、`logs/`
- **动态性（全自动）**：新文件/新 import 在每 5 分钟图重建时自动进入；teammates 更新 fragment 后 merge 自动刷新节点/状态/边；运行时证据（olean freshness/last_exit）自动写入 runtime-status；coord/DAG-NEXT.md 与 dag/watchdog/next.json 每个 rebuild/cycle 自动刷新；blocked/refuted/detoured 由 coord/DAG-BLOCKED.json 自动排除。