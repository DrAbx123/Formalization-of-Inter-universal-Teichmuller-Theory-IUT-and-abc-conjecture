# Lean 低级任务自动化

入口为 `tools/lean_auto.py`、`lean_queue.py`、`lean_worker.py`；复用 `build_guard.ps1`，只依赖 Python 标准库。自动模型调用预算固定为 **0**，没有后台模型循环。以下命令从 `D:/lean` 运行。

## 日常单文件入口

```powershell
python -X utf8 -B tools/lean_auto.py repair PATH.lean --build-deps
```

先检查缓存，再经资源门控编译；缺失 `.olean` 或依赖源码比产物新时，最多构建一个明确模块并重试一次。同一版本失败过的依赖构建不会反复执行。不会自动 `lake update`、下载缓存、清理产物或构建整个 Project。

```powershell
python -X utf8 -B tools/lean_auto.py repair PATH.lean --apply --build-deps
python -X utf8 -B tools/lean_auto.py audit PATH.lean --fresh
python -X utf8 -B tools/lean_auto.py packet PATH.lean --target '具体消费者、冻结命题和缺失接口'
```

`--apply` 只在原文件编译通过后删除**重复的普通单行 import**，保持行号，保存原字节并重新验证；失败回滚。不会自动修改证明、增加假设、调高 heartbeat、补 `sorry` 或换数学对象。只对自己拥有编辑权限的文件使用。`--fresh` 跳过已有验证缓存和失败依赖构建缓存。

`packet` 复用同一次检查结果；保留诊断所属文件与多行目标，只截取指定文件上下文。依赖报错不会误引用当前文件同一行。最多提供 6 个错误（每个 1200 字符）、5000 字符局部源码和必要尾部；完整输出留在 `log` 路径。普通检查最多返回 20 个诊断，不把全日志交给模型。

## 路由规则

| 状态 / route | 后续处理 |
|---|---|
| `green / none` | 本次局部检查通过，或明确标记 `cached:true` 的旧证据复用 |
| `missing_dependency`、`stale_dependency / dependency_build` | `repair --build-deps` 最多一次定向构建；仍失败交依赖 owner |
| `resource_wait`、`timeout`、`resource_limit / operations` | 资源或执行配置问题，不当作数学问题交模型 |
| `inputs_changed` | 本次结果不认证正在改动的版本；稳定后重新入队 |
| `local_repair / small_model_candidate` | 未知名字、类型应用、局部 tactic 等生成小任务包；由 owner 决定是否交已有廉价 worker |
| `proof_policy`、`proof_review`、`unclassified_failure / source_owner` | 核对实际前提、声明及原目标，不自动跳到大模型 |
| `promoted_pending_batch / batch_build` | 只完成落位和目标文件编译，Project 验收待批次末 |

`small_model_candidate` 是诊断启发式：`unsolved goals` 或 `failed to synthesize` 也可能藏着真正数学缺口，不宣称它一定简单。脚本**没有实现自动 DSH 派发或模型补丁采纳**；输出的是可供现有 worker 使用的候选包。保留单 agent 使用方式。

## 批量任务

```powershell
python -X utf8 -B tools/lean_queue.py init
python -X utf8 -B tools/lean_queue.py add --kind repair --file PATH.lean --build-deps --target '实际消费者与缺口'
python -X utf8 -B tools/lean_worker.py --worker local --max-tasks 20
python -X utf8 -B tools/lean_queue.py list
```

队列默认 `tmp/lean-queue.jsonl`；各队列命令用 `--queue EXACT_PATH` 可隔离。worker 默认处理 1 个任务；`--max-tasks` 为 1..100 的有界批次，不常驻、不循环重试失败任务。同一个源码和依赖版本、任务类型、选项及目标自动去重；失败任务也不重新入队。`--new` 显式建立新任务，但编译缓存仍有效。

四种任务有实际分派：`audit` 检查、`repair` 机械修复/任务包、`promote` 落位、`build` 执行 Lake 构建。`build --file` 接模块名；不会把 build/promote 偷换成 packet。

队列在操作系统文件锁内追加事件，`init` 不清历史，路径归一化，同一文件最多一个活动 claim；build 与本队列其他任务互斥。完成/失败需要对应 worker 和一次性 claim token。进程死亡不会自动解除源码所有权：

```powershell
python -X utf8 -B tools/lean_queue.py release --id TASK_ID --confirmed-stopped --reason '已确认旧进程停止'
python -X utf8 -B tools/lean_queue.py retry --id TASK_ID --reason '外部依赖已经修复'
```

`release` 只用于运行中任务；`retry` 只用于失败任务。源码/依赖版本改变后应重新 `add`，旧任务的冻结指纹不会悄悄更新。旧 v1 队列可重放；无 token 的旧 claim 需先确认停止，再 release。损坏 JSON 行明确报错并保留，不丢弃历史。锁不代替仓库 owner 约束；跨不同队列及不遵循脚本的编辑器不受同一 claim 保护。

结果和候选包默认写入 `tmp/lean-automation/results/`，编译日志、缓存、修复备份在同一 runtime。可用 `--runtime EXACT_PATH` 改位置；worker 的 `--out EXACT_JSON` 另外保存本次完整结果。终端默认只回报状态、路由、缓存命中及结果路径；`--details` 才输出完整任务包，避免成功日志重复占用模型上下文。

## 落位与批次构建

```powershell
python -X utf8 -B tools/lean_auto.py promote SCRATCH.lean LeanFormal/IUT/DEST.lean --after EXISTING.MODULE
python -X utf8 -B tools/lean_auto.py build LeanFormal.IUT.Project --timeout 1800
```

落位是显式操作，必须拥有 scratch、目标和 `Project.lean` 的权限。默认拒绝覆盖，直接命令的 `--force` 才允许替换；队列不隐式开启 force。先检查源文件，再保存目标及 Project 原字节，插入精确 import，验证目标文件。失败时只恢复仍等于本次写入的文件；发现别人修改，报告 `rollback_conflict` 并保留备份，不覆盖外部编辑。事务记录位于 `promotion-*/journal.json`。进程中途强杀后的 `prepared` 事务须据备份与实际文件检查，不能假定已落位或已回滚。

成功状态明确为 `promoted_pending_batch`，队列为 `staged`，不冒称 Project 已通过。全 Project 构建由批次末显式命令负责，不每落位一文件就全构建。

## 证据边界与只读盘点

缓存指纹包括目标与可解析 import 的递归源码内容、对应 `.olean` 大小和时间戳、toolchain、Lake 配置/manifest，以及编译工具版本。新源码比 `.olean` 更新时阻止直接拿旧产物报绿；这是保守时间戳检查，不是 Lake trace 的替代。文件内容与依赖在检查期间变化时拒绝记绿。

缓存不覆盖元程序读取的任意外部文件、环境变量、未声明的插件输入或特殊动态 import；这些场景使用 `--fresh`，依赖有疑问时先明确 `build MODULE`。`green` 表示局部编译与词法检查通过，**不是完整公理审计或 IUT 论文忠实性证明**。批次验收仍须核对真实依赖及原命题。

```powershell
python -X utf8 -B tools/lean_triage.py --files EXACT_A.lean EXACT_B.lean
```

默认只盘点明确文件；`--all-project` 才扫描 LeanFormal、Iut 和 tmp。盘点报告同名/同字节分组、词法禁用项与导入信息；完整模式计算 Project 可达性。未接 Project 只是复核候选，不自动判为鸡肋、删除或落位。执行全量盘点仍需拥有相应读取范围。

回归测试：`python -X utf8 -B tools/test_lean_automation.py`。测试使用独立临时目录；没有生产数学编辑、模型调用或全 Project 构建。
