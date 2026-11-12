# N8-LEGACY-ARCHIVE — 只读盘点（shehdd, 2026-11-11, A465 任务2）

范围：tmp/n8-* 旧 pipeline 目录 + 旧 fragment，仅盘点/记录，**不动任何文件**。

## 目录盘点（.lean 计数 / 体积 / watchdog 结果记录）

| 目录 | .lean 文件 | 体积 | results 记录 EXIT0 | EXIT1 | 无结果 | 近 1h 修改 |
|---|---|---|---|---|---|---|
| tmp/n8-20261018 | 2258 | 12.5 MB | 0 | 0 | 2258 | 0 |
| tmp/n8-20261020 | 113 | 0.2 MB | 0 | 0 | 113 | 0 |
| tmp/sheaf/n8 | 878 | 2.6 MB | 23 | 2 | 853 | 0 |

- 三个目录合计 3249 个 .lean（~15.3 MB），近 1 小时无修改 → 非活跃 pipeine。
- `tmp/n8-20261018/` 内是旧 root 布局（如 `compile-root/LeanFormal/IUT/*`、`general/*`、`puncturebuild/*`），曾被用于 legacy SourcePsi/AdicCompletion port 的源（该 port 链已按 Lead A460 PARK，`coord/DAG-BLOCKED.json` 记为 PRAGMATIC-DEAD-END）。
- `tmp/sheaf/n8/` 中仅 23 个文件有 EXIT0 记录（如 closure 下部分 C*.lean），2 个 EXIT1（Group1Statement.lean 等重复声明类错误），853 个无 results 记录。

## Legacy fragment

- `coord/target-chain.legacy-dag.json`：nodes=89，edges=164；状态：PROVED 18、CONDITIONAL 18、GAP 15、NAMED 38。
- 该 fragment 在 `tools/dag_merge2.mjs` 中仍被合并（`legacy-dag:` 前缀节点），但 `tools/dag_next.mjs` 明确排除 `legacy-dag:` 前缀 → 不进入可行动队列。

## 结论/建议（不需要动作，除非 Lead 指示）

1. 三个 n8 目录可视为**归档只读**：不新增、不修改、不追逐其 results 状态；若需减负可从 extra-targets 移除其路径（当前 extra-targets 未列入 n8 目录项）。
2. `coord/target-chain.legacy-dag.json` 保持现状（历史 DAG 证据），不升级状态、不新增节点。
3. `tmp/sheaf/n8/Group1Statement.lean` 等 EXIT1 属旧 pipeline 重复声明（与 LeanFormal 现有 decl 重名），修复无收益 → 记 PRAGMATIC-DEAD-END 即可，不修改文件。
4. 与 legacy SourcePsi 链（已 PARK）的关系：n8-20261018 为其旧布局源，保留归档以支持必要时重建，但不再尝试编译。
