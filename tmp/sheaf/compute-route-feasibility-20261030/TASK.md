用户任务：单线程探索是否可把当前 IUT 源比较的部分困难，转化成大规模逻辑搜索或大量项相消等计算问题；查网上原始研究和本地 mathlib，并检查已有失败路线。只做可行性分析，不声称新方法已闭合 gap，也不启动大算力训练或证明批次。

任务 ID：compute-route-feasibility-20261030；owner：当前 chat root；SHEAF stage 1。
消费者：Q-BRIDGE/xif-source-construction；源路线仍为用户确认的 Formalization 2026 §4 和 EssLgc 2024 Stp1–8。
范围：同一合格 C、固定 q/Theta gluing、原允许像族及 Ind1–3、完整 1-column、原权重/参考/符号。计算化必须证明源数据到计算表示的正确性；不把新的目标等价假设藏在编码中。
读：两份补充材料、当前直接源消费者、已有 C9/xi-f 失败路线索引；只读候选方法涉及的 mathlib 文件和原始论文/官方文档。
写：coord/reports/compute-route-feasibility-20261030.md；本目录证据/检索记录；独立 DAG 节点；AUDIT_LEDGER、STATE、queue 仅追加。
阶段：阶段 1，先辨认可计算子问题、所需表示、可验证证书、源转移义务、停止条件和算力作用。没有获准把目标换成有限样本、简化 q/Theta 模型或经验数值比较。
版本：记录 workspace HEAD、mathlib HEAD、确切文件 SHA256；网页核对日期 2026-10-30。已读历史证据仅按其实际版本使用。
验收：给出候选优先级和具体最小实验；区分现有算法、AI 搜索增强、尚无依据的设想；指出每项如何避免重复搬迁 gap。编译/内核/目标验收未运行时分别标明。
