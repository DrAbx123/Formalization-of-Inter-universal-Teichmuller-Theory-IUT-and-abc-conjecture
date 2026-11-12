# Review Understanding — 2026-11-02 (FROZEN RECORD)

状态：冻结记录。  
日期：2026-11-02（Asia/Shanghai）。  
记录人：lead（Team Lead）。  
用途：记录我对两份审查报告的共同点、不同点和自我更正的理解，供后续引用。  
不是：对两份报告的优劣裁决；不是 paper-level 验收；不是目标变更授权。

## 0. 两份审查报告

1. 主工作区报告：
   D:/lean/coord/ROADMAP-2026-11-02-REVIEW.md

2. worktree 报告：
   D:/lean/.claude/worktrees/roadmap-2026-11-review-cddd5f/coord/ROADMAP-2026-11-02-REVIEW.md

两份报告都在审查：
D:/lean/coord/ROADMAP-2026-11-02.md

本记录不对两份报告做“哪份更好”的判断。两份的 scope、证据基础和排期建议不同，应作为互补的审查输入保留。

## 1. 共同点

两份报告在以下判断上一致：

1. paper-level 3.12 仍未验收。
2. D6(c) 没有按原路线图 Batch 1 闭合。
3. M2b 不是 (A)+(C) 就能收；M2c 仍缺。
4. H² 块漏了 h2Comparison 满射。
5. D5 缺 S2057Mod29FactorizationData。
6. D9 缺 S1964HonestCFQuotient。
7. S2040 的 O^xmu / hull / logVolumeComparison 需要语义核对。
8. 标签精度不足：[ACTUAL] 混用了实际 inhabitant 和条件蕴含。
9. S2106 的 M3 后三项反例只有接口，没有具体实例，应标 REFUTED-informal。
10. S2108TwoFullInputs 仍以已被否定的 hG 为参数，是空真的。
11. 不应靠改目标、加字段、加 IsSepClosed 来解决。

## 2. 不同点

1. 重心不同：
   主报告偏 paper-level 数学消费者与 S2040 语义；
   worktree 报告偏证据链、ledger、版本控制与全局目标固定。

2. 主报告没有讨论 ledger 截断；
   worktree 报告实测本地 ledger 与 HEAD 差异，指出历史条目缺失。

3. worktree 报告提出 S2094BigSquareEssSurj 的 projection-only 风险，建议在 S1850Doubled 上做证伪探针；
   主报告没有展开这一点。

4. worktree 报告追问 paper-level 3.12 的 Lean 陈述、SourceNativeInitialThetaData、paperP6Target_actual、challengeC6Aligned_proved 与 IUT-CRITIQUE 禁止步骤；
   主报告没有系统讨论这组目标歧义。

5. worktree 报告统计 D6 同一缺口有约十个名字，建议停止换名归约；
   主报告没有展开这一点。

6. 排期建议不同：
   主报告若自排，先做 S2040 单位商映射与 q 读数/Θ-hull 读数；
   worktree 报告若自排，先做 Batch 0 ledger 修复与 paper-level Lean 陈述固定，再做 H² 块。

7. 证据风格不同：
   主报告多用 Lean 行号和 IUT 原文页码；
   worktree 报告用 [source]/[ledger]/[inference] 标记，并检查 olean 与 git 状态。

8. 这些不同点主要是 scope 和优先级差异，不是互相否定。
   在重叠问题上，两份报告判断一致。

## 3. 我的错误更正

1. 我说“第二份更严格/更好”是越界。
   两份报告不能排名；应保留为不同 scope 的审查输入。

2. 原路线图把 D6 Batch 1 写成可闭合链，是过乐观。
   实际仍缺：
   S2121ComparisonTwist；
   S2086CospanGMapFiniteEtale（cover-map 证书）；
   S2127 的编译证据；
   S2094BigSquareEssSurj 的可靠性。

3. 原路线图把 M2b (A)+(C) 写成可收，是错的。
   (C) hcanon 与 LocalReciprocityData 依赖 M2c；
   M2c 仍是深输入。

4. 原路线图 H² 块只写 CoboundaryLift，漏了 h2Comparison 满射；
   G2/G3 有重复，G1 必须先做。

5. 原路线图没有把 ledger 修复和 paper-level 陈述固定放在 Batch 0。

6. 原路线图把 paper O^tri / O^xmu 全部写成 actual，语义上不够精确；
   O^xmu 需区分 rootsOfUnity 子群与论文的单位商。

7. 原路线图没有列出 D5 S2057Mod29FactorizationData 与 D9 S1964HonestCFQuotient 的缺口。

## 4. 修正后的下一批

Batch 0（阻塞后续）：
1. 修复 ledger：从 HEAD / recovery 副本恢复缺失历史，并加写入保护。
2. 固定 paper-level 3.12 的唯一 Lean 陈述；分类 S2030、paperP6Target_actual、challengeC6Aligned_proved。
3. 做一次 git 检查点或 SHA 快照。

Batch 1（低成本、高信息）：
1. S2127 编译验收，按签名登记为条件结论。
2. S1850Doubled 证伪探针：测试 S2121ComparisonTwist / S2094BigSquareEssSurj。
3. 不把 S2094BigSquareEssSurj 当可靠输入。

Batch 2（S2040 语义）：
1. 核对 O^xmu 是 rootsOfUnity 子群还是单位商。
2. 核对 hull 有限性与 H <= -vol(image) / Q <= H 的方向。
3. 核对 logVolumeComparison / EtaComparison 与 IUT-CRITIQUE 禁止步骤。

Batch 3（H²）：
G1 -> h2Comparison 满射 -> CoboundaryLift -> PsiCnsH2LimitComparison -> PsiCns-M3 -> M4。

Batch 4（M2b）：
先做 (A) TransferBridge；M2c 暂缓或明确登记为深输入。

Batch 5（D5/D9）：
D5 S2057Mod29FactorizationData；
D9 商见证 / SlicePushNaturality。

## 5. 明确不做

1. 不改 M3 原目标。
2. 不把 IsSepClosed 当原 M3 验收目标。
3. 不给 EtaleStackBaseChangePresentation 加 coherence 字段。
4. 不把条件接口当无条件。
5. 不使用已否定的 S2094GPresentationConeEssSurj。
6. 不把 S2106 的接口反例说成 kernel 已证具体反例。
7. 不把 ledger 当前状态当作完整历史。
8. 不把两份审查报告排名。

## 6. 冻结方式

本文件写入后：

1. 计算 SHA-256；
2. 生成同名 .sha256 文件；
3. 在 AUDIT_LEDGER.md 追加封印条目；
4. 设置本文件与 .sha256 文件为只读。

注意：文件系统不是真正不可变的。
本记录的“固定”含义是：
后续只能追加新的更正条目/新文件并引用本文件 SHA-256；
不应改写本文件；
若本文件被改动，SHA-256 校验会发现。

## 7. 结论

两份报告的共同结论：

paper-level 3.12 未验收；
原路线图在 D6、M2、H²、S2040、D5/D9、ledger 和 paper-level 陈述上都需要修正。

两份报告的不同点：
主要是 scope、证据基础和排期建议不同；
不构成互相否定；
也不构成谁更优的裁决。

我的责任：
按两份报告修正路线图和后续工作，
不改用户锁定的目标，
不把条件结果当完成。
