# SHEAF 具名 sorry 使用规则（2026-10-22 用户纠正）

用户指出：sorry 不能随便写，必须有条件/资格。此页把“允许的具名 sorry”收紧为可审计规则。

## 1. 允许的 sorry

只允许用于定理/引理（Prop）的证明体，且同时满足：

1. 有精确 Lean 类型：完整对象、变量、量词、假设、结论。
2. 有 DAG 节点和实际 consumer（文件:声明）。
3. 有来源：paper 定位或已有 Lean 供体；不能只凭名字。
4. 有自然语言证明步骤，或明确写出“缺哪条前置/构造”。
5. 有 exact gap：为什么现在不能证，缺什么 donor。
6. 记录在 node/queue/STATE；报告 statement_compiles，不报 proof。

## 2. 禁止的 sorry

禁止：

- 用 noncomputable def ... := by sorry 制造实际对象（curve、cover、diagram、root、Yddot、model、data、ATheta、q_v、theta 等）。
- 用 sorry 填 card/结构字段、空接口、任意 Type、任意数据。
- 用 sorry 把待证结论变成自由字段或自造假设。
- 对 false / 不可满足 / 与已知反例冲突的目标写 sorry。
- 用新增假设、缩量词、改对象来“绕过”缺口。
- 只为了 statement_compiles 而写没有 consumer/来源/证明步骤的 sorry。

## 3. 条件 sorry

若目标本身是条件定理，允许把论文原有的合格输入作为假设；必须记录：

- 条件来自原文哪条定义/假设；
- 条件不是为本证明临时新增；
- 实际构造该条件的责任另列节点。

若条件本身尚未构造，不能说目标已闭合；只能说“条件定理 statement_compiles”。

## 4. 对象尚未构造时的正确写法

不要用 noncomputable def sourceDiagram := by sorry 制造全局对象。

应定义 obligation 结构：

    structure SourceDiagramObligation where
      diagram : ...
      root : ...

下游定理显式接受 (D : SourceDiagramObligation)，从字段投影；不要依赖一个用 sorry 伪造的全局对象。

## 5. 当前审计

- S1/S2/SourceG2/F2/F3 的定理级 named sorry：按本规则复核。
- F8a–F8e 中 noncomputable def ... := by sorry 制造 sourceDiagram/sourceRoot/Yddot/model/data/factorization：违规，必须改为 obligation 参数/投影，不得保留任意对象。
- SourceG2Statement 的 preGaloisCategoryOfSourceG2/galoisCategoryOfSourceG2 若能由已有字段直接构造，应删除 sorry；若不能，改写为显式条件定理。
- 其余 tmp stage1/2 文件逐个按此审计。

## 6. 报告格式

每个 sorry 必须登记：

    file:line
    declaration
    exact type
    source/paper anchor
    consumer
    NL proof steps or exact missing donor
    condition provenance (if conditional)
    stage1/stage2 status
    why sorry is temporary
