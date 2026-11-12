# N8 label 结构更正（2026-10-23）

依据：IUT III corpus 544-570。

原文：
- label 是有限集合 S_{j+1} = {0,1,...,j}，j=0,...,l^⋇；
- 每个 S_{j+1} 带 arbitrary permutation automorphisms；
- 不是 AddGroup，不是 Group，也不是 Multiplicative LAdd。

更正：
- C0 的 `[AddGroup Label]` 只是 `SourceTheorem311Realization` 的生产索引表示，不是原文 label 语义；
- C4/C5 的 `[Group Label]` 是形式化工具，不能当原文 label；
- T1 不再是 AddGroup↔Group bridge；T1 改为 `LabelData`/`ProcessionLabelData`：有限集合 + `Equiv.Perm` action，并单独给出 production additive index 与 label set 的显式比较；
- C4/C5 的 Ind1/Ind2 应最终改为 `Equiv.Perm Labels`/permutation action，而不是抽象 Group Label；
- 任何把 label 当加法群/乘法群/`LAdd` 的旧描述都作废。

影响：
- C0-STAGE1.md、C4-STAGE1.md、C5-STAGE1.md、N8-CLOSURE-TASKS.md 需按此更正；
- N8Closure.lean 不能建立在 AddGroup/Group 统一桥上；
- C10 full output 的 label 字段必须引用 LabelData/permutation 结构。