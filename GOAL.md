# SHEAF 目标登记

更新时间：2026-10-22。目标是沿忠实于 IUT 原文的证明路线推进 3.11 → 3.12 → 算术结论/ABC，同时保留用户要求的原文更强结果。迁移不改变原命题强度，也不把这条路线本身当成已验证依赖链。

## 当前目标与候选

| ID | 内容 | 已有位置 | 当前状态 |
|---|---|---|---|
| `abc-target` | 标准整数 ABC 的 ε-常数命题 | `LeanFormal.IUT.ABCConjecture`，ABCBridge/Statement.lean | 有命题定义；没有本轮验收的无条件证明；未锁定 |
| IUT III 3.11 | 对原文合格初始数据的定理 | SourceOriginalInput / SourceTheorem311Assembly | 候选入口；完整原文逐项对应待定，不将任意 native/card 当成原对象 |
| IUT III 3.12 | 原文的 hull/volume 结论及其上下文 | Corollary312 与 SourceHullCompactnessReduction | 候选入口；实际载体与原文比较仍须核对 |
| IUT IV 算术过渡 | 将上述几何/体积结果变为实际高度比较 | Cor312ToABCBridgeInterface | 条件桥存在；不能用接口存在性代替原文证明 |
| `l03-g2-milestone` | 所需实际覆盖范畴的有限群商/G2 | 既有 FiniteEtaleCover / GaloisCategory 接口 | 局部里程碑；到实际 source 范畴/fiber 的桥另列；未锁定 |
| L0.4 / L0.5 | 实际 log 比较、source Theta 与 uniformization | 既有数学交接 | 按实际消费者逐包登记；本轮不新造总卡片 |

正式 DAG 目前只有 6 个局部节点，见 [dag/README.md](dag/README.md)。没有把全库自动提取成图，也没有给后三类候选虚构完整形式化陈述。

## ABC 陈述锚点

当前定义的精确正文为：

```lean
∀ epsilon : Real, 0 < epsilon →
  ∃ K : Real, 0 < K ∧
    ∀ a b c : Nat, IsABCTriple a b c → ABCInequality epsilon K a b c
```

其中 `ABCInequality` 是 `c ≤ K * radical (a*b*c)^(1+epsilon)` 的实数幂形式。锁定前须核对 `IsABCTriple`、`radical`、实数转换及幂的实际定义，不能仅审查名字和注释。

当前已见：

```lean
LeanFormal.IUT.cor312ToABCBridge_abcConjecture
  (D : LeanFormal.IUT.Cor312ToABCBridgeInterface) :
  LeanFormal.IUT.ABCConjecture
```

这是有参数 `D` 的条件定理。实际构造源忠实的 `D` 是另一项未闭合义务；源码还将接口非空性与 ABC 校准为等强。因此不能把 `Nonempty Cor312ToABCBridgeInterface` 当作廉价接口任务，也不能从 ABC 构造接口后循环宣称证明 ABC。

## 锁定和最终验收

当前 `locked_targets = []`。本轮没有生成空的 Challenge 或 TargetsCheck，没有用错误对象抢先锁目标。

冻结目标的逐项审查记录在 [coord/targets-review.md](coord/targets-review.md)。有准确陈述和完整来源的局部目标可以先锁定并推进，不等待全 IUT 图完成。最终目标的类型不能因选短路线而削弱；中间命题可以随完整证明路线修正。

最终接受同时要求：相同版本构建通过、Lean comparator 接受锁定 Challenge、目标传递公理检查通过、源语义审查有效。当前这些最终验收未执行。

## 不作为主线进度

未有真实消费者的通用数学、固定模型的重复验证、Project import 数、旧结论的合取、任意 card 的 inhabitant、只完成 regular/trivial action、没有同步的逐标签同构，都不自动算作目标推进。

给定合格初始数据的原文定理，与从更弱算术输入构造合格初始数据，是不同任务。不得擅自把后者加入前者的假设义务。
