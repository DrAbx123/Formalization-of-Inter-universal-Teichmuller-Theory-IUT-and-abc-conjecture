# 目标与定义审查

2026-10-22；本次由迁移执行者自审，没有独立审查或 comparator 验收。

## 审查规则

每个正式目标记录：原文版本/页码/命题、完整原文假设与结论、Lean 类型、逐项对应、引用定义到 Mathlib 的对应、差异及理由、审查者、文件/依赖版本、未决问题。只看类型名字不足以锁定。

本文件的条目可更新，变更理由追加 AUDIT_LEDGER；历史原文和失败结论不覆盖删除。

## `abc-target`：未锁定

- 现有命题：`LeanFormal.IUT.ABCConjecture`，定义位于 `LeanFormal/IUT/ABCBridge/Statement.lean`。
- 已核对表层量词：`∀ ε > 0, ∃ K > 0, ∀ a b c, IsABCTriple a b c → ...`。`K` 不依赖单个三元组。
- 尚需把 `PrimitiveAdditiveTriple`、`natRadical`、`ABCInequality` 的实际定义及已有字典证据纳入同一版本审查。
- 源文件关于 radical 的注释与 `radical_zero` 的表面取值不同；零不在正三元组范围，这本身不是 ABC 反例。锁定时按定义/定理核对有效定义域，不凭注释判断，也不为这点展开额外数论。
- 没有把既有条件桥定理当无条件 ABC 证明。
- 状态：`unreviewed_definitions`；Challenge 未创建，Lean 编译/公理检查本轮未重跑。

## `cor312-conditional-abc`：条件供体，非最终目标

- 源码表层类型：`(D : Cor312ToABCBridgeInterface.{u}) → ABCConjecture`。
- `D` 包含 carrier、hullData 和每个 ε 的比较；这些不是已构造的源对象。
- 当前文件明确说明其 value-monoid realization 未声称就是原文 IQ carrier，且接口非空性与 ABC 等强。
- 因而可复用其条件推导，不能把任意接口 inhabitant 视为 IUT 原路线验证。
- 状态：源码声明已核对；当前依赖版本的构建/公理/源比较未验收。

## `l03-g2-milestone`：局部目标候选

- 目标规格保留全部 finite G 和该覆盖范畴内全部作用图。
- `S` 的实际取值/范围、FiniteEtaleCover 的精确实例仍须从当前消费者冻结，不能把数学示意当 Lean 完整类型。
- scheme 的 G2 到 source orbicurve/fiber 不是 definitional equality；已有 consumer_trace 给出了实际连接缺口。
- sign quotient 可表示性另查，不能凭仿射路线缩小原目标范围。
- 状态：`needs_exact_source_scope`；没有锁定或声称接入完成。

## IUT III 3.11 / 3.12 / source Theta

当前只列候选入口，没有复刻原文完整命题或定义闭包。后续按实际工作节点补审查，不据模块名冻结；也不要求为了做一个已确定的局部引理先完成全项目审查。
