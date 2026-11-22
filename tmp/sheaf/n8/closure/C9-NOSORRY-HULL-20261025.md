# C9 no-sorry SourceHolomorphicHull：obligation 化与反例

任务：task-481（No-sorry SourceHolomorphicHull）。owner：iplsheapt。日期：2026-10-25。目标文件：`tmp/sheaf/n8/closure/SourceHolomorphicHull.lean`。No fake/axiom/toy；只写本 MD；目标 Lean 文件按任务要求修改。

## 0. 结果

原文件的唯一 `sorry` 是：

```lean
theorem sourceHolomorphicHullData_nonempty ... :
  Nonempty (SourceHolomorphicHullData ... (B := B) ...) := by
  sorry
```

该命题对**任意** `C6ActualIQData` 值 `B` 是假的，因此不能证明，也不应保留为 sorry 或 axiom。现已：

```
(1) 用具体反例证明旧的无条件命题为 false；
(2) 用 exact obligations 结构替换原 sorry；
(3) 证明 hull package ↔ obligations；
(4) 证明 obligations ⇒ Nonempty；
(5) 删除旧的无条件 theorem（不是改成 axiom/toy）。
```

目标文件现在 **无 `sorry` 声明、无 `axiom` 声明、无 toy carrier**；编译：

```
pwsh -NoProfile -File D:/lean/tmp/n8-20261018/lead/lean-serial.ps1 env lean -j1 -R D:/lean tmp/sheaf/n8/closure/SourceHolomorphicHull.lean
# exit 0
```

## 1. Exact counterexample

原 theorem 对任意 `B : C6ActualIQData C3.tensorPlaces C3.tensorTuple mu` 断言

```
Nonempty (SourceHolomorphicHullData ... (B := B) ... n).
```

`C6ActualIQData` 的字段有默认值，但可以被独立覆盖。取

```lean
def emptyHullCounterexampleB : C6ActualIQData ... where
  hull := ∅
```

它的 `iqInterface` 仍是默认的 actual interface，其 hull 是 `arithmeticTupleCanonicalHull`，有 positive Haar mass，因而非空；而 `B.hull = ∅`。任何 `SourceHolomorphicHullData` 的 `iqHull_eq` 字段要求

```
B.iqInterface.hull = commonHull ... B = B.hull = ∅,
```

矛盾（canonical hull 非空由 `measure_arithmeticTupleCanonicalRegions_pos_lt_top` 证明）。目标文件中：

```lean
theorem emptyHullCounterexampleB_iqHull_ne_empty : ...
theorem not_sourceHolomorphicHullData_nonempty_emptyHull :
  ¬ Nonempty (SourceHolomorphicHullData ... (B := emptyHullCounterexampleB ...) ...)
```

因此旧 theorem 不是“漏证”，而是 **false**；保留其 sorry 会隐藏一个错误命题。

## 2. Exact obligations

目标文件新增

```lean
structure SourceHolomorphicHullObligations ... where
  iqHull_eq : B.iqInterface.hull = commonHull ...
  image_subset_hull : permittedImage ... ⊆ commonHull ...
  haar_pos : 0 < mu (commonHull ...)
  haar_lt_top : mu (commonHull ...) < ⊤
  qPilot_mem : qPilotPoint ... ∈ commonHull ...
```

其余字段不是新假设：

```
contains_permitted      由 image_subset_hull 推出；
hull_subset_scaleShift  由 B.iqInterface.hull_subset_scaleShift + iqHull_eq 推出；
logVolume_lt_top        由 IQHullLogVolumeInterface.hull_logVolume_lt_top + iqHull_eq 推出。
```

并证明：

```lean
theorem sourceHolomorphicHullData_nonempty_iff_obligations :
  Nonempty SourceHolomorphicHullData ↔ Nonempty SourceHolomorphicHullObligations
theorem sourceHolomorphicHullData_nonempty_of_obligations :
  SourceHolomorphicHullObligations → Nonempty SourceHolomorphicHullData
```

这是 exact conditional form，没有 fake/axiom。

## 3. Exact obstruction / downstream consequence

原 theorem 的 consumer（例如 `N8ClosureAchieved.lean`）用 `(B := C6ActualIQData.actual ...)` 调用它。现在必须改为：

```
(i) 提供 actual B 的 SourceHolomorphicHullObligations；或
(ii) 通过 C7Native 的 ThetaImageContainmentDonor / QPilotHullMembershipDonor 及 actual canonical hull 的 Haar positivity/finiteness 构造这些 obligations，再调用 sourceHolomorphicHullData_nonempty_of_obligations。
```

这不是本任务可自动补齐的：`image_subset_hull` 与 `qPilot_mem` 正是 C7Native 中仍未证的 donor（ThetaImageContainmentDonor、QPilotHullMembershipDonor）。`iqHull_eq`/Haar positivity 对 `actual` 可证，但 donor 不能由现有声明直接推出，也不能用 axiom/toy 字段替换。

## 4. What changed in target file

| item | status |
|---|---|
| old `sourceHolomorphicHullData_nonempty` sorry | REMOVED（false for arbitrary B） |
| `SourceHolomorphicHullObligations` | ADDED (exact fields) |
| `SourceHolomorphicHullData.ofObligations` | ADDED (constructs package) |
| `sourceHolomorphicHullData_nonempty_iff_obligations` | ADDED |
| `sourceHolomorphicHullData_nonempty_of_obligations` | ADDED |
| counterexample `emptyHullCounterexampleB` | ADDED |
| `not_sourceHolomorphicHullData_nonempty_emptyHull` | ADDED |
| `sorry` declarations | NONE |
| `axiom` declarations | NONE |
| fake/toy carriers | NONE |

## 5. Verification

```
target lines: see hash below
compile command: pwsh -NoProfile -File D:/lean/tmp/n8-20261018/lead/lean-serial.ps1 env lean -j1 -R D:/lean tmp/sheaf/n8/closure/SourceHolomorphicHull.lean
exit code: 0
grep: only the docstring word 'sorry'/'axiom' occurs; no declaration.
```

## 6. Conclusion

原文件唯一的 sorry 对应一个对任意 `C6ActualIQData` 为假的命题；不能用 proof 消除，也不能保留为 sorry/axiom。现已用 exact counterexample 证明其为假，并用 exact obligations/counterexample 替换。目标文件编译通过、无 sorry/axiom/toy。剩余实际数学义务是 `SourceHolomorphicHullObligations` 中的 `image_subset_hull` 与 `qPilot_mem`（以及 arbitrary B 情形下的 `iqHull_eq`/Haar 条件）；它们对应 C7Native 的 donor gap，不是本文件可伪造的内容。No mixed/E3; P6 open.

