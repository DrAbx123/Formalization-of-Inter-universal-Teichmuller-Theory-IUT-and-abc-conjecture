# S1784 — S1756FirstMissing / source retraction unit 2-cell

日期 2026-11-01。状态：**missing（未证明）**，按任务要求精确记录；无 fake 2-cell、无 fake equivalence。

## 交付物与证据

| 项 | 值 |
|---|---|
| 文件 | `tmp/sheaf/xif/paper/S1784SourceRetractionUnitActual.lean`（25892 字节，521 行） |
| SHA256 | `f88ba3003642a05ac589a7d54d2bc3a9b81e8f8101e5f7170b8c469cc53bbfa6` |
| 编译 | `lake env lean -j1 -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1784SourceRetractionUnitActual.olean <file>`，**EXIT=0**，无 error/无 sorry/sorryAx |
| olean | `.lake/build/lib/lean/tmp/sheaf/xif/paper/S1784SourceRetractionUnitActual.olean`（111656 字节） |
| 下游导入验证 | `tmp/sheaf/xif/paper/_S1784ImportProbe.lean` 导入该 olean 并 #check 主定理，**EXIT=0**，公理仅 `propext, Classical.choice, Quot.sound` |
| 编译方式说明 | 资源门控 `lean_auto.py repair` 当时返回 `resource_wait`（机器 CPU 满载，非数学问题），故改用直接 `lake env lean`；未使用 Project 全构建。 |

## 结论：S1756FirstMissing 未证明，且当前接口不足以证明它

`TwoPullbackWitness`（`Iut/Foundations/Orbicurve.lean`）只有 7 个字段：
`lift`, `liftToX`, `liftToY`, `liftTwoCell`, `liftTwoCell_toX`, `liftTwoCell_toY`, `twoCell_ext`。
其中 `twoCell_ext` 正好是比较函子 `Hom(W,P) ⟶ Cone(W)` 的**忠实性**；缺失的是它的反方向
（本质满/满性）：

> 给定锥 c（顶点 W）与 f : W ⟶ P，若 f ≫ toX ≅ c.toX 且 f ≫ toY ≅ c.toY，则 f ≅ lift W c。

没有这一条，`S1784EndTrans_toSource` / `S1784EndTrans_projection`（`toSource ≫ lift` 与 𝟙 有相同的两个投影）
无法升级为 2-cell `toSource ≫ lift ≅ 𝟙`；`twoCell_ext` 只比较同源同靶的 2-cell，帮不上忙。

**七字段不足以强制 unit**（可手工核对的 Cat 反模型，写在文件头，未形式化）：退化方块
X=Y=Z=𝟙，toX/toY/point 全为常值函子，P = 偏序 {0<1}（thin），lift := const 0。
七字段全部满足（`liftTwoCell` 取恒等 2-cell；两个投影等式两边都是子单元素；
`twoCell_ext` 成立因为 `[W,P]` 是 thin），但 `toSource ≫ lift = const 0` 与 𝟙 P 不同构（1 不是不动点）。
注意 P 非 thin 时 `twoCell_ext` 会被破坏（例如 P = C × Bℤ/2），所以 thin 是构造反模型的必要条件。

顺带核对：vendor 上游 snapshot 的同一结构（`vendor/promachina/snapshots/1fa6387f…/Iut/Foundations/OrbicurvePullback.lean:265-323`）
注释声称 “Essential surjectivity is represented by lift, liftToX, liftToY … Thus precomposition
with the two legs is an equivalence”，该声明超出了字段内容：`lift` 只定义在锥上，而任意 1-cell
不等于“它自己的锥的 lift”，这一点没有字段保证。

## 本文件新增的定理（全部已编译，公理干净）

无条件：

* `S1784EndTrans`：1-cell `toSource ≫ lift`，`S1784EndTrans_eval`：其 2-Yoneda 求值就是 `S1756End`。
* `S1784Section`：`lift ≫ toSource ≅ 𝟙`（S1756 已用的 counit，显式封装）。
* `S1784EndTrans_toSource` / `S1784EndTrans_projection`：`(toSource ≫ lift) ≫ toSource ≅ toSource`、
  `(toSource ≫ lift) ≫ projectionMap ≅ projectionMap`（后者把 `S1756End_projection` 证明内部的 1-cell 形式抽出）。
* **`S1784EndTrans_fixes_lift`：`lift ≫ (toSource ≫ lift) ≅ lift`。** 自同态固定 lift 的整幅像。
* **`S1784YonedaEval_lift_fixed`（方案层面）：** 对任意测试方案 U 与任意源点 `x : h_U ⟶ A.source`，
  `eval (x ≫ lift) ≫ S1756End = eval (x ≫ lift)`。即“来自 source 的模型点都是 S1756End 的不动点”。
  反例只能来自 source 看不见的模型点。
* **`S1784End_eq_one_of_point_from_lift`：** 若 `∃ x, x ≫ lift ≅ 𝟙 (S_A)`，则 `S1756End A = 𝟙`。
  与 S1756 的 `S1756End_eq_one_of_retraction` 等价（后者是 x = toSource 的特例），但本证明不用
  `S1756_unit_iso` 的双范畴消去。
* **`S1784FirstMissing_iff_idPoint_from_lift`：** `S1756FirstMissing` ⟺ 每个 cover 的模型单位点来自 source。
* **`S1784LiftPointSurj` / `S1784LiftPointSurj_of_unit` / `S1784End_eq_one_of_liftPointSurj` /
  `S1784FirstMissing_iff_liftPointSurj`：** 缺失命题 ⟺ lift 在测试方案点上满射（模型每个点都来自 source）。
  这是“几何上缺什么”的最简等价形式，且说明自同态本身没有额外隐藏结构。
* `S1784Retraction_iff_point_from_lift`：S1743 的 retraction 判据 ⟺ 上述点判据。

条件（把缺失的万有性质补上即闭合）：

* `S1784PullbackCone`、`S1784Counit`（pullback 自己那个锥的 lift）、`S1784CounitData`（两个 2-cell 的极小输入）、
  `S1784End_eq_one_of_counitData`。
* **`S1784LiftEssSurj`**（上面那条缺失的满性，作为显式谓词）与
  **`S1784End_eq_one_of_liftEssSurj` / `S1784FirstMissing_of_liftEssSurj`**：
  补上它即得 `S1756FirstMissing`；并得 `S1784Retraction_of_liftEssSurj : S1743SourceRetraction`、
  `S1784SourceRepresentableAll_of_liftEssSurj : S1756SourceRepresentableAll`。

## 未做 / 未证（如实记录）

* `S1756FirstMissing` 本身**未证明**；`S1784LiftEssSurj A`（甚至其单锥形式 `S1784CounitData A`）对任何 cover 都未构造。
* 未形式化 Cat 反模型（需要把 `TwoPullbackWitness` 泛化到任意双范畴并在 `Cat` 中实例化；`CategoryTheory.Cat.bicategory` 存在，但本轮编译预算未做）。反模型在文件头逐条列出，结论可手工核对。
* S1756 的 projection-mono 特例（`S1756End_eq_one_of_mono`）仍是唯一已证的方案层面充分条件；
  与新增的点判据互不包含，二者是同一 gap 的两种记录。
* 未改 `AUDIT_LEDGER.md` / `coord/STATE.md` / `coord/queue.md`（避免与协调者并发写冲突），请协调者代录。

## 一个可执行的下一步

真正闭合只有两条路，且都必须补上“满性”这一半：

1. **补字段**：在 `TwoPullbackWitness`（或并行新结构）加入
   `lift_uniq : ∀ W c f, (f ≫ toX ≅ c.toX) → (f ≫ toY ≅ c.toY) → Nonempty (f ≅ lift W c)`，
   然后对所有 cover 用 `S1784FirstMissing_of_liftEssSurj` 直接收口。注意这是**加强定义**，需要重审
   `EtaleStackBaseChangePresentation` 的所有既有 inhabitant，不能悄悄替换。
2. **构造真 pullback**：把 `(A.map, 𝟙)` 的二范畴拉回显式做成 iso-comma 伪函子 P′（逐点：
   P′(U) 的对象 = (x ∈ source(U), y ∈ Hom(U, Spec R′), A.map(x) ≅ y)；因 Hom 集是离散的，
   P′ ≃ source），证明 P′ 满足完整万有性质，再证 presentation 的 `h_{S_A}` 与 P′ 等价。
   难点已在 S1756 指出：现有弱字段不足以给出 `h_{S_A} ≃ P′`，所以第 1 条或“把 `isPullback`
   改成从 P′ 出发的具体等价”二者至少要做一个。

在 (1) 或 (2) 完成之前，S1743 item (a)、`S1756FirstMissing`、`S1756SourceRepresentableAll`
都保持未闭合。
