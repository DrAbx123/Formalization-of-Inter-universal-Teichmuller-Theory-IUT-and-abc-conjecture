# S1904：实际 thetaHull/determinant 上的 procession 桥

日期：2026-11-01。任务：在 S1902/S1903 的实际 thetaHull/determinant 上证明 S1880 的 D 第三字段

    thetaHull.haar.logVolume thetaHull.compactHull.hull
      = ENNReal.ofReal determinant.procession.average

（IUT III, Step (xi-d)/(xi-e) 的 procession normalization），或给出精确第一 missing；不得 fake。

## 结论（先给结果）

**该等式不能被证明，且它不是实际数据的推论；在显式实际 determinant 上它是假的。**
S1904 给出它的精确分类，并把真正的缺口归约成一个具名、可检验的算术 Haar readout 构造。

1. [已证] 桥 → `0 ≤ average` 且 `average ≤ 1`（`s1904_bridge_average_le_one`）。
   下界对任意实际 determinant 无条件成立（`s1904_processionAverage_nonneg`），
   上界来自实际 theta hull 的归一化（`s1904_hullLogVolume_le_one`，即
   `ActualThetaHull.hull_logVolume_le_one`）。
   若 `average ≠ 1`，桥还强制 `¬ unitRegion ⊆ hull` 与 `¬ scaleShift '' unitRegion ⊆ hull`
   （`s1904_failure_conditions_of_bridge_ne_one`）。
2. [已证] 存在实际 determinant，其 procession 平均 = 2（`s1904UniformDeterminant`：
   壳层标度 `exp 2`、单位参考包、tensor power 1、均匀权重 `1/l`、权重和 1，
   真 `SignedHullLogActual` 居民），而**对每个**实际 theta hull 桥在该 determinant 上为假
   （`s1904_bridge_false_of_one_lt_average`、`s1904_bridge_not_derivable`）。
   因此 `OrigXiFPaperSignedHullData` 在 "determinant = 该 exp 2 包" 上无居民
   （`s1904_no_datum_with_average_gt_one_determinant`），S1880 D 字段不是其余字段的推论。
   新推论：**每个** D 都满足 `determinant.procession.average ≤ 1`
   （`s1904_datum_average_le_one`）。
3. [已证] 反过来，给定实际 theta hull 几何，theta 侧 readout 的可达值恰为 `[0,1]`：
   对任意 `a ∈ [0,1]` 存在真正的 `OneCircUHaarNormalization`（同空间、同 unit region、
   同 scaling、单调、`logVolume unitRegion = 1`、scaling 不变）使 hull 值 = `ofReal a`，
   并有 D 使桥成立且 `average = a`（`s1904LevelHaar`、`s1904_exists_datum_of_average_between`）；
   `a = 1` 不需任何非退化假设（`s1904UnitHaar`、`s1904_exists_datum_average_one`、
   `s1904_exists_datum_of_average_between'`）。
4. [已证] 桥 ⇔ 有限（`toReal`）实值恒等式（`s1904_bridge_iff_toReal`）⇔ 符号形式
   `-|log Theta| = -average`（`s1904_bridge_iff_signed`）；同一 theta hull 上两个满足桥的
   determinant 必须有相同平均（`s1904_average_unique`）。
5. [已证] **三字段结构相对 theta hull 不增加内容**：
   `Nonempty (OrigXiFPaperSignedHullData X l) ↔ Nonempty (ActualThetaHull X l)`
   （`s1904_nonempty_datum_iff`；正向由 `s1904_nonempty_datum_of_thetaHull` 给出：
   把 Haar 泛函重归一化为 hull 上取 1 的 up-set，并取平均 1 的均匀 determinant）。

## 对 S1905 消费者的重要警告

S1905（`S1905Unconditional312Actual.lean`，已 import 本文件）用 `s1905_nonempty_iff` 把
无条件 3.12 归约到 `Nonempty (OrigXiFPaperSignedHullData X l)`。由 5，该目标**等价于**
`Nonempty (ActualThetaHull X l)`，而 `ActualThetaHull` 的每个字段都是可自由给出/无证明义务的
（`logVolume` 是任意函数字段；`paper_IQCarrier_realization` 是 `Prop` 槽），且由 3 桥在
Haar 泛函自由时总能满足。因此 "D 非空" 不能作为原文 Step (xi-d)/(xi-e) 的验收目标：
真正的内容必须在 `ActualThetaHull` 的**源构造**（IQ 载体实现）与**算术 Haar readout** 中。

## 精确第一 missing

现有接口上 `ActualThetaHull.haar.logVolume` 只是无约束函数字段（仅受单调性、
`logVolume unitRegion = 1`、scaling 不变约束）。由 1-3，D 第三字段的全部内容 =
进程序平均落在 `[0,1]`（真约束，见 2 的反例）+ 对 Haar 泛函 hull 读数的选择，
所以它不可能作为"进一步代数定律"被证明。真正缺的是**从实际算术 Haar 测度构造 readout 本身**：
把 `logVolume` 取为某个 `Measure.IsAddHaarMeasure mu` 的归一化 log-volume，并证明其 hull
值等于实际 determinant-procession 平均。这正是项目里已有的具体缺口形状：

    HaarSignedAverageProof.SignedUnitFactorThetaComparison
    arithmeticTupleHullUnitLogVolume places tuple
      + Real.log (mu (arithmeticTupleCanonicalUnitReference places tuple)).toReal
      = (c3ThetaSignedProcession C3).average

（`tmp/sheaf/xif/paper/HaarSignedAverageProof.lean`；C6 载体，Haar 侧是真正的
`Measure.IsAddHaarMeasure mu`）。换言之：C6 型恒等式（外加 `average ≤ 1`）才是 D 第三字段
在原文语义下的唯一实质内容；在抽象 `ActualThetaHull` 接口上无法再进一步归约。

## 证据

- Lean：`tmp/sheaf/xif/paper/S1904ProcessionBridgeActual.lean`
  - 697 行，33388 字节，SHA256 `B31C647468542F44DD1048B9F26DC27AB72997FFCE5C5B2214F0C3E54445EB8F`
  - 编译：`lake env lean -R D:/lean tmp/sheaf/xif/paper/S1904ProcessionBridgeActual.lean`，
    EXIT=0，无 warning，无 sorry/admit/axiom
  - olean：`.lake/build/lib/lean/tmp/sheaf/xif/paper/S1904ProcessionBridgeActual.olean`
    318384 字节，SHA256 `3C5761EC8D3DE0567E12A34FACF59BDD7C6F7980C254D5E19B931432D9B3A7F0`
  - axioms：全部主定理仅 `[propext, Classical.choice, Quot.sound]`（文件内 `#print axioms`）
- Consumer probe：`tmp/sheaf/xif/paper/_S1904ConsumerProbe.lean` EXIT=0，
  验证 S1905 使用的接口形状（`S1904ProcessionBridge`、`s1904_bridge_not_derivable`、
  `s1904_bridge_average_le_one`、`rw [FirstMissing, s1904_bridge_iff_signed]; rfl` 模式、
  `s1904_datum_average_le_one`）。
- 未修改：`S1880OriginalXiFActual.lean`、`ThetaHullActual.lean`、
  `SignedHullLogActual.lean`、`OrigXiFPaperSignedHullActual.lean`、`S1905Unconditional312Actual.lean`。

## 边界与未完成

- S1904 **没有**断言桥；`S1904FirstMissing` 是具名 Prop，仅登记为待构造对象。
  `target_accepted` 仍为 false。
- 共享工作区并发编译（中心 watchdog / 其他 agent 正在重建 mathlib 与 LeanFormal olean）
  会造成 `failed to read file ... .olean.private` 之类的瞬时 IO 失败；本包编译与 S1905 编译
  都遇到过，重试即通过或属他人构建，与文件类型/接口无关。S1905 最后一次本地编译仍卡在
  mathlib 私有 olean 读取（并发噪声），其与本包的接口已由 consumer probe 独立验证通过。
- 未运行：全 Project 构建、comparator 验收、中心 watchdog 队列、独立人工审查。
  本包不改 coord/queue.md、coord/STATE.md、AUDIT_LEDGER.md（由协调层整合）。

## 追加（2026-11-01 13:31）：S1902 实际 theta hull 出现后的具体化

S1902 已落地并构造出真正的实例
`s1902ActualThetaHull T : ActualThetaHull (S1902Carrier T) l`
（`tmp/sheaf/xif/paper/S1902ActualThetaHullActual.lean`）：
`haar.logVolume = haarLogVolume (s1902NormalizedHaar T)`（实际乘积 Haar 的归一化，
使 `logVolume O = 1`，见 `s1902LogVolume_unitRegion`），hull = 闭球乘积
`rootExtensionProductImageHull T`，unit region = 单位球乘积，且 `paper_IQCarrier_realization`
被真正证明。S1902 自己明确不证与本包的桥。

把 S1904 的结论用到该实例（无需新增证明，只是把 1-4 特化）：

- 对任意实际 determinant `P`，桥在 `s1902ActualThetaHull T` 上成立
  **当且仅当** `P.procession.average = a0`，其中
  `a0 := (s1902LogVolume T (s1902Hull T)).toReal`；且 `0 ≤ a0 ≤ 1`
  （由 `s1902Hull ⊆ O` 与 `ActualThetaHull.hull_logVolume_le_one`）。
  即：实际 theta hull **唯一确定** determinant 的 procession 平均为 `a0`。
- 因此原文 (xi-d)/(xi-e) 在 S1902 载体上的实质内容就是数值恒等式
  `procession average = a0`，其中（待独立验证的比例计算）
  `a0 = 1 + Σ_{b : Bad} [K_b : Q_p] · log(rootImageRadius T b)`
  ——这可由 `rootExtensionProductHaar` 在乘积上的因子化、单位球归一化与
  `rootImageRadius_eq_norm_fieldLambda`（`PaperRootExtensionFieldScalingActual.lean`）
  得到；相关度量事实已有 `rootExtensionProductImageHull_measure_pos_lt_top`。
- 反过来，取均匀标度 `exp a0` 的实际 determinant 即可证
  `∃ P, S1904ProcessionBridge (s1902ActualThetaHull T) P`，
  于是 `Nonempty (OrigXiFPaperSignedHullData (S1902Carrier T) l)` 在真实 theta hull 上成立。
  但这是"选 determinant 去匹配 a0"，**不是**源 determinant 的证明；验收口径必须区分
  "D 非空"（可满足）与"源 determinant 的 procession 平均等于 a0"（真实缺口）。

S1904 文件**没有** import S1902：S1902 是 13:25 新落地的文件，为避免把已验证 EXIT=0 的
本包绑到仍在演化的依赖上，上述特化留给下一个包（建议：import S1902 + S1904，证 `a0` 的
因子化公式与 `a0` 域，再构造/识别源 determinant）。
