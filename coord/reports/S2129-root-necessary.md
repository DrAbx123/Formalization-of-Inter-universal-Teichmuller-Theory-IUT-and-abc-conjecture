# S2129: paper completion root – necessary divisibility audit

日期: 2026-11-02
任务: 核对 S1413/S2032/Theta/S2092/S2040 的当前 source 数据是否已经蕴含
paper completion root q_v^(1/2l) 所必需的

- l ∣ eSource
- 2l ∣ ord(q_v)

若不蕴含，记录 root 目标在现有数据上可能 unreachable 的精确理由，以及需要补的
source 条件。不构造 fake root，不改目标。

Lean 文件: tmp/sheaf/xif/paper/S2129RootNecessaryActual.lean

## 1. 目标与必要条件（已由 S2092/S1413 证明）

目标未改变:

- paperOtriRootMissing T b := SectionTwoLRootRequired T b
  := Nonempty (SectionTwoLRoot T b)
- SectionTwoLRoot 的字段: root : Completion (sectionKPlace T b),
  root_pow : root ^ (2 * l.value) = (sectionQ T b).q
- S2092 的 paperOtriRootMissing_iff 把它等同于 paperOtriRootInCompletion
  (额外要求 root 在 O^⊿ 中)，两者等价。
- S2040 的 s2040PaperOtriAttachmentActual 的 qv_root_attachment 字段
  定义上就是 paperOtriRootMissing (rfl)，所以 S2040 没有把这个字段变成证明。

S2092/S1413 已经证明:

- paperOtriRoot_forces_l_dvd_ramification
  : root -> l.value ∣ eSource T b
- paperOtriRoot_forces_twoL_dvd_order
  : root -> 2 * l.value ∣ (sectionQ T b).order

其中 eSource T b = fkDescentSectionRamificationIndex (nativePlaceSelection T) b.1
是 restriction-section lift sectionFiniteLift 的 K-place 相对其 F-shadow 的
分歧指数；sectionQ 是 clause-B q 参数沿该 K-place 的完备化像。

## 2. 核查结果：当前数据不蕴含这两个整除条件

### 2.1 S1413 SourceKPlaceQComparison

提供:

- sectionFPlace / sectionKPlace 的 comap 方图；
- shadowQ (源 F-side q)，shadowQ_order_coprime: Coprime shadowQ.order l；
- sectionQ 与 sectionQ_q = rfl；
- sectionQ_order: sectionQ.order = eSource * shadowQ.order；
- sectionQ_valuation 及 norm/log 归一化；
- l_dvd_ramification_of_root, two_l_dvd_order_of_root (必要条件本身)。

不提供:

- eSource 的具体值或任何整除性；
- shadowQ.order 的奇偶性；
- 任何从 clause A/B/C 推出 l ∣ eSource 或 2 ∣ shadowQ.order 的定理。

关键点: SourcePlaceSelection 只有 V_mod_bad、奇剩余特征和非空三个字段；
section 是规范 restriction section。源 clause (a)--(f) 约束剩余特征、q-order
与 l 互素、l-torsion kernel field 和 Tate 比较，但没有一条约束所选 K-place
相对 F-shadow 的分歧指数。S1413 自身也明确把 SectionTwoLRoot 列为 missing，
并说根强制 l ∣ eSource，而不是反过来。

### 2.2 S2032 / Theta 数据

S2032 的局部模型给出 localOFieldQParameter D b = 5 ^ paperQVOrder D b。
可用的 order 事实只有 paperQVOrder_pos: 0 < paperQVOrder D b；没有
2l ∣ paperQVOrder。

本包进一步在该 Q_5 模型中证明:

- s2032_q5_root_of_twoL_dvd: 若 2l ∣ m，则 5^m 在 Q_5 中有 2l 次根；
- padic_five_pow_no_twoL_root: 若 2l ∤ m，则 5^m 在 Q_5 中没有 2l 次根；
- s2032_q5_root_iff_twoL_dvd: 因此 S2032 的 q_v 在模型域 Q_5 中
  存在 2l 次根当且仅当 2l ∣ paperQVOrder。
- s2032_no_q5_root_of_not_twoL_dvd: 同一结论的失败侧形式。

这既确认整除条件是真实障碍，也确认 S2032 的数据没有提供它。

Theta 侧: hodgeTwoLthRoot 是 F-side qVFamily 在 qVPlace = (nativeBadLift T).lift b
的 algebraic-closure root (hodgeTwoLthRoot_pow)。S342/S2092 的
theta_side_no_completionRoot 证明同一个 F-side q 在该完备化中根本没有
completion root。因此 Theta 侧根不能替换 paperOtriRootMissing：它不在
sectionKPlace，且其所在位置的 completion root 已被排除。Theta 的根系数
qVFamPaperRootCoefficient = order(qVFamily)/(2l) 是实数，对任意 order 都有定义，
不要求 2l 整除 order。

### 2.3 S2092 / S2040

S2092 给出实际 O^⊿/q_v/O^×μ 载体和根的必要条件，但没有根。
S2040 的 s2040PaperOtriAttachmentActual 只把 paperOtriRootMissing 放进
qv_root_attachment 字段；定理 s2040_root_attachment_eq 是 rfl，证明目标未改，
也证明 S2040 没有新增根或整除性证明。

## 3. 形式化的“记录数据不足”证据

S1413 记录的唯一 order 算术是

  ord(q_v) = eSource * ord(shadowQ),  Coprime ord(shadowQ) l.

本包在 Lean 中证明这个抽象数据不足以推出两个条件:

- order_law_counterexample_l_not_dvd:
  exists e m, Coprime m l /\ not (l ∣ e)  (e = m = 1)
- order_law_counterexample_l_dvd_not_twoL:
  exists e m, Coprime m l /\ l ∣ e /\ not (2l ∣ e*m)  (e = l, m = 1)
- not_uniform_twoL_dvd_factorization:
  not (forall e m, Coprime m l -> 2l ∣ e*m)  (S467 反例，重述)

并把精确的算术化简形式化:

- l_dvd_order_iff_l_dvd_ramification:
  l ∣ sectionQ.order <-> l ∣ eSource
- twoL_dvd_order_iff_order_and_two:
  2l ∣ sectionQ.order <-> (l ∣ sectionQ.order /\ 2 ∣ sectionQ.order)
- two_dvd_order_iff:
  2 ∣ sectionQ.order <-> (2 ∣ eSource \/ 2 ∣ shadowQ.order)
- twoL_dvd_order_iff_ramification_and_two:
  2l ∣ sectionQ.order <->
    (l ∣ eSource /\ (2 ∣ eSource \/ 2 ∣ shadowQ.order))
- rootNecessary_iff_twoL:
  (l ∣ eSource /\ 2 ∣ sectionQ.order) <-> 2l ∣ sectionQ.order

这说明: l-part 正好是 l ∣ eSource；2-part 是独立的 parity 输入，可由
2 ∣ eSource 或 2 ∣ shadowQ.order 提供；两者都没有被现有 source 数据证明。

S1284 已经对 qVFamilyK lift 证明同一精确化简
(2l ∣ qVFamilyK.order <-> l ∣ qVFamilyKRamificationIdx 且 2 ∣ qVFamilyK.order)，
S1281 在该 lift 上证明 root -> 2l ∣ order、root -> l ∣ ramification 及相应的
refutation。本文件是同一算术在 paper section K-place / sectionQ 上的版本。

## 4. root 目标可能 unreachable 的精确判据

本包证明:

- not_root_of_not_l_dvd:
  not (l ∣ eSource) -> not paperOtriRootMissing
- not_root_of_not_twoL_dvd:
  not (2l ∣ sectionQ.order) -> not paperOtriRootMissing
- not_root_of_not_two_dvd:
  not (2 ∣ sectionQ.order) -> not paperOtriRootMissing
- not_root_of_not_necessary:
  not (l ∣ eSource /\ 2 ∣ sectionQ.order) -> not paperOtriRootMissing

因此，若在实际 T,b 上能证明 l ∤ eSource 或 2l ∤ ord(q_v)（或 2 ∤ ord），
root 目标不是“还没填的 gap”，而是直接被反驳。当前树没有证明任一条件成立，
也没有证明其否定；但可以确定的是，按现有数据不能推出它们。

即使两个整除条件都成立，也不足以得到根: S1413/S472/S1449 已记录，
2l ∣ ord 只是必要条件，仍缺单位部分的根下降与指定完备化中的实际根。

## 5. 需要补的 source 条件（精确形式）

1. S2129LDivRamification T b := l.value ∣ eSource T b
   （等价地 l ∣ sectionQ.order）。这是论文指定 section K-place 的局部分歧
   整除性。应由源级局部分歧理论给出；S472 对 qVFamilyK lift 命名的
   KLocalRamificationDivisibleByLGap 是同类缺口。

2. S2129TwoDivOrder T b := 2 ∣ sectionQ.order。
   充分条件二选一:
   - 2 ∣ eSource T b，或
   - 2 ∣ shadowQ T b.order。
   论文侧来源是 q_v 为平方 / 2*3-torsion 输入，但当前树没有把
   Torsion23Rational 转成 q-order parity；S472 的
   TwoTorsionToQOrderParityGap 正是这个缺口。

3. paperOtriRootMissing T b 本身: 指定完备化中的 2l 次根。
   即使 1、2 都成立，仍需要单位部分/根下降的实际构造或论文允许的源输入；
   不得用 algebraic-closure root、Theta root 或 F-side qVFamily root 替代。

## 6. 构建与验收

命令:

  lake env lean -j1 -R D:\lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S2129RootNecessaryActual.olean tmp/sheaf/xif/paper/S2129RootNecessaryActual.lean

EXIT = 0
stdout 无 error/warning；构建日志 tmp/sheaf/xif/paper/S2129Build.log。
olean 已由临时模块 _S2129OleanCheck.lean 重新 import，EXIT = 0。

文件:

- source: tmp/sheaf/xif/paper/S2129RootNecessaryActual.lean
  SHA256 = 361DBB18C6B33088A08FC77A06787E0D26F73AE1413097A134934B36DFF1B28E
  432 行（构建后未再编辑）
- olean: .lake/build/lib/lean/tmp/sheaf/xif/paper/S2129RootNecessaryActual.olean
  SHA256 = BD77E932139798DB33CCF2488D3B2CB710386725B6167D7446C10388A66DE7E8
  size = 286904 bytes

公理审计（#print axioms，全部在文件内）:

- 所有报告定理只依赖 [propext, Classical.choice, Quot.sound]
- not_uniform_twoL_dvd_factorization 只依赖 [propext, Quot.sound]
- 无 sorryAx

未运行: 全 Project 构建、comparator、独立人工审阅。本包只做单模块 kernel
验收与 olean import 验证；不宣称 tree 已 closure，不宣称根存在或不存在。

## 7. 结论

- 当前 source 数据没有蕴含 l ∣ eSource，也没有蕴含 2l ∣ ord(q_v)。
- 现有数据能证明的是: 根 -> 两个整除条件；以及两个整除条件失败 -> 根被反驳。
- 精确缺口是 l ∣ eSource 与 2 ∣ ord(q_v) 两个 source 级算术输入，外加
  指定完备化中的根本身。
- 目标未改；paperOtriRootMissing 仍是 S1413/S2092 的同一个 Prop；
  S2040 的 root 字段仍是它（rfl）。没有构造 fake root，没有新增 axiom。