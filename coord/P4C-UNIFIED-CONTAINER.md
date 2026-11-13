# P4-C — 统一容器 / 全部允许像（Ind2 μ2l 与 Ind3 输出 hull）判定

日期：2026-11-13；hull。结论：**块级统一容器只能覆盖已经落到 qVFamTensorBlock 的输出 hull；Ind2/Ind3 的 stage 像没有到该块的 map，不能伪造包含。**

## 1. 现有实际块级对象（green）

| 对象 | file:line | 内容 |
|---|---|---|
| `ind3OutputHull` | Ind3OutputHullQPilotActual.lean:70-71 | `= rootNormHull`，实际闭包输出 hull |
| `ind3OutputHull_measure_lt_top` | Ind3OutputHullQPilotActual.lean:91-94 | 有限 Haar（rootNormHull_measure_lt_top） |
| `rootNormHull_measure_pos` | RootHullMeasureActual.lean:150 | 正 Haar |
| `ind3OutputHull_measure_pos_lt_top` | Mzk1PaperFaithfulHullActual.lean:122-129 | 正/有限 |
| `paperFaithfulThetaHull` | Mzk1PaperFaithfulHullActual.lean:97-98; P4 file | PaperNonzeroLabel、paperRootCoefficient 的 hull |
| P4 positive/finite | Mzk1PaperFaithfulHullP4Actual.lean | S1023 开性正性；S920 子集 canonical 有限 |

这两个 hull 是不同对象：`ind3OutputHull=rootNormHull` 用 `rootNormCoefficient`（supply c_norm），
`paperFaithfulThetaHull` 用 `qVFamPaperRootCoefficient=order/(2l)` 且只取非零标签；
没有等式；不能用一个替换另一个。

## 2. 为什么 Ind2/Ind3 不能直接加入块级容器

- Ind1/Ind2/Ind3 的实际作用在 `S1902Carrier`：
  `ind1Act` Mzk1ThetaPilotObjectActual.lean:84-87，`ind2Act` :90-94，`ind3Act` :98-101；
  `ind2Images` :108-110，`ind3Images` :113-115。
- L-valued 侧：`ind2LValued`/`ind3LValued` PaperFinalLValuedTensorCarrierActual.lean:66-74；
  `ind2Image`/`ind3Image`/`thetaImageIndUnion` PaperFinalLValuedThetaIndHullActual.lean:34-46。
- 从 stage 像到 qVFamTensorBlock 的 multiradial map **不存在**：
  `Ind3StageToOutputHullGap` Ind3OutputHullQPilotActual.lean:156-164（字段是 Prop，没有构造）。
- `FinalL = RootExtension = AlgebraicClosure`（PaperFinalLValuedTensorCarrierActual.lean:42），
  完整 `FinalLValuedCarrier` 非有限维，无 Haar 测度；不能把 L-valued 像直接放进块级 Haar 容器。
- `rootNormedExtension` 是基 completion 的有限中间域（PaperRootCompletionTensorActual.lean:58-60），
  与 `qVFamTensorBlock` 是 **不同域/载体**；无 trace/norm/restriction map。

## 3. 可安全陈述的统一容器（块级输出）

块级已有：
- `ind3OutputHull` 有限/正；
- `paperFaithfulThetaHull` 有限/正；
- 二者都在块上，但**不是同一 hull**。

可证的“统一容器”只能是给这两个**输出 hull 各自**的容器，例如 canonical `s920O`：
- paperFaithful 侧：S920 paperNonzero hull ⊆ canonical（P4 finiteness 使用）；
- ind3OutputHull 侧：由 green `ind3OutputHull_measure_lt_top` 给有限测度，但“⊆canonical”
  需要 `rootNormCoefficient` 侧的区域包含证明（当前未写；不是明显 rfl）。

**不可证**：把 Ind2 的 μ2l 轨道、Ind3 的 stage 像本身放入块级容器，因为缺 stage→block map；
若把 `ind3OutputHull` 当作 Ind3 像的容器，必须先证明 map 并在 map 下比较，不能直接说“像 ⊆ hull”。

## 4. 精确缺口

| GAP | 精确对象/位置 | 需要的实际构造 |
|---|---|---|
| GAP-P4C-STAGE-BLOCK | Ind3StageToOutputHullGap (Ind3OutputHullQPilotActual.lean:156-164) | 从 S1902Carrier/rootNormedExtension 到 qVFamTensorBlock 的 stage image map，并证与 Ind3 作用相容 |
| GAP-P4C-IND2-MAP | ind2Act/ind2Images (Mzk1ThetaPilotObjectActual.lean:90-94, :108-110) | Ind2 像落到块上的 map 或块级 Ind2 action；当前没有 |
| GAP-P4C-HAAR | FinalLValuedCarrier (PaperFinalLValuedTensorCarrierActual.lean:45, :71-90) | 非有限维 carrier 上的 Haar/测度；当前无 |
| GAP-P4C-HULL-ID | paperFaithfulThetaHull vs ind3OutputHull | 两者系数/标签不同；无等式；若目标要求同一 hull 需先补系数/标签修正 |

## 5. 结论

P4-C 的块级有限性/正性对**输出 hull** 已经 green；但“全部允许像”的 Ind2/Ind3 部分被 stage→block map 和
非有限维 L-valued carrier 两个实际缺口阻断。按不捏造原则，本轮不把 Ind2/Ind3 像塞进块级容器，
也不声称 Ind3 输出 hull 等于 stage 像的 container；记录上述 GAP，下一步需先构造 map（或换载体）。