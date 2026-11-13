# CANDIDATE-ORDER 输入：定义级障碍说明

日期：2026-11-13 19:0x。Status: READ-ONLY 分析；不接管 S1413/S2680。

## 目标输入

`CANDIDATE-ORDER`: 对所有 `b : Bad (nativePlaceSelection T)`，

`(badPlaceQCandidate (nativePlaceSelection T) b).order = (sectionQ T b).order`。

## 定义对照

- `badPlaceQCandidate`（`SourcePlacePartitionReduction:684`）是 source section 的 K-side q candidate，由 `finitePlaceQCandidate_nonempty` 的 `Classical.choice` 在 `sectionFiniteLift` 上构造；
- `sectionQ`（`S1413SourceKPlaceQComparisonActual:199`）是 `FinitePlaceQCandidate.map` 作用于 `shadowQ`，`shadowQ = Classical.choice (T.clauseB.q_comparison sectionFPlace ...)`；
- `sectionQ_order`（S1413:211）只给出 `sectionQ.order = eSource * shadowQ.order`；
- S2680 的 `fkDescentScaledShadowStatement_nativeCard_of_sectionQAgreement`（:306-317）及 `tateQIdentificationStatement_of_sectionQAgreement`（:332-343）把该 order 等式作为**显式假设 hQ**。

## 结论：没有定义级等式

1. `badPlaceQCandidate.order` 是 source DVR candidate 的 order；`sectionQ.order` 是 clause-B q candidate 的 completion image 的 order；两者底层 q 元素/构造不同。
2. S1413 只联系 `sectionQ` 与 `shadowQ`，不联系 `badPlaceQCandidate`。
3. S2680 也把该等式作为 hypothesis，不证明。
4. 因此 candidate-order 是**独立算术/对象输入**；不能由 `rfl`/`unfold`/`simp` 得到。要关闭它，需要构造/证明 `badPlaceQCandidate = sectionQ`（或至少 order 相等）的实际 q candidate 识别。
