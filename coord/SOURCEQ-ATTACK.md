# SOURCEQ-ATTACK — S1012 的 `sourceQ` Prop 逐个攻 (A1129)

| field | value |
|---|---|
| Status | ATTACK RESULT: **不可由展开/定义相等证明**；S1026 已给精确等价 + 条件定理；剩余为精确 GAP |
| Prop 位置 | `S1012FinalChecklistActual` L43-48: `structure S1012FinalExactChecklist where fOpen ... sourceQ : Prop; sourceLink : Prop; finiteLinkEvidence : Prop` |
| sourceQ 内容 | S1009 的 `S1009SourceQIdentification I C3 := sourceQPilotSignedLog I.initial = localSignedLog C3.q`（S1009HQHC3Actual:61-64） |
| 精确形式 | `S1026SourceQExactFormula I C3 := -(∑ b : I.initial.badPlaces, |Real.log (I.initial.reduction.qParameter b)|) = Real.log ‖C3.q.q‖`（S1026:43-48） |
| 判定 | **GAP-SOURCEQ**：没有定理把 `I.initial.reduction.qParameter`（任意 Real 数据字段）与 `C3.q.q`（donor 构造的 q candidate）联系起来；不可 rfl/展开 |

## 1. 精确定义（源级）

```lean
-- S1009HQHC3Actual.lean:61-64
def S1009SourceQIdentification (I) (C3) : Prop :=
  sourceQPilotSignedLog I.initial = localSignedLog C3.q

-- S1026SourceQIdentificationActual.lean:43-48（精确公式形式）
def S1026SourceQExactFormula (I) (C3) : Prop :=
  letI : Fintype I.initial.badPlaces := I.initial.bad_finite;
  -(∑ b : I.initial.badPlaces, |Real.log (I.initial.reduction.qParameter b)|) = Real.log ‖C3.q.q‖

-- S1026:51-57（已证：两者等价，rfl）
theorem s1026SourceQIdentification_iff_formula :
  S1009SourceQIdentification I C3 ↔ S1026SourceQExactFormula I C3 := by
  letI ...; unfold ...; rfl

-- S1026:60-63（条件定理）
theorem s1026SourceQIdentification_of_formula (h : S1026SourceQExactFormula I C3) :
  S1009SourceQIdentification I C3
```

## 2. `qParameter` 与 `C3.q` 的来源（为何不可展开相等）

### 2.1 `qParameter`：SourceDefinition31Data 的**任意 Real 数据字段**
```
SourceDefinition31Data（SourceDefinition31Boundary.lean:667-690）
  reduction : SourceReductionClause selectedPlaces badPlaces
  reduction.qParameter : badPlaces → Real          （任意 Real 函数；无有限位/完成元）
S1487SourceData（S1487:400-424）: reduction.qParameter := q  （调用者任意给定）
S1487FaithfulSourceData: q := fun _ => ‖S1487Cand.q‖
```
### 2.2 `C3.q`：donor 构造的 q candidate
```
SourcePilotRegionData（ported lana）字段 q : FinitePlaceQCandidate（由 donors/qPilotLineOfSource 构造）；
c3WithSourceTheaterTheta（ThetaPacketQIdentificationActual:75-79）只改 thetaPacket，不改 q；
actualGaussianC3（C3GaussianThetaPacketActual:91-92）来自 donor D；
S1487Cand（S1487:133-134）是 `Classical.choice (finitePlaceQCandidate_nonempty ...)`，
  只提供 `localLogMagnitude S1487Cand = order * log 5`（S1487:152-154），
  **不是** C3.q 的定义，也没有 `C3.q.q = S1487Cand.q` 的定理。
```
**结论**：`qParameter` 是抽象 Real 族，`C3.q` 由另 stack（donors/qPilotLine）构造；两者之间
**没有任何定义/定理**连接；`S1026SourceQExactFormula` 不是 rfl，也无法由展开得到。

## 3. 为什么 S1026 只能给等价/条件式

```
S1026 的 `s1026SourceQIdentification_iff_formula` 是 rfl 等价（把 S1009 的定义展开成公式）；
`s1026SourceQIdentification_of_formula` 是条件定理；
S1026 文件头（:8-9）：concrete source data currently provide no relation between qParameter and C3.q,
  so the formula equality is the exact minimal input.  No fake proof.
⇒ 与我们审计一致：**不可无条件证**。
```

## 4. 精确 GAP 与可证条件

```
GAP-SOURCEQ := S1026SourceQExactFormula I C3
  ⇔ -(∑_b |log qParameter b|) = log ‖C3.q.q‖
  ⇔ sourceQPilotSignedLog I.initial = localSignedLog C3.q   （等价，已证）

证明它需要（任一）：
(a) 构造性联系：让 C3.q.q 由同一 qParameter 族定义（例如 qPilotLine 的 q 由 source q 族生成），
    则公式可能是定义展开；
(b) 具体实例：S1487 的 C3 用 `q := S1487Cand` 构造，且 qParameter b := localLogMagnitude S1487Cand
    （单点 badPlaces=PUnit），再用 `S1487Cand_magnitude` 计算；但当前 C3 构造不接 S1487Cand；
(c) 新的 geometric identification（Step (xi-d)/q-pilot 线丛）——超出本 lane。
```

## 5. Lean 状态与建议

```
✓ S1026SourceQIdentificationActual（olean=True）已提供：
   s1026SourceQIdentification_iff_formula（rfl 等价，green）；
   s1026SourceQIdentification_of_formula（条件，green）；
   S1026SourceQExactMinimum（精确最小输入）。
⇒ **不需要新 Lean 文件**（重复定义无益；lead 的 A1112 也要求不建重复文件）。

建议：
1. S1012FinalExactChecklist 的 `sourceQ : Prop` 实例化为 `S1026SourceQExactFormula`（或保留抽象，
   在后续实例化时用 S1026 的 iff）；
2. 在 checklist 文档/状态中把 `sourceQ` 标为 **GAP-SOURCEQ**（不是可证项）；
3. 若要证具体实例：优先尝试 S1487FaithfulSourceData + 以 `S1487Cand` 构造的 C3，
   使公式变为 `|log ‖S1487Cand.q‖| = log ‖C3.q.q‖`（单点、可计算）；
   若 C3.q.q = S1487Cand.q（定义选择），则公式可能 rfl/由 `S1487Cand_magnitude` 得。
```

## 6. 结论

1. `sourceQ` 的精确内容是 `S1026SourceQExactFormula`（⇔ `S1009SourceQIdentification`），
   由 S1026 以 rfl 证明等价；
2. **不可展开/定义相等直接证明**：`qParameter` 是 SourceDefinition31Data 的任意 Real 字段，
   `C3.q` 由 donor/qPilotLine 构造，二者无连接定理；
3. 精确 GAP-SOURCEQ 已记录；S1026 的条件定理可直接用于 checklist 的实例化；
4. 若要推进：构造 C3 使 `q` 来自同一 source q 族（方案 (a)(b)），或接受 GAP；
5. 不新建重复 Lean 文件；建议 checklist 中 `sourceQ` 保留为抽象 Prop 并标注 GAP。