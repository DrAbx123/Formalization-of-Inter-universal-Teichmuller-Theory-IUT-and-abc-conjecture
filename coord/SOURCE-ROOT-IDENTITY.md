# SOURCE-ROOT-IDENTITY — Route A 缺口定理 (A1072)

| field | value |
|---|---|
| Status | PARTIAL (等价性真证；多 place 体积 = -paperQAbsLog 仍是 GAP) |
| Lean | `tmp/sheaf/xif/paper/Mzk1SourceRootIdentityActual.lean`（未编译；无 sorry/axiom） |

## 1. 定义（精确）

- `OrigXiFPaperBadQAbsLog S = ∑ b : S.badPlaces, |Real.log (S.reduction.qParameter b)|`
  （OrigXiFPaperQPilotObjectActual:97-100；`= sourceBadQAbsLog S` rfl，:103-105）；
- `paperQAbsLog l logQ = qNormFactor l * logQ`，`qNormFactor l = 1/(2*l.value)`（S2691:51/55）；
  ⇒ **`paperQAbsLog l logQ = logQ/(2ℓ)`**（本文件 `paperQAbsLog_eq_logQ_div` 真证）；
- `paperQPilotLogVolume_multi D = - sourceBadQAbsLog I.initial`
  （`paperQPilotLogVolume_multi_eq_neg_sourceBadQAbsLog`，S2708/S2711HcompMulti:32）；
- `paperQPilotLogVolume_multi D = sourceQPilotSignedLog I.initial`（另一方向，S2714 文档引用）。

## 2. 目标定理

```lean
def SourceRootIdentity (I) (logQ : Real) : Prop :=
  OrigXiFPaperBadQAbsLog I.initial = paperQAbsLog l logQ
theorem sourceRootIdentity_iff_multi (D : MultiPlaceQPilotDonor I) (logQ) :
  SourceRootIdentity I logQ ↔ paperQPilotLogVolume_multi D = -paperQAbsLog l logQ
theorem sourceRootIdentity_of_multiVolume (h : paperQPilotLogVolume_multi D = -paperQAbsLog l logQ) :
  SourceRootIdentity I logQ
```
即：**只需证多 place q-pilot 体积 = −paperQAbsLog**，即完成 Route A 标量闭合。

## 3. 为何这是 GAP（精确）

S2708 的文件头（:25-70）已说明：`SourceDefinition31Data` 的
- `badPlaces : Type` 是**抽象类型**；
- `reduction.qParameter : badPlaces → Real` 是 **Real 值**；
- 没有 finite place map、没有 completion element、没有 `FinitePlaceQCandidate`。

因此 `paperQPilotLogVolume_multi D = -paperQAbsLog l logQ` 等价于要求
`Σ_b |log(qFamily b)| = logQ/(2ℓ)`，其中 `logQ = Σ_w weight_w * qOrder_w * log p_w`；
这是 **source Real q-参数族** 与 **paper q-divisor 数据** 的识别（IUT I Example 3.2(iv) 型），
S2708 把它精确记为 `FinitePlaceQPilotDonor` 缺口（需要 `placeOf : badPlaces → FinitePlace Fmod`
与 `localLogMagnitude (qFamily b) = |log (qParameter b)|`）。

## 4. Lean 内容（真证部分）

- `paperQAbsLog_eq_logQ_div`：`paperQAbsLog l logQ = logQ/(2l)`（ring）；
- `multiVolume_eq_neg_badQ`：port（green）；
- `sourceRootIdentity_iff_multi`：等价（`hbad` rfl + `hvol` + linarith）；
- `sourceRootIdentity_of_multiVolume`、`sourceRootIdentity_eq_abs`（条件版）。

## 5. 结论

1. Route A 标量链的**唯一缺口**精确化为：`paperQPilotLogVolume_multi D = -paperQAbsLog l logQ`；
2. 本文件已把 `SourceRootIdentity` 与其等价起来（真证），所以补这条即可闭合；
3. 该等式需要 S2708 所述 `FinitePlaceQPilotDonor`（finite place map + discrete q 实现），
   在 `SourceDefinition31Data` 现有字段下**不可证**（GAP-SOURCE-ROOT，非循环、非目标假设）；
4. 下一步（若 owner 允许扩展 source 数据）：构造 `placeOf` 与 `qFamily`，用
   `ordp_qrootOf`/`localNormOrder` 证明离散 q 条件 `|log q_b| = n_b log p_b`。