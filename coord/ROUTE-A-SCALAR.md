# ROUTE-A-SCALAR — 标量 q-pilot 体积恒等式 (A1065)

| field | value |
|---|---|
| Status | PARTIAL (标量核心真证；几何识别三条 GAP) |
| Lean | `tmp/sheaf/xif/paper/Mzk1QPilotVolumeScalarActual.lean`（未编译；无 sorry/axiom） |

## 1. 定义盘点

- `sourceQPilotSignedLog S := -sourceBadQAbsLog S`（PaperQPilotObject:73），
  `sourceBadQAbsLog S := Σ b : S.badPlaces, |Real.log (S.reduction.qParameter b)|`；
- `S2717QPilotLogVolume … := sourceQPilotSignedLog (S2711I …).initial`（`S2717Cor312FullTargetActual:69-76`）
  —— 所以 **S2717 目标是 scalar target 的实例**（S := initial）；
- `localNormOrder p x := -Real.log ‖x‖ / Real.log p`（FinitePlaceFractionalAbsorption:114）；
- `S3050Unit p jValue l := -(((-localNormOrder p jValue)/(2*l:Nat)))*log p`（S3050:18-20）；
- `localQrootLogVolume T b := Real.log (rootNormedElementNorm T b)`（HullDet:78-82），
  `rootNormedLogVolume := Real.log ‖rootNormedUnit‖`（PaperRootCompletionTensor:126-127）；
- `paperQAbsLog l logQ := qNormFactor l * logQ`（S2691:55）；
- `S3016StepVQPilot a b c := S2736QPilotLineBundleLogVolume (S2752J …)`（S3016:30-32），
  `S3016IdentificationTarget : S3016StepVQPilot = S3016WeightedGlobalQPilot`（Prop，GAP）。

## 2. Lean 目标（已落盘）

```lean
def QPilotVolumeScalarTarget (S : SourceDefinition31Data l) (A : Real) : Prop :=
  sourceQPilotSignedLog S = -A
theorem sourceQPilotSignedLog_eq_neg_badQ : sourceQPilotSignedLog S = -OrigXiFPaperBadQAbsLog S
theorem qPilotVolumeScalarTarget_iff_badQ : QPilotVolumeScalarTarget S A ↔ OrigXiFPaperBadQAbsLog S = A
theorem qPilotVolumeScalarTarget_of_badQ (hA : badQ = A) : QPilotVolumeScalarTarget S A
theorem S3050Unit_eq_log_norm_div : S3050Unit p x l = - Real.log ‖x‖ / (2*(l:Real))
```

## 3. 已能证多少

- **真证**：badQ 归约（`sourceQPilotSignedLog = -badQ`，port green `OrigXiF:114-117`）；
- **真证**：`S3050Unit = -log‖x‖/(2l)`（A1070 符号修正；标量代数，用 `localNormOrder` 定义 + log p ≠ 0）；
- **真证**：`S2717QPilotLogVolume = sourceQPilotSignedLog initial` 是 rfl（定义层，不需额外定理）。

## 4. 剩余 GAP（精确）

1. **GAP-SOURCE-ROOT**：`sourceBadQAbsLog` 用的是 source data 的 `qParameter b`，
   而 `localQrootLogVolume`/`rootNormedLogVolume` 用的是 **2l-th root** `rootNormedElement`；
   二者之间需要 `Real.log |qParameter b| = 2l * Real.log ‖rootNormedElement b‖`（或带符号）
   的识别——在 S1487/OrigXiF 栈中未找到直接定理；
2. **GAP-S2691**：`paperQAbsLog l logQ = qNormFactor l * logQ`，而我们的 `A = logQ/(2l)`；
   需 `qNormFactor l = 1/(2l)`（或等价）——未证；
3. **GAP-S3016**：`S3016IdentificationTarget a b c` 是 Prop（StepV q-pilot = weighted global），
   这是 Step (v) 的识别 GAP，不能作为证明；
4. 若取 `A := OrigXiFPaperBadQAbsLog initial`，则 target **成立**（`qPilotVolumeScalarTarget_of_badQ` rfl 分支），
   但这只是把 A 定义成 source badQ 和，不是 paper 的 `|log q|`；
   要得到 `A = paperQAbsLog`/`|log q|` 仍需 GAP-SOURCE-ROOT + GAP-S2691。

## 5. 结论

1. Route A 标量核心（badQ 归约 + S3050Unit 标量恒等式）**真证**；
2. `S2717QPilotLogVolume = -A` 的 paper 归一化版本**尚不可证**，缺 GAP-SOURCE-ROOT 与 GAP-S2691；
3. 若允许 `A := OrigXiFPaperBadQAbsLog initial`（source 和），target 立即成立（但这不是 paper 的 |log q|）；
4. 下一步：找/证 `Real.log |qParameter b| = ± 2l * Real.log ‖rootNormedElement b‖` 与 `qNormFactor = 1/(2l)`。