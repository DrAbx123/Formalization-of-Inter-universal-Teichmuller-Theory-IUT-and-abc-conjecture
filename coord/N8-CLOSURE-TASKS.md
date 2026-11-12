# N8 closure task board (2026-10-23)

目标：N8 有 sorry 的 statement/dependency closure。C10 实际消费 C1–C9；C0 base 由 C0 named-sorry 供应；不新增自由结论。

## T1 — Label 统一桥（qside）
文件：tmp/sheaf/n8/closure/LabelBridge.lean
- C0 N8TargetInput 的 Label 是 [AddGroup]；C4/C5 的 Label 是 [Group]。
- 定义 Multiplicative LAdd 与 C0 additive label 的显式 equiv/transport；C0 realization 用 additive label，C4/C5 用 group label。
- 只允许 theorem-level named sorry；exit0。

## T2 — C5 actual permitted family（iplsheapt）
文件：tmp/sheaf/n8/closure/SourceAlgorithmCompatibility.lean
- 给 SourceAlgorithmCompatibilityData 加实际 permitted/pilotLabel/nonempty/mem 字段。
- sourceAlgorithmCompatibility_nonempty 仍只一个 named sorry；exit0。

## T3 — C6 actual product bridge（volumedet）
文件：tmp/sheaf/n8/closure/PaperNormalizedVolume.lean 或新 C6ProductBridge.lean
- 把 C7 用的 C6ProductVolumeData 从 handoff 改为由 C6 PaperNormalizedVolumeData 派生/桥接。
- 不重证 Group6Normalization；exit0。

## T4 — C7 actual C5/C6（kummer）
文件：tmp/sheaf/n8/closure/SourceHolomorphicHull.lean
- 删除本地 C5PermittedFamilyData/C6ProductVolumeData handoff；
- import 实际 C5（T2）和 C6 bridge（T3）；
- sourceHolomorphicHullData_nonempty 保留一个 named sorry；exit0。

## T5 — C8/C9 adapt（transport / logdescent）
- C8 SourceDegreeComparison.lean 改用 T4 的 C7 类型/C6 bridge；一个 named sorry；exit0。
- C9 SourcePilotApproximation.lean 改用 T4/C8 实际类型；一个 named sorry；exit0。

## T6 — C10 full closure（primespine）
文件：tmp/sheaf/n8/closure/N8Closure.lean
- N8FullOutput 字段：C1–C5 actual、C6、C6Prod、C7、C8、C9、C0 base + label bridge；
- n8Assembly_closure 接收 C1–C9，实际构造 full output；
- 只有 C0 base 调 C0 named sorry；不得 total-goal sorry；exit0。

## 依赖
T1 -> T6
T2/T3 -> T4 -> T5 -> T6

## 验收
每文件 lake env lean -R D:/lean exit0；报告 exact types、named sorry、first blocker；不写空结构/True/自由结论。
## 2026-10-23 label 更正

T1 改为 LabelData/ProcessionLabelData（有限集合 + Equiv.Perm），不是 AddGroup↔Group bridge；C0 的 AddGroup 仅是 production index。T2/T4/T6 的 label 字段均按此更正。

## 2026-10-23 actual IQ correction

T8 IQCarrier.lean — qside: actual `SourceLogShellActualIQTensor` carrier, no product-of-fields.
T9a C4 IQ — multiradial.
T9b C6 IQ/log-volume — volumedet.
T9c C7 IQ hull — kummer.
T10 C5 actual IPL family — iplsheapt.
T9d C8 IQ mu_log — transport.
T9e C9 IQ Values — logdescent.
T6 C10 actual IQ assembly — primespine after T8-T10.
