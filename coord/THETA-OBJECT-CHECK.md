# A497: Θ-pilot 对象核对（paper Cor 3.12 Θ-pilot vs 我们的 θ 读法）

来源: IUT III Def 3.8(i) L6617-6655；Cor 3.12 L10324-10338；III L552-567（l⋇/l±）；III L598-609（theta values q^{j²}）；III L10215（2ℓ-th roots）；IV L1258-1363（|log q|=(1/2ℓ)log q）。配套: coord/COR312-STATEMENT-AUDIT.md（stepxi）、coord/FOUR-TRIANGLE-OBJECT-LIST.md §5/§7。只读。

## 结论（立即执行）
- `Mzk1QPilotR4Stage5AlignActual.thetaPilotLogImage := qPilotLogImage/(2l.value)` 是 **q 除以 2ℓ**，不是 paper Θ-pilot；`qThetaReadout_ordered (q<theta)` 只是负数除法恒等式；`qThetaStepXIContract.targetSigned := thetaSigned`、`target_le_theta := rfl`；因此 step3115_comparison_proved 与基于它的 Cor312Conclusion **VOID**，不得作为 3.12 证据。
- `StepXIContract/Cor312Conclusion` 本身过弱：targetSigned 是 paper 没有的中间量（可取 target=theta 使 target_le_theta=rfl）；至少应去掉 target 或要求其独立于 theta。
- 真内容在 `Cor312ToABCBridgeInterface.Cor312EpsilonArithmeticComparison` 的两条 IUT IV 比较（height_le_normalizedRegionVolume、regionVolume_le_normalizedWeight）——named 真缺口，不能再用 q≤target 充数。

## Θ-pilot 对象逐项核对

| paper Θ-pilot 组成 | paper 锚点 | 我们现有 | 缺口 |
|---|---|---|---|
| Θ-pilot object = ∏_{j∈F_l^⋇}(†F^⊛_MOD)_j realification，由 v∈V_bad 的 Ψ⊥ generator 决定 | III Def 3.8(i) L6617-6655 | 无 product/Frobenioid 对象 | 需构造（OBJECTS 1-3） |
| theta values {q_v^{j²}}_{j=1..l⋇}，l⋇=(l−1)/2 | III L598-609、L552-567；IV L4417-4421 | S310CompletionSameCarrierPairActual.thetaCompletionImagePoint（root^{gaussExponent j}）; PaperRootCompletionTensorActual.sourceRoot（AlgClosure 中 2ℓ root） | 无 F_l^⋇ 全体/Ind 轨道、无 product 结构 |
| 2ℓ-th roots / Kummer indeterminacy（theta values up to 2ℓ roots；q_v 是 q 的 2ℓ root） | III L10215；IV L1358-1363 | sourceRoot（AlgClosure 中 root）；S342 证明 completion 内不存在 2ℓ root | 需 Kummer 扩张对象、up-to-roots 不变性、q_v 与 q 关系 |
| -|log Θ| = 对 j∈F_l^⋇ 平均的 procession-normalized log-volume of holomorphic hull of union of possible images under Ind1/2/3 | III Cor 3.12 L10324-10338 | 无（GlobalThetaPilotLogVolume 只是值层候选且归一化不对；GlobalPositive 用 value-model；S3137/AbsTopIII09 是单 λ-O tensor 区域 Haar） | hull/union/procession average/Ind 全部缺 |
| -|log Θ| ∈ R（finiteness）与 -|log Θ| ≥ -|log q|（C_Θ ≥ -1） | III L10349-10353 | 无 paper 形式；qTheta 链 VOID | 需真实 Θ-pilot log-volume 与 finiteness |

## 缺失构造（对象优先）
1) BPS/0-column/etHT/Hodge theater/log-shell/tensor packets（OBJECTS 1-6）；2) theta values 全体 j∈F_l^⋇ 与 2ℓ root 的 Kummer 扩张；3) Ind1/2/3 possible images 的 union；4) holomorphic hull（packet-wise/λ-O/archimedean）；5) procession-normalized log-volume（j∈F_l^⋇ 平均，含 sFactor=(l⋇+1)(2l⋇+1)/6，IV L1746-1753）；6) q-pilot object 与 |log q|=(1/2ℓ)log(q)（IV L1358-1363，含 [F:Q] 权重）。

已有可复用（对象候选，不接线）: literal IQ carrier+product Haar（A481/A483b: S1929/PaperIQCarrier/IQCarrierFromSource/S2723/S3129）、SourceHullCompactnessReduction/IQCarrierHaarData/IQCarrierConcreteModel（hull/log-volume 候选）；S310/PaperRootCompletionTensor（theta values/root 候选）。

本记录只读；未改文件/队列/watchdog。