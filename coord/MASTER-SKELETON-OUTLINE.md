# MASTER-SKELETON-OUTLINE (Lead draft; mainline 补全合并)

Date: 2026-11-11 ~00:15. Purpose: 完整骨架/图像草稿；mainline 主笔的 `MASTER-SKELETON.md` 以此为基础补全节点表。

## 0. 最终目标（唯一 anchor）

- **ABC 陈述**：`LeanFormal/IUT/ABCBridge/Statement.lean:32` `ABCConjecture : Prop`
  - 精确正文：∀ ε>0, ∃ K>0, ∀ a b c, IsABCTriple a b c → ABCInequality ε K a b c
- **目标登记**：`GOAL.md` abc-target；`coord/queue.md`；当前 `locked_targets = []`（最终验收未执行：同版本 build + comparator + 传递公理 + 原文语义审查）

## 1. 最终链（Goal → bottom 的必经 Lean 节点）

| 层 | Lean 节点 | 文件:行 / 声明 | 状态 |
|---|---|---|---|
| G0 | **ABCConjecture** | ABCBridge/Statement.lean:32 | 定义 |
| G1 | `cor312ToABCBridge_abcConjecture (D) : ABCConjecture` | ABCBridge/Bridge/Cor312ToABCBridgeInterface.lean:446 | **条件定理（已证）** |
| G2 | `Cor312ToABCBridgeInterface` | 同文件:404（carrier : Type u; hullData : IQHullLogVolumeInterface carrier; epsilonComparison : ∀ε, Cor312EpsilonArithmeticComparison hullData ε） | **named 输入结构**；`nonempty_iff_abcConjecture`（:605）说明等价于 ABC，不能当廉价义务 |
| G2' | `ABCFrontier` / `ABCFrontierRealLine` | ABCBridge/Bridge/ABCFrontier.lean:213,309,337,354 | 条件等价（`abcConjecture_of_frontier`, `abcFrontier_iff_abcConjecture`） |
| G3 | **Cor 3.12 / 3.11 hull-volume 结论** | IUTIII：Corollary312、Theorem311、SourceHullCompactnessReduction、SourceTheorem311Assembly（见 SKELETON-IUTIII） | 部分真实对象 + 接口；hull/determinant 等 deep 构造 named |
| G4 | **IUT IV 算术过渡 + 估计** | IUTIV：ArithmeticDivisorDegree（94KB）、Section1、Section2、StepV*、ArchimedeanTensorMetric；ABCBridge/Geometry 的 IQHull/Hull 系列 | 大量真实对象；两个 `Cor312EpsilonArithmeticComparison` 字段（height≤region volume、region volume≤weight）仍 named；单一解析终点 `S2717UpperGap`（S2804） |
| G5 | **IUT III theta-hull / StepXI / log-shell** | IUTIII：ThetaPacketBridge、CardAMPLThetaBoundSupply、SourceLogShellMuNQuotientCarrier、Source*StepXI*、Source*SHETransport*、CardHull* | 真实锚点 + 大量接口；H5 O^× / H7-Ob9 / AbsTopIII05 深输入 named |
| G6 | **IUT II EtTh / Frobenioid / log-shell** | IUTII：EtaleThetaQuotient 全套、Example36*（194 文件，Frobenioid/Tate/étale）、SourceLogShellCarrier、SourceLogShellAbsTopIIIBridge；EtTh00-13 | 真对象多；EtTh02 10 deep inputs + EtTh11 rows5-7 named |
| G7 | **IUT I Hodge theater / source** | IUTI：SourceHodgeTheaterFamily(40KB)、SourceClauseConstructors(51KB)、Definition31*、SourceEtaleStack、ConcreteInitialTheta* | 真对象多；source-supplied 部分 named |
| G8 | **基础数学** | LeanFormal/IUT/Foundations（539 files）：Theta analytic（OddTheta* 10 files）、QlTheta*、LocalFields、AlgebraicGeometry；tmp 移植 flt_core RR、TauCeti Belyi/CV | 大部分已证；OddThetaNegativeDecay/TermAlgebra、AbsoluteKummer* 等构建缺口 |

## 2. 已完成的 bottom 层（本 session，全部无 sorry/axioms trio）

| 层 | 对象 | pin |
|---|---|---|
| B1 | Problem A fold：`betaAvoiding_all : ∀ S β:ℚ, β∉S → BetaAvoidingAt S β` | Mzk1BetaAvoidingFoldActual 27144B E07D7038 |
| B2 | finite-β corrected base（原 ∞-β 陈述 refuted） | Mzk1BetaAvoidingBaseActual 10430B 691DFC7F |
| B3 | rational 2.4 target（finite-β 无条件） | Mzk1Rational24TargetBottomActual 5781B A4D82E80 |
| B4 | C degree/measure/termination（28 定理） | Mzk1NestedInductionActual 37958B 76D71E7D |
| B4b | C BaseCaseProvider（identity 构造） | Mzk1NestedInductionBaseCaseActual 4728B 14F5F5A7 |
| B5 | Lemma 2.3 rational / P¹ Möbius | Mzk1Lemma23MoebiusActual 6400B 66D16886 |
| B6 | D-BASE（RR-independent pencil + scheme vacuity 修） | Mzk1GeomCoreFoundationActual 14032B 0F74F433 |
| B6b | D-RR（RR 真证 + hdual discharged，无 named） | Mzk1GeomCoreRRProvedActual 15877B 813224A5 |
| B7 | RR 接口（flt_core） | Mzk1RRInterfaceActual 8895B 7BD88E7D |

## 3. 未闭合/last-mile（按依赖顺序）

1. **C StepProvider'**：几何 f1/f2/f4（stage4）+ `CVCompositionLawF`（abc/stage4）+ fixed-β 额外论证 named → C 组装无条件
2. **D bridge/finite-map 构造层**：scheme↔function-field bridge、finite map to P¹（flt_th / scheme 定义与 flt_core 冲突需独立接口层）
3. **E 构建缺口**：OddThetaNegativeDecay/TermAlgebra、AbsoluteKummer{Continuity,Injection,Quotient}、SourceThetaPilotIQContainment、Section0Objects 修编
4. **E 扩展**（按资产优先）：SourceLogShellDatum→Prop 5.8(ii) diagram、Example36↔EtTh 对应、Prop5.8(i)/Cor5.5 算法（new theory named）
5. **IUT III/IV 高层**：Cor312/3.11 的 hull-volume 真构造；H5 O^× normalization / hull≤image-volume、H7/Ob9 arbitrary iterate、AbsTopIII05 deep anon、EtTh02 10 deep inputs、EtTh11 rows5-7
6. **IUT IV comparison**：`height_le_normalizedRegionVolume`、`regionVolume_le_normalizedWeight`（两个 named 字段）+ S2717UpperGap 解析端点
7. **最终验收**：锁定目标（challenge）→ comparator 接受 → 传递公理检查 → 原文语义审查 → 同版本 build

## 4. 搜索覆盖（需要继续补）

- 已系统看：LeanFormal/IUT/{IUTI 69, IUTII 194, IUTIII 190, IUTIV 14, Foundations 539, ABCBridge 164}，tmp/sheaf/xif/paper 12790，tmp/external/ported 2163
- 已用旧文档：GOAL/SHEAF/SETUP/coord/STATE、dag/README、C3_CONSUMER_CHAIN_CLOSURE、E-EXISTING-CLOSURE-MAP、E-EXTENSION-PLAN、PROBLEM-E-INVENTORY、FOUNDATIONS-IUTIV、FOUNDATION-FIRST-PLAN、IUT_SUBTARGETS、THEOREM311_*、ENDGAME-DEPENDENCY-LEDGER、FINAL-STATUS
- **待补搜**：每个树里未在旧文档出现的"目标相关声明"（grep：Corollary312/Theorem311/SourceTheorem311Assembly/StepXI/hull/Ob9/EtTh/AbsTop/Frobenioid/Hodge/theta-link）；tmp 历史目录中仍有价值的实现；外部 LANA 产物的后续公开文档
