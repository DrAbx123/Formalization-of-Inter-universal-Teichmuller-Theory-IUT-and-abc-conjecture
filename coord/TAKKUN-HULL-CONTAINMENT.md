# TAKKUN HULL CONTAINMENT — (xi-d)–(xi-f) 提取与我们的 step3115/hull 读法对照

范围: 只读 tmp/sheaf/takkun/IutLean/ 的既有 Lean 文件（A500 移植）。目的: 提取其
(xi-d)–(xi-f) containment / θ-包体积估计，标示可复用资产与不可作为结论的数据，并与我们
hull/det lane 的读法逐项对照。**本文件不是证据声明**；所有 Takkun 结论仅作待审计数据。

## 1. 读取的文件与关键声明

表（文件 → 关键声明）:

- Multiradial/Cor312.lean:
  PilotVolumeData（Ω、Γ、vol: Ω→ℝ、vol_mono、thetaPilot、qPilot、hull、
  hull_spec: ∀g, g•θP ≤ hull、**containment: ∃ g, qP ≤ g•θP**）；
  cor312: vol qP ≤ vol hull（证明只用 vol_mono + containment + hull_spec）；
  twelve_mul_thetaPilotDegree（12·θ = l⋆·l·(l+1)）。
- Multiradial/Thm311.lean:
  Thm311Transcription：K: LogKummerCorrespondence、volS/volR 单调、
  **theta_vol: volS θP = arithFactor·(−qVol)**（由 theta_vol_derivation 从
  gaussian_total_degree 真正导出）、
  **hull_dominates: K.HullDominates θP hullR**（(Ind3) 合并的像 ≤ hullR）、
  **q_vol: volR (K.kummer 0 θP) = −qVol**、
  **hull_bound: volR hullR ≤ cΘ·qVol（唯一残余义务）**；
  transcription_passes: containment 由 K.base_le_hull W.hull_dominates 在 level 0 得出，
  即 **q 像 ≤ hullR 是机构引理，不是字段**。
- Multiradial/ThetaHullDichotomy.lean:
  ThetaHullTranscription 增加 **Θ-包 pin: volR hullR ≤ volS θP + L**；
  thetaHull_forces_height: (arithFactor−1)·qVol ≤ L；
  no_lossless_theta_hull（L=0 不可满足）；
  thetaHullTranscription_iff（任意 L≥0 存在性 ↔ 高差不等式 ∧ cΘ≥−1）
  ——**该 pin 的成立与结论同值**，不构成独立推导。
- Multiradial/TwoSidedLink.lean:
  分离 Send/Recv；IsRelabeling（Θ-link 保体积）⟹ relabeling_vacuous
  （不等式退化为 volS θP ≤ volS hull）；link_not_isometric（Gauss 因子 >1 时不可能保体积）；
  bounded_distortion_bounds_height；残余 TwoSidedSupply。
- Multiradial/DisputedCore.lean:
  strict_collapse（严格同一化 + Gauss 次数 + q 非平凡 ⟹ False）；
  hull_exceeds_orbit；slack_lower_bound: (factor−1)(−vol qP) ≤ vol hull − vol θP；
  MultiradialSupply（抽象可达）。
- Padic/LogShellRadius.lean:
  半径常数 aRadius p e、bRadius p e；aRadius_tame/bRadius_tame/radius_tame
  （顺分叉 a=1/e=−b）；one_div_le_aRadius、le_aRadius（严格不等号在 (p−1)∣e 时不成立，
  原文修正）、aRadius_lt、neg_one_div_le_bRadius；aRadius_one/bRadius_one。
- Padic/LogVolume.lean:
  logVol x := Real.log ‖x‖；logVol_one: logVol 1 = 0；logVol_p: logVol p = −log p；
  logVol_mul、logVol_pow（θ 值 q^{j²} 的体积）、logVol_logOnePlus；
  logShell_vol_boundary = −aRadius·log p、logShellVolFormula = −(1/e + m/(ef))·log p；
  **实配线 11a3: curve11a3_qShell_logVol: logVol(11·ℤ₁₁) = −logq、
  curve11a3_qShell_logVol_qVol: logVol(11·ℤ₁₁) = −(2·7)·qVol**。

## 2. Takkun 的 (xi-d)–(xi-f) 内容提取

- (xi-d) 行列式/体积归一化: Padic/LogVolume.logVol 给出 μ_log(p·R) = −log p 与
  乘法性/幂律（logVol_pow 正是 q^{j²} 的体积）；logShellVolFormula =
  −(1/e+m/(ef))log p 为非分叉情况的显式公式。Thm311.theta_vol_derivation 用
  gaussian_total_degree + thetaPilotDegree_div_lStar 从 Frobenioid 的 Gaussian 次数
  真正导出 **volS θP = arithFactor·(−qVol)，其中 arithFactor = l(l+1)/12**。
- (xi-e) log-Kummer / (Ind3) containment: hull_dominates 是 log-Kummer 对应结构的一部分
  （(Ind3) 上半兼容的合并），K.base_le_hull 把它降到 level 0；因此
  **q 像 = K.kummer 0 θP ≤ hullR**。这是 Takkun 所谓“已验证 containment”的实际内容：
  它依赖 LogKummerCorrespondence（hull_dominates 字段/引理）与 Θ-link 定义，**不是**
  从 C3/数域数据独立构造的 actual images hull。
- (xi-f) 比较: 由 q_vol 与单调性 volR (kummer 0 θP) ≤ volR hullR 得 −qVol ≤ volR hullR；
  要得到 ... ≤ cΘ·qVol 需要 **hull_bound**（[IUT-IV] Props 1.1–1.9 的 p 进 log-volume 上界）。
  ThetaHullDichotomy 进一步表明：若把上界写成 Θ-包 pin，则 pin 的可行性与高差不等式
  **同值**（thetaHullTranscription_iff），lossless (L=0) 不可行；故 Takkun 自身**没有**
  给出 hull_bound 的独立推导。
- 2ℓ 归一化: curve11a3_qShell_logVol_qVol 明确 logVol(11·ℤ₁₁) = −(2·7)·qVol，
  即原始 p 进体积 −log 11 除以 2l 得到 qVol；theta_vol = arithFactor·(−qVol)。
  arithFactor = l(l+1)/12 = sFactor(l⋆)（LANA 的 sFactor；l⋆=(l−1)/2），
  即 **theta 侧的内容是 qVol 乘 Gauss/sFactor 因子，不是 q/(2ℓ) 本身**。

## 3. 与我们 step3115 / hull 读法的对照

- 局部 q 读法: Takkun Padic.logVol x = Real.log ‖x‖（logVol_p = −log p）与我们
  hullReadoutLocal b = qPilotLogImage T b = localSignedLog (qVFamily T b)
  = Real.log ‖(qVFamily T b).q‖ **逐字一致**（局部 signed log；同为负值）。
- 2ℓ 归一化: Takkun qVol = logq/(2l)，logVol(q-shell) = −(2l)·qVol，
  theta_vol = arithFactor·(−qVol)；我们的旧 VOID 读法
  thetaPilotLogImage = qPilotLogImage/(2l)，我们的 hullReadoutGlobal = −|log q|，
  独立 thetaPilotReadout = Haar log(C3 hull region)。旧 VOID 量在数值上等于 **−qVol**
  （Takkun 的 2ℓ 归一化 q 体积），**不是 θ**；Takkun 真正的 θ 侧是 arithFactor × 它。
  我们缺的是 arithFactor = sFactor(l⋆) 这一 Gauss 增益与真实的 hull。
- hull/containment: Takkun hullR 由 HullDominates 支配 kummer 0 θP（(Ind3)）；我们的 C3
  thetaPilotHull = actualC3LogShellTensorRegion（hull=region），没有 possible-images /
  Ind3 合并的 hullR。Takkun 的 containment 逻辑可复用（base_le_hull 模式），但其 hullR/K
  不是从我们的 C3 Haar 区域构造；我们的 C3 asset 也没有 q 像 ≤ hullR 的真实包含证明。
- hull 体积估计: Takkun hull_bound: volR hullR ≤ cΘ·qVol（[IUT-IV] Props 1.1–1.9）**未证**；
  我们的 thetaPilotReadout 是 C3 tensor log-shell hull 的真实 Haar log；没有 volR hullR
  的 possible-images 版本。这正是我们 hull lane 应构造/估计的对象。
- 结论: Takkun cor312 依赖 containment 字段；transcription_passes 依赖 hull_bound；
  thetaHull_forces_height/thetaHullTranscription_iff 显示 pin 与高差同值；我们的旧
  step3115_comparison_proved 是 VOID（q/(2ℓ) 恒等式）。**不可采纳** Takkun 的
  cor312/transcription_passes/ThetaHullTranscription 作为 3.12 证据；可采纳其 logVol、
  theta_vol_derivation、HullDominates 结构、半径常数与 hull_bound 的残余形式。

### 可复用（对象定义 / 已验证引理）
1. Padic/LogVolume.logVol 及其 logVol_p/logVol_pow/logVol_mul/logVol_logOnePlus
   —— 与我们的局部 q 读法**定义一致**，可直接作为局部 Haar 体积引理使用。
2. Padic/LogShellRadius 的 aRadius/bRadius 与 tame 等式、不等式 —— 真实算术常数。
3. Thm311.theta_vol_derivation（gaussian_total_degree + thetaPilotDegree_div_lStar）
   —— 给出 arithFactor = l(l+1)/12 = sFactor(l⋆) 的 Gaussian 次数，是我们独立 θ 读法
   应匹配的发送侧归一化因子。
4. hull_dominates/base_le_hull 的**逻辑模式**：由 (Ind3) 像的合并得到 q 像 ≤ hullR；
   我们的 C3 侧需要构造对应的 actual possible-images hull 才能使用。
5. Padic/LogVolume 的 11a3 实例: logVol(11·ℤ₁₁) = −(2·7)·qVol，可作为 2ℓ 归一化与
   q 读法一致性的真实测试。

### 只能作待审计数据（不可作为结论）
- PilotVolumeData.containment、cor312、ThetaHullDichotomy 的 Θ-包 pin 与
  thetaHullTranscription_iff（pin ⇔ 高差，循环）、TwoSidedLink.relabeling_vacuous、
  DisputedCore.MultiradialSupply（抽象 witness）、transcription_passes（含 hull_bound 义务）。
- 这些文件里的 vol qP ≤ vol hull 是在抽象 Ω/Takkun T 上成立；其到 actual C3/Haar 载体的
  实例化没有给出，不能直接搬到我们的 step3115/hullReadout。

## 4. 对 hull lane 的下一步（与 A497/A498/A499 一致）
1. 以 Takkun Padic.logVol 为对照，确认我们的 qPilotLogImage = log‖q_V‖（局部）与
   hullReadoutGlobal = −|log q|（C3 全局）的归一化一致；2ℓ 只出现在 qVol 归一化，
   θ 侧必须乘 arithFactor=sFactor(l⋆) 并取真实 hull 体积。
2. 在 actual possible-images hull 上构造 received-normalization 的 thetaPilotReadout
   （ThetaPilotObjectActual.sourceHolomorphicHull + ThetaPilotHullProcessionActual 的
   globalThetaPilotHullProcessionLogVolume 是现有入口），然后试证 Takkun 型 hull_bound:
   thetaPilotReadout ≤ cΘ·|log q|。这对应 TwoSidedSupply 的真实实例。
3. 若 hull_bound 无法从 C3/invariant 数据得到，则精确记录缺失常数
   （arithFactor、aRadius/bRadius、different bound）与缺失对象（possible-images hull 的
   received measure），而不是回退到 q/(2ℓ) 读法。


## 5. qpilot 复用映射交叉引用（A500）

qpilot 已整理 coord/TAKKUN-REUSE-A500.md，与本文档互补：
- RealKummer.realQRootSystem/realThetaRootSystem（2ℓ 根体系，qroot^(2ℓ)=q），
  IUT.Theta.thetaValueMon/gaussExp/thetaValue_neg（Θ 值组合），
  IUT.Padic.logVol_pow（独立 Θ 读法体积 = gaussExp·logVol qroot，**非 q/(2ℓ)**），
  aRadius/bRadius、shell/shell_subset_iff/unit_mul_shell、Ind2/Θ-link 群论。
- 与本文档 §2–§3 一致：Takkun 的 logVol/半径常数/Gaussian 次数是真实可复用资产；
  containment 与 hull_bound 仍是结构/残余义务。O2 的 qroot 建议升级为根体系 2ℓ 层，
  由 O2 owner 按 qpilot 消息推进；hull lane 的独立读法以 S3137/AbsTopIII09 的
  actual C3 Haar 资产为准，不依赖 O2 的 L_b root。
