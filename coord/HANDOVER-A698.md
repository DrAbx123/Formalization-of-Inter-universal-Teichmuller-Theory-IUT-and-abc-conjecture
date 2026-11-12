# 交接文档 — IUT 3.12 前置构造 + ABC 条件归约（A698 / 2026-11-11）

## 0. 一句话现状
IUT 3.12 的全部前置对象与推导已在 Lean 4（Mathlib pin v4.32.2）中构造并 kernel 验证，
仅用三公理 [propext, Classical.choice, Quot.sound]，无 sorry / 无自定义 axiom / 无 toy 载体。
ABC 猜想未证明；已机器化到只剩一条显式算术假设 NatRadicalWeightBound：

    NatRadicalWeightBound:
      ∀ ε>0, ∃ D, ∀ ABC 三元组 (a,b,c),
        Σ_{p ∈ bad 集} v_p(a+b+c+1) · d_p · log p  ≤  (1+ε)·log rad(a·b·c) + D

其中 bad 集来自固定 Initial Θ-data T，d_p = finrank_{Q_p}(L_p)（局部扩张次数）。
关键诚实边界：该假设在 d_p=1 情形与 ABC 的 radical 形式等价（ObjectTightnessD1，收尾中），
即这不是被弱化过的 toy 假设，而是 ABC 强度本身。反向（ABC ⇒ 假设）在一般 d_p>1 时不成立
（系数障碍，见 §4）。ABC gate NOT passed，不声称无条件证明。

## 1. 代码位置与环境
- 仓库根：D:\lean；代码主要在 tmp/sheaf/xif/paper/（Mzk1* 前缀）+ LeanFormal/IUT/。
- 编译：watchdog tools/dag_watchdog2.mjs（计划任务 DshDagWatchdog），每文件 log 在
  dag/watchdog/logs/（append-only，需看最后一次 run 的 gate 行）。
- Mathlib 布局坑（已踩过）：
  * 本版本没有 Mathlib.MeasureTheory.Measure.Product.Basic；Measure.pi 在
    Mathlib.MeasureTheory.Constructions.Pi（Measure.pi_pi / Measure.pi_singleton 在此）。
  * NoAtoms 已 deprecated，用 MeasureTheory.NullSingletonClass + measure_singleton。
  * nativePlaceSelection 有根命名空间与 N8Closure abbrev 两个版本，同时 open 会 Fintype
    合成失败并出现假性 sorryAx；用完全限定名或只 open 一个。
  * qVFamTensorP T b 不同 bad places 可共享同一有理素数，不能假设两两互素；corrected
    badPart 用 image 去重后的 distinct primes（Mzk1BadPartActual）。
- 环境性故障：Mathlib .olean.private 偶发读失败、大文件 OOM（拆小、降 heartbeats、
  单文件 lake env lean 先独立确认；坏缓存可换名重写）。

## 2. 已完成的链（35/35 关键 olean 绿；gate 全 trio）
### 2.1 IUT III / Cor 3.12（requirement 级）
KummerTransport → KummerRealization → XiEContainmentRequirement → Haar 严格性
（HaarScalingOneDim + HaarStrictScalingProduct + HaarStrictChainSummary：strict_measure 是定理）
→ Cor312RequirementResolved（paper 不等式、C_Θ ≥ −1）
→ HqnegHullModel + Cor312HqnegDischarged（hqneg 在具体 q-pilot 侧模型消解）
→ Cor312FinalAssembly → Cor312AcceptanceFinal → FinalConditionalCertificate。

### 2.2 比较区域必要性（机器化审计）
PaperComparisonRegionScaling（tripleScale、两 ε-形式 gap、abc_of_tripleComparison）
S1902BridgeInterface（具体载体桥）
A618ScalingObstruction（固定 scaleShift 不可能）
GapStructuralConsequences（Gap1 ⇒ 区域体积无界；有限 hull 内 ⇒ 不可能）
PaperRegionNecessityFinal（最终合取审计，4 clean gates）。

### 2.3 方向修正 / 逆缩放（本阶段关键）
p-adic 乘法收缩 product Haar log-volume；paper 的 λ-multiple 用逆幂因此增大它。
canonical tripleScale（乘 N）方向相反 → corrected 逆缩放模型：
ProductHaarSingleton（单点零测 B1）、ScalingDirection（逆素幂测度/对数律）、
BadPart（distinct prime 修正）、CarrierBadInvScaleLaw/Product（乘积 Haar 律）、
CorrectedLogLawB2（归一化拆分）、B3（log 乘积算术）、CorrectedRegionLogLawProved。

### 2.4 Gap1（IUT IV Thm 1.10 高度估计）——已定理化
CorrectedRegionGap1（条件版，算术核 log c ≤ Σ e_b d_b log p_b 已证）
→ CorrectedGap1Unconditional：Gap1 = 定理（显式 full support / d_b≥1 / unit≥0；三 gate trio）。

### 2.5 Gap2 与最终归约
CorrectedGap2ToABC：Gap2 形状 ⇒ ABCConjecture = 定理（trio）。
Gap2ArithmeticReduction：correctedGap2_iff_arith（Gap2 ⇔ 纯算术 BadSumWeightBound，几何消除）；
  logN_le_log_c_add_log3；correctedGap2_reduces_to_radical。
Gap2ArithmeticTightness：单向紧性（BadSumWeightBound ⇒ ABC；反向不证）。
BadSumWeightBoundExplicit：FinalNamedInput = BadSumWeightBoundNat（natRadical 显式）。

### 2.6 最终交付
FinalBoundaryCertificateV2Actual：finalBoundaryCertificateV2（7 行三态 scope，gate trio）。
FinalConditionalABCActual：final_conditional_ABC : NatRadicalWeightBound → ABCConjecture（trio）
   + final_theorem_package : (final_3_12) ∧ (NatRadicalWeightBound → ABC) ∧ scope。
辅助：GapTightness（抽象紧性 Nonempty bridge ↔ ABC）、LanaBridgeAudit。

## 3. 唯一剩余 named 假设
NatRadicalWeightBound（= FinalNamedInput = BadSumWeightBoundNat）：
for all ε>0, ∃D, ∀ABC triples, Σ_b e_b·d_b·log p_b ≤ (1+ε)·log(natRadical(a*b*c)) + D
机器等价：NatRadicalWeightBound ↔ BadSumWeightBound ↔ CorrectedGap2Shape（三者等价已证）。

## 4. 当前困难与定量消除评估
### 4.1 为什么本模型内没有定量消除路线
- 设 D0 = Σ_b d_b（有限常数）。每 b：e_b·log p_b ≤ log N ≤ log(3c) = log c + O(1)，
  故 badSum ≤ D0·log c + O(1)。
- 若 d_b=1 且全支撑：Σ e_b d_b log p_b = log N 精确（stage4 badSum_eq_logN 已证）。
  于是假设 ⇔ log N ≤ (1+ε)log rad + D；N=2c+1，log N = log c + O(1)，
  即假设 ⇔ ABC radical 不等式（ObjectTightnessD1 正在收尾确认）。
- 若 d_b>1：badSum 系数为 Σd_b 而非 1；反向（ABC ⇒ 假设）不成立
  （A692 反论：D0(1+ε') 的 w 系数无法吸收进 1+ε）。此时假设严格强于 ABC。
- 结论：不存在调常数/调 d_b/换 unit 体积就能消掉假设的路线；等价改写都回到 ABC 本身
  （d_b=1）或更强命题（d_b>1）。要消假设只能真正证明 ABC 强度 radical 不等式，
  或从 paper q-pilot 数据推出坏支撑的真实算术结构（本仓 T 为固定抽象数据，不含该结构）。
### 4.2 可能的真正突破口（需新数学/新数据，不是调参）
(1) 用 paper 的 q-pilot 作缩放元素（bad-supported，|log q| ~ height），把假设化为 q 的显式
    算术界；但仍等价 ABC——需 IUT III/IV 关于 q-pilot 的真实不等式（lana 有推导但依赖未证
    Cor 3.12 variant，且 toolchain/pin 不兼容不可移植）。
(2) 直接证明 radical 坏和不等式：本质是 ABC 的定量形式（log c vs log rad 比较），未解决数学。
(3) 若允许改我们的答案而非题目：把 T 从固定抽象 Θ-data 改为随三元组构造的 Θ-data
    （paper 中 Θ-data 确实随 abc 变），使 bad 集覆盖 rad(abc)；假设变成 log N ≤ (1+ε)log rad+D
    的纯算术形式——仍等价 ABC。对象级改造不消除难度，只是更忠实 paper。
### 4.3 工程建议
- 短期：保持当前边界（最紧可陈述形式）；完成 ObjectTightnessD1 双向校准并把
  「唯一假设 ≡ ABC」写进最终报告；停止调参式消假设尝试（已证无效）。
- 中期：如继续攻 ABC，需真正证明 radical 坏和不等式或引入 q-pilot 真实算术估计（新数学）。
- 长期：保留该假设作为显式 named 输入 + d_b=1 情形校准，使条件定理与 ABC 等价闭合。

## 5. 证据位置
- AUDIT_LEDGER.md：A546…A697（80 条），含根因、修法、gate 原文、诚实边界、lane 分工。
- coord/FINAL-REPORT-A695.md（最终报告）、FINAL-REPORT-A692.md、coord/STATE.md。
- dag/watchdog/logs/*.log：每文件编译输出 + #print axioms。

## 6. Lane 现状
- mainline：最终交付链 15/15 settled；ObjectTightnessCalibration 绿、D1 待修（line 99 补
  abcRationalPoint_logHeight₁，见 A698 消息）。
- hull：30 文件 fresh/red 全清（B1/inverse scaling/badPart/语义审计均绿），lane 已收口。
- qpilot/shehdd/lattice/abc/stage4/stepxi：核心交付全绿；少量旧日志/环境时序类 red（非阻塞）。
- 单 owner 纪律（A570/A687）：不得编辑他人独占文件。

## 7. 下一步（按优先级）
1. 完成 ObjectTightnessD1Actual 双向校准（mainline），使「唯一假设在 d_b=1 情形 ⇔ ABC」入链。
2. 收尾最后 cosmetic red / watchdog 记录（不新增对象）。
3. 更新最终报告/STATE 到 A698+，保留三态语义。
4. 若继续攻数学：按 §4.2 立项，需新 paper 数据/估计，不是现有对象调参。

---

## 附录 A700（2026-11-11 18:20 更新）

### 新增终局结果（单文件 lake env lean EXIT=0，gate 全 trio；watchdog 已按用户要求关闭）
1. `Mzk1ObjectTightnessD1Actual`：**d_b=1 模型下唯一 named 输入恰等价 ABC**
   - `badSum_eq_logN`（d_b=1 + full support ⇒ Σ e d log p = log N）
   - `abc_implies_natRadicalWeightBound`（ABC 高度界 + log N ≤ log c + log3 ⇒ 假设）
   - `natRadicalWeightBound_iff_ABC` ⇒ **假设 ≡ ABC**（对象级精确校准，最紧边界）
2. `Mzk1ObjectTightnessCalibrationActual`：`namedInput_implies_bridge`/`bridge_implies_ABC`/`bridge_iff_ABC`（trio）
3. `Mzk1QPilotRouteActual`（paper q-pilot 路线，第二忠实模型）：
   - `QPilotScaleData`（s = q-pilot signed size；0≤s；height≤s；regionLogVolume = unit+s）
   - `gap1_of_qPilotRoute`（真证：q-pilot 路线 ⇒ Gap1）
   - `qPilotRadicalBound`（剩余 named 估计：s ≤ (1+ε)weight + D0）；`qPilotRadicalBound_implies_ABC`（真证）
   - scope：与 N-scaling 路线同为 ABC 强度，仅使边界更忠实 paper q-pilot 形状

### q-pilot 接口缺口（abc 只读核查）
- S3137 q-pilot readings 需要 `PaperQPilotObjectActual (I := I)`；仓内**无**从 `SourceNativeInitialThetaData T` 构造该对象的 green 定理。
- 从 T 出发的 green 链只到 Kummer/S1902 侧（`qPilotInThetaCarrier`），不连到 `qPilotLogVolumeReading`。
- 若要真正走 paper q-pilot 真实估计，需补接口：T→OriginalInput 数据桥、q = ∏p_b^{e_b} 构造、|log q| ≥ height。

### 环境变更（用户指令）
- watchdog 计划任务 `DshDagWatchdog` 已 **Disabled**，当前无 lean/node 编译进程；
- `tools/run_dag_watchdog.cmd` 的 `DAG_MAX` 已由 12 改为 **5**（下次重启时最多 5 并发）；
- 恢复方式：`schtasks /Change /TN DshDagWatchdog /ENABLE` + `schtasks /Run /TN DshDagWatchdog`。


---

## 附录 A702（2026-11-11 18:22）：论文原样 3.12 的缺口清单与桥接计划

### 已完成的（requirement 合约口径）
- `final_3_12` 定理（trio）：resolved requirement + hqneg/IPL/SHE/APT 证据 ⇒ `Cor312Conclusion`；
- `strict_measure` 定理化；SHE genuine log-volume 不等式、target_matches_paper 等审计定理；
- 全链无 sorry/自定义 axiom。

### 尚未完成（论文原样、无条件）
1. **hqneg 一般情形**：当前 `final_3_12` 接受 `hqneg : requirementSignedQ (rpRequirement T) < 0` 假设；
   仅在具体 q-pilot 侧模型给出 `cor312_hqneg_discharged (hq : qRead < 0)` 的消解证据。
2. **q-pilot 读法三桥**（abc 已定位 green 构造器 `paperQPilotObjectSourceActual` @
   PaperQPilotObjectSourceActual.lean:61，4 输入）：
   (a) T → OriginalInput 数据桥（boundary / oneColumn / lineBundle / logKummer 四输入）；
   (b) q-pilot 构造实例（q = ∏ p_b^{e_b} 的 `sourceQPilotStrip` 语义）；
   (c) |log q| ≥ height（q-side Gap1 的剩余 named）。
3. **IPL/SHE/APT 证据**：目前作为 Prop 参数传入，尚未从初始 Θ-data 构造。

### 桥接计划（按可行性排序）
- B1（abc）：用 `paperQPilotObjectSourceActual` 写**参数化桥**：把四输入作为显式数据结构字段，
  证明 `qPilotLogVolumeReading (qPilotObjectOfData) = sourceQPilotSignedLog I.initial`，
  再与 S3137 的 `qPilotLogVolumeReading` 接口对接（参数化、不假装构造）。
- B2（mainline）：写出 paper-faithful 条件定理形状（`ReadoutData` 三字段 ⇒ `qPilotRadicalBound` ⇒ ABC），
  使「论文原样 3.12 → ABC」的剩余内容精确化为这三个字段。
- B3（后续）：T→OriginalInput 的具体构造（需要 paper IUT III 初始数据构造，难度高，非本轮）。

### 重要提醒
即便论文原样 3.12 完成，也不会自动证 ABC：ABC 路线的唯一剩余假设 `NatRadicalWeightBound`
在 d_b=1 模型下已机器证明与 ABC 等价（`Mzk1ObjectTightnessD1Actual`，trio）。


---

## 附录 A705（2026-11-11 18:31）：空真已机器证明并撤回——当前主路线

### 已机器证明（单文件 lake env lean EXIT=0，gate 全 trio）
`Mzk1FinalConditionalVacuityActual`：
- `hfull_unsatisfiable`：对任意 eN，`hfull` 不可满足（取素数 P>max(bad)、P=2k+1，则 IsABCTriple 1 (k-1) k 且 N=P；
  若某 e_b≠0 则 bad 素数 p_b | P ⇒ p_b=P 但 p_b≤B<P 矛盾；全 0 则乘积=1≠P）；
- `final_conditional_ABC_retracted`：**旧终局条件定理正式 RETRACTED / VACUOUS**（trio）；
- 因此 `final_conditional_ABC`、`final_theorem_package`、`natRadicalWeightBound_iff_ABC` 不再作为结论引用。

### 撤回原因（用户审读 + 机器确认）
1. `hfull` 对固定 T 不可满足 ⇒ 终局条件定理与 d_b=1 等价校准**空真**；
2. `N = a+b+c+1` 缩放非论文结构（paper 坏素数 = abc 素因子；权重按 [F_v:Q_p]/[F:Q] 归一）；
3. 3.12 链未承重（C_Θ ≥ −1 只由包含单调性得到，thetaReading 无上界，与 ABC 无线）。

### 新主路线（N1–N5）
- **N1**（已落地部分）：triple-dependent Θ-data，`q=(abc)²`、坏素数=primes(abc)；
  `log q = 2log(abc)`、(1/6)log q=(1/3)log(abc)；
  有界域：`c≤K·ab` ⇒ `log c ≤ ½log(abc)+½log K`；`c²≤K·ab` ⇒ `log c ≤ ⅓log(abc)+⅓log K`；
  `log f = log rad(abc)`；一般小 ab 情形归 N5。
- **权重归一化**（hull 绿）：`Σ_{v|p}(d_v/D)(v_p·log p)=v_p·log p`（旧 d_b 系数障碍消失）。
- **N2**（进行中）：具体 H（thetaPilotHull）的壳体积上界 (U)，IUT IV Prop 1.2–1.4 的局部格计算；
  常数先作显式参数，未证部分列 named。
- **N3（唯一真难点）**：共享解析容器上的 Cor 3.12 全局下界 (L)；判定实验：最小局部模型（K=ℚ_p、小 l）
  构造共享容器 → 路线活；证 no-go → 与 Scholze–Stix j² 同形（对应 A618ScalingObstruction）。
- **N4**：合并 (U)+(L) ⇒ Szpiro 型不等式；取 l≈√height 得 1+ε。
- **N5**：GenEll/非临界 Belyi 去有界性（我们 [Mzk1] Thm 2.5 线的真实消费者）。

### 当前禁止事项
- 不得引用 `final_conditional_ABC`/`final_theorem_package`/`natRadicalWeightBound_iff_ABC` 作为结论；
- 不得使用 hfull 或 N=a+b+c+1 缩放作为论文结构；
- 新工作一律 triple-dependent Θ-data + 归一化权重。


### A705 补充：撤回范围扩大（stage4 机器结果，2026-11-11 18:35）
- `Mzk1Stage4A703CorrectionActual.hfull_unsatisfiable` 另用两个三元组 (1,2,3)/(2,3,5)：hfull 同时强制 7 = ∏… = 11，矛盾（omega）；
- **`corrected_gap1_hypotheses_inconsistent`：`corrected_gap1_of_fullSupport` 的假设包不一致 ⇒ corrected Gap1 条件定理也空真**；
  因此依赖 hfull 的链（CorrectedGap1Unconditional、CorrectedGap2ToABC 的 N-缩放版本等）全部 RETRACTED；
- stage4 `Mzk1RetiredBoundaryAuditActual`：6 行 retired + 4 行 newRoute（N1）；
- shehdd 四个 Sha 表已标 RETRACTED + N1 行（`Mzk1FinalSemanticsShaActual`/`FinalBoundaryCertificateV2ShaActual`/`OneWayTightnessShaActual`/`B1B2StatusShaActual`），并新增 `Mzk1N1TripleThetaDataRouteShaActual`（audit only）；
- 剩余：canonical `Mzk1FinalConditionalABCActual`/`FinalBoundaryCertificateV2Actual` 文件头 RETRACTED 标注由 mainline 完成（A706）。

