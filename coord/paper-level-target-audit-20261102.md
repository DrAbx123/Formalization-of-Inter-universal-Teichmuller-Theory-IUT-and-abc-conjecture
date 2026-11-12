# Paper-level 3.12 目标审计（2026-11-02）

状态：只读审计。未改动任何 Lean 文件、目标文件、comparator 或 coord/targets/ 下的文件。

证据版本：行号按 2026-11-02 工作树读取；tmp/ 未受版本控制。S2040-312 源 SHA 记录为 E53A19EE604CD91DF38E0879196AEB7E183714EBBEC7F6A5712538CDD9092F42（coord/reports/S2040-actual-theta-link.md:92-98）。S2030 的读取日志只保留 axiom probe，没有源 SHA；P6/C6 的行号按当前工作树。未做 git commit/checkpoint 核对。

审计对象：

- tmp/sheaf/xif/paper/S2030Direct312Actual.lean（S2030）
- tmp/sheaf/xif/paper/S2040ActualThetaLink312.lean（S2040 新）
- tmp/sheaf/xif/paper/S2040ActualThetaLinkActual.lean（S2040 旧占位）
- coord/PAPER-TARGET-LOCK.md
- coord/targets/Challenge.lean、TargetsCheck.lean
- coord/targets/ChallengeC6Aligned.lean、TargetsCheckC6Aligned.lean
- tmp/sheaf/n8/closure/PaperP6Target.lean、PaperP6C6AlignedTarget.lean
- IUT-CRITIQUE-ROUTE-AUDIT.md 第 2 节六条禁止步骤

## 0. 结论

1. 当前仓库没有一份可称为 paper-level 3.12 的 Lean 声明。现有候选分别落在三种不同输入上，没有任何一份同时满足：同一份合格输入、q 侧来自该输入、Θ 侧是原文的 -|log Θ|、方向为 Q ≤ H、有限性非平凡。

2. S2030 是形状最接近的一份，但不是 paper-level。它是 -|log S1487Cand.q| ≤ -a0(T)；左端 q 是固定候选，不依赖 T；证明只用 a0(T) ≤ 1 与 |log S1487Cand.q| ≥ log 5 > 1，即 -|log q| < -1 ≤ -a0。它没有使用 T 自己的 q，也没有使用 Θ-link。

3. paperP6Target_actual / challenge_proved 和 challengeC6Aligned_proved 不是 paper-level 3.12，而且不是“弱版本”，是另一个不等式。它们的右端是 C6 的正对数体积 log(mass) ≥ 0；原文右端是 -|log Θ| ≤ 0。P6 证的是 log‖q‖ ≤ +log(mass)。若把 thetaLogVolume 读作 |log Θ| 的正值版本，则 P6 是 -|log q| ≤ |log Θ|，等价于 |log q| ≥ -|log Θ|。原文是 |log Θ| ≤ |log q|（即 |log q| ≥ |log Θ|）；P6 的右端是负的 |log Θ| 的正值版本，因此 P6 比原文更弱，并且由“负数 ≤ 非负数”自动成立，不涉及 Θ-link。

4. S2040 新文件的陈述形状是 paper-like 的（两端都是负数），但当前形式把 Θ 定义成 q 的实标量 q^(1/(2l))，且把 hull normalization 作为结构字段。它只能算 conditional schema；S2040FirstMissing 没有 inhabitant。旧文件 S2040ActualThetaLinkActual 更直接把结论 logVolumeComparison : O.qPilotLogVolume ≤ P.signedHullLogVolume 放进结构字段。

5. 建议的锁定对象是第 4 节的 PaperLevel312 规格：同一份合格输入上的 Q(I) ≤ H(I) 且 H(I) 有限。它是唯一的 paper-level 陈述形状；但当前没有可编译声明，因为缺 paperSignedHullOf（同一输入到 paper signed hull 的构造）和输入类型/桥。在补齐这两项之前，不应把任何现有声明标为 LOCKED。

6. 六条禁止步骤对照结论：S2030 落入第 1、2、3 条（第 4 条为效果上退化，第 5、6 条不落入）；S2040-312 落入第 1、2、3、5、6 条，第 4 条高风险；旧 S2040 第 1 条是字面落入（结论即字段）。P6/C6 落入第 1、2、3 条，第 4 条高风险。

## 1. 原文陈述与仓库约定

本文把 paper-level 3.12 固定为 IUT III Corollary 3.12 的 xi-f 有符号不等式及其有限性：

- Q = -|log q| < 0，q 取自同一份合格初始 Θ-数据的 q-pilot（一列 q[1u]）。
- H = -|log Θ| ≤ 0，Θ 为 Θ-pilot 所有 possible images 之并的 holomorphic hull 的 procession-归一化对数体积；H 起初可取 +∞，推论同时给出 H ∈ R。
- 结论：Q ≤ H，等价的正幅度形式 |log Θ| ≤ |log q|，且 H 有限。
- 输入只允许论文 Theorem 3.11 情形下的合格初始 Θ-数据；不允许 q-pilot/Θ-pilot comparison、local/global comparison morphism、κ = 0、S ≥ κ、h ≤ Θ、Q ≤ Θ、ValuesBounded，也不允许由结论定义的 effective zero divisor。

范围限制：本审计的“3.12”指 xi-f 有符号不等式与有限性，即 coord/ROADMAP-2026-11-02.md 第 6 节所称的 “3.12 inequality”。完整的 Corollary 3.12 还有 xi-a–xi-g 的其他条款；当前没有任何目标覆盖完整合取。如果“paper-level 3.12”指完整推论，那么连陈述都还缺。

仓库内的对应约定：

- coord/O2-PAPER-DEFINITIONS.md:27-31：论文 q-pilot 是负量 -|log q|；Θ 侧是 -|log Θ| ∈ R ∪ {+∞}；结论是 -|log Θ| ≥ -|log q|，等价于 |log Θ| ≤ |log q|。
- coord/O2-PAPER-DEFINITIONS.md:53：-|log q| 已是负实数；q-pilot 一侧不施加 (Ind1),(Ind2),(Ind3)。
- coord/O2-PAPER-DEFINITIONS.md:59-69：Θ 侧是 possible images 的并、其 holomorphic hull、procession average、Kummer isomorphisms 与 (Ind1)-(Ind3)。
- tmp/sheaf/xif/PaperSignedHull.lean:78-81：signedHullLogVolume = -(ambient.logVolume ambient.hull).toReal，注释明确这是 -|log Θ|，不是正值。
- tmp/sheaf/xif/paper/OrigXiFPaperSignedHullActual.lean:163-176：OrigXiFThetaHullLogVolume 是 hull 的 normalized Haar log-volume（|log Θ|）；OrigXiFSignedThetaHullLogVolume 是它的负值。

关键符号约定：原文的 H 与 Q 都是非正数；任何以 +log(mass) 或 +normalizedLogVolume 为 Θ 侧的声明，即使数值上成立，也不是原文的 H。

## 2. 现有候选的精确声明与证明路径

### 2.1 S2030：SourceNativeInitialThetaData + 固定 q

精确声明（tmp/sheaf/xif/paper/S2030Direct312Actual.lean:363-367）：

    theorem s2030_paper312_inequality
        (T : SourceNativeInitialThetaData.{0} l) :
        -|Real.log ‖S1487OQPilotScalarEqualityActual.S1487Cand.q‖| ≤
          OrigXiFSignedThetaHullLogVolume
            (s2030D T (s2030_native_bad_set_finite T))

相关声明（同文件）：

    -- :303-308
    noncomputable def s2030D
        (T : SourceNativeInitialThetaData.{0} l)
        (h : T.tuple.source.V_mod_bad.Finite) :
        OrigXiFPaperSignedHullData (S1902Carrier T) l :=
      letI : Fintype (Bad (nativePlaceSelection T)) := s2030FintypeOfFinite T h
      s2030DOf T

    -- :166-172 数值判据
    theorem s2030_neg_abs_log_q_le_neg_average_of_average_le_one
        (P : SignedHullLogActual (SignedLabel l.value))
        (hP : s1904ProcessionAverage P ≤ 1) :
        -|Real.log ‖S1487Cand.q‖| ≤ -s1904ProcessionAverage P := by
      have hq := s2030_log_five_le_abs_log_q
      have h1 := s2030_one_lt_log_five
      linarith

证明链：

1. s2030D T h 的 theta hull 是 s1902ActualThetaHull T，determinant 是 s1940PaperLStarDeterminant T，第三字段是 s1940_s1904_bridge T（S2030:267-271）。
2. s2030DOf_average_eq_a0 : s1904ProcessionAverage ... = s1915A0 T（S2030:279-282）。
3. s1915_a0_le_one : s1915A0 T ≤ 1（S1915ThetaHullA0Actual.lean:387-389）。
4. s2030D_average_le_one（S2030:312-318）给出 average ≤ 1。
5. s2030_neg_abs_log_q_le_neg_average_of_average_le_one 用 linarith 把 log 5 ≤ |log q| 与 1 < log 5 合起来。
6. OrigXiFSignedThetaHullLogVolume D = -average（OrigXiFPaperSignedHullActual.lean:218-222），于是得到 -|log q| ≤ -a0。

性质：

- 左端 q 是 S1487Cand，固定在 S1487FivePlace（Gaussian 域上 5 的位），localLogMagnitude ≥ log 5 > 1（S1487OQPilotScalarEqualityActual.lean:133,152-167）。它不依赖 T。
- 右端 -a0(T) 是实际 S1902 hull 的负对数体积，a0 ∈ [0,1]（S1915:382-393）。
- 由于 -|log q| < -1 ≤ -a0(T)，该不等式对任意 a0 ≤ 1 成立；T 只通过 a0 出现在右端，且 a0 ≤ 1 的上界已经足够。证明没有使用 T 的 q，也没有使用 q 与 Θ 之间的任何比较。
- 它不是“从更弱 native 输入构造 source”的问题；它本身就是 native T 层（SourceNativeInitialThetaData）的标量校准。

结论：S2030 是 [ACTUAL, weaker]，不是 paper-level 3.12。它甚至没有证明 paper 所需的 a0(T) ≤ |log q(T)|；对一般的 q(T)，|log q(T)| 可能小于 1，现有 a0 ≤ 1 不足以推出结论。

同源声明：S1944 的 s1944_paper312_inequality（tmp/sheaf/xif/paper/S1944Paper312Actual.lean:284-287）也用固定的 S1487Cand.q，因此同样不是 paper-level。coord/reports/S1944-paper-312-actual.md 把它称作 paper-level，是按“Θ 侧 actual”而非“q 侧来自同一输入”的标准；引用时应加注本审计的结论。coord/reports/S2040-actual-theta-link.md:51-69 把 S2030 称作 “genuine actual P-side/q-side scalar 3.12 route”，也应按本审计修正为 scalar calibration。

### 2.2 S2040-312：OriginalInput + 实标量 Θ + 结构字段

精确声明（tmp/sheaf/xif/paper/S2040ActualThetaLink312.lean:343-359）：

    structure S2040ThetaLink312
        (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
        (Opaper : S2038PaperOActual (I := I) (G := G) (envStrip := envStrip)
          (Label := Label) (Choice := Choice) (l := l) (V := V) O)
        (P : PaperSignedHull X label) where
      theaterLink : HodgeTheaterLink (I.theaterAt 0 0) (I.theaterAt 1 0)
      theaterLink_eq : theaterLink = I.linkAt 0 0 1 0
      displacement : S2040ThetaLinkDisplacement Opaper
      qPilotLogIdentification : O.qPilotLogVolume = Real.log Opaper.q
      hull_normalization : P.signedHullLogVolume =
        Real.log displacement.rootStackTheta

    -- :386-389
    theorem S2040ThetaLink312.paper312_inequality
        (L : S2040ThetaLink312 O Opaper P) :
        -|Real.log Opaper.q| ≤ P.signedHullLogVolume := by
      rw [← qPilotLogVolume_eq_neg_abs L]
      exact (mem_hullLogVolumeRay_iff).mp L.link_implies_inclusion

关键字段与模型（S2040:229-276）：

    structure S2040ThetaLinkDisplacement ... where
      rootStackTheta : Real
      rootStackTheta_eq : rootStackTheta = s2040Theta l Opaper.q
      rootStack_pow : rootStackTheta ^ (2 * l.value) = Opaper.q
      ambientQ : Type
      [commGroupQ : CommGroup ambientQ]
      ambientTheta : Type
      [commGroupTheta : CommGroup ambientTheta]
      embedQ : unitsMu.U →* ambientQ
      embedTheta : unitsMu.V →* ambientTheta
      intDegreeQ : ambientQ →* Multiplicative Int
      intDegreeTheta : ambientTheta →* Multiplicative Int
      logDegreeQ : ambientQ →* Multiplicative Real
      logDegreeTheta : ambientTheta →* Multiplicative Real
      generatorQ : ambientQ
      generatorTheta : ambientTheta

    -- :100-101
    noncomputable def s2040Theta (l : PrimeGeFive) (q : Real) : Real :=
      q ^ (((2 * l.value : Nat) : Real)⁻¹)

    -- :151-163
    theorem s2040_log_q_le_log_theta {q : Real} (hq0 : 0 < q) (hq1 : q < 1) :
        Real.log q ≤ Real.log (s2040Theta l q) := by
      have hlog : Real.log (s2040Theta l q) < 0 := s2040_log_theta_neg hq0 hq1
      have h2 : (1 : Real) ≤ 2 * (l.value : Real) := ...
      have hmul : (2 * (l.value : Real)) * Real.log (s2040Theta l q) ≤
          1 * Real.log (s2040Theta l q) :=
        mul_le_mul_of_nonpos_right h2 hlog.le
      rw [one_mul] at hmul
      rw [s2040_log_q_eq_twoL_mul_log_theta hq0]
      exact hmul

证明实质：

- Opaper.q = I.oneColumnQAtZero 是实际一列 q（S2040:179-181）。
- rootStackTheta 被字段固定为 s2040Theta l Opaper.q = q^(1/(2l))；hull_normalization 又把 P.signedHullLogVolume 固定为 Real.log rootStackTheta。
- 于是 paper312_inequality 变成 -|log q| ≤ log(q^(1/(2l)))；因 q < 1、2l ≥ 1，log q ≤ log(q^(1/(2l)))，数值上成立。
- 这里没有构造 paper Θ-hull；Θ 侧是 q 的实标量根。S2040FirstMissing（S2040:445-453）没有 inhabitant；s2040_paper312_of_firstMissing（S2040:482-490）只是把同一个 schema 再包一层。

旧占位 S2040ActualThetaLinkActual.lean 更直接：

    -- :46-57
    structure S2040ActualThetaLink ... where
      theaterLink : HodgeTheaterLink left right
      qPilotLinkCompatibility : Prop
      omuLinkCompatibility : Prop
      logVolumeComparison : O.qPilotLogVolume ≤ P.signedHullLogVolume

    -- :73-75
    theorem S2040ActualThetaLink.paper312_inequality
        (L : S2040ActualThetaLink left right O P) :
        O.qPilotLogVolume ≤ P.signedHullLogVolume :=
      (mem_hullLogVolumeRay_iff).mp L.link_implies_inclusion

logVolumeComparison 就是结论本身；这是目标假设，不是证明。新文件 312 相对旧文件确实把结论从字段移到证明，但代价是把 Θ 换成 q^(1/(2l)) 的实标量模型。

### 2.3 P6：SourceInitialThetaData + C6 正对数体积

精确声明（tmp/sheaf/n8/closure/PaperP6Target.lean:16-28）：

    def PaperP6Target (S : SourceInitialThetaData l) : Prop :=
      ∃ qLog thetaLog : ℝ,
        qLog = Real.log ‖(C7MassFormulaZeroSorry.qUnit S : PK S)‖ ∧
        thetaLog = C7MassFormulaZeroSorry.thetaLogVolume S ∧
        qLog ≤ thetaLog ∧
        (thetaLog : WithTop ℝ) < ⊤

    theorem paperP6Target_actual : PaperP6Target S :=
      ⟨Real.log ‖(qUnit S : PK S)‖,
        thetaLogVolume S,
        rfl, rfl,
        PaperP6ComparisonActual.paper_log_norm_le_thetaLogVolume S,
        PaperP6Final.thetaLogVolume_lt_top S⟩

PaperP6Conclusion 是同一内容的 structure（PaperP6Final.lean:66-80）。

证明实质（PaperP6ComparisonActual.lean:132-162）：

    theorem regionLogVolume_nonpos : regionLogVolume S ≤ 0 := by
      rw [regionLogVolume_eq_qPilot S]
      have hpos : 0 < ‖(qUnit S : PaperKf S)‖ := ...
      have hlt : ‖(qUnit S : PaperKf S)‖ < 1 := ...
      exact le_of_lt (Real.log_neg hpos hlt)

    theorem thetaLogVolume_nonneg : 0 ≤ thetaLogVolume S := by
      ...
      exact Real.log_nonneg hmreal

    theorem paper_regionLogVolume_le_thetaLogVolume :
        regionLogVolume S ≤ thetaLogVolume S :=
      le_trans (regionLogVolume_nonpos S) (thetaLogVolume_nonneg S)

    theorem paper_log_norm_le_thetaLogVolume :
        Real.log ‖(qUnit S : PaperKf S)‖ ≤ thetaLogVolume S := by
      rw [← regionLogVolume_eq_qPilot S]
      exact paper_regionLogVolume_le_thetaLogVolume S

关键：thetaLogVolume 是 Real.log ((c6UnitRefNormalizedData ... c6Hull).toReal)（C7MassFormulaZeroSorry.lean:119-121）。c6Hull 包含 unit reference，unit reference 的 normalized mass 为 1，故 hull mass ≥ 1，thetaLogVolume ≥ 0。q 侧 qUnit 的范数 < 1，故 log‖qUnit‖ < 0。于是 P6 的 qLog ≤ thetaLog 是“负数 ≤ 非负数”，由符号直接成立；证明只用 le_trans，没有用 qPilotRegion ⊆ c6Hull。

按原文写法：

- 原文要 |log Θ| ≤ |log q|，即 -|log q| ≤ -|log Θ|。
- P6 证 log‖q‖ ≤ +log(mass)；若把 thetaLogVolume 读作 |log Θ| 的正值版本，即 -|log q| ≤ +|log Θ|。
- 这不是原文的弱版本；它把右端换成正量，得到 |log q| ≥ -|log Θ|，比原文的 |log q| ≥ |log Θ| 更弱，并且由符号自动成立。P6 的真值来自 thetaLog ≥ 0，不来自 Θ-link。

theta_finite 是 (thetaLog : WithTop ℝ) < ⊤，其中 thetaLog : ℝ，由 WithTop.coe_lt_top 直接成立（PaperP6Final.lean:59-60）。它不能表达原文“H 起初可能为 +∞，后证有限”的内容。

### 2.4 C6Aligned：把 Q 和 Θ 都识别成 C6 正归一化体积

精确声明（tmp/sheaf/n8/closure/PaperP6C6AlignedTarget.lean:34-50）：

    def PaperP6C6AlignedTarget : Prop :=
      PaperP6NormalizedTarget S ∧
        (PaperP6NormalizedValuesActual.normalizedTheta S =
          (C6ActualIQData.actual ...).normalizedLogVolume
            (c6Hull ...)) ∧
        (Real.log ‖(qUnit S : C7MassFormulaZeroSorry.PaperKf S)‖ =
          (C6ActualIQData.actual ...).normalizedLogVolume
            (qPilotRegion S))

    theorem paperP6C6AlignedTarget_actual :
        PaperP6C6AlignedTarget S :=
      ⟨paperP6NormalizedTarget_actual S,
        normalizedTheta_eq_c6NormalizedLogVolume S,
        qLog_eq_c6NormalizedLogVolume_qPilot S⟩

PaperP6NormalizedTarget（PaperP6NormalizedValuesActual.lean:68-74）：

    def PaperP6NormalizedTarget : Prop :=
      (∀ z ∈ normalizedValueSet S, z ≤ normalizedTheta S) ∧
      Real.log ‖(qUnit S : PaperKf S)‖ ≤ normalizedTheta S

normalizedTheta = thetaLogVolume S / d S（PaperP6NormalizedValuesActual.lean:33-35），仍是正量；normalizedLogVolume 是 arithmeticTupleNormalizedLogVolume（C6ActualIQData.lean:32-49），也是正量。两个 C6 等式本质上是把 q 和 Θ 都对齐到 C6 的同一个正归一化读数；normalizedTheta_eq_c6NormalizedLogVolume 的证明是展开后 rfl（PaperNormalizedLogBridge.lean:94-102），不是 paper hull 的对象识别。

因此：

- challengeC6Aligned_proved 的三项都是 C6 正量的对齐/比较；其中 qLog ≤ normalizedTheta 这一项仍是“负数 ≤ 非负数”，另一项是对 normalizedValueSet 的界。
- 它不是 paper-level 3.12；最多是 C6/one-factor 的对齐辅助。
- 它的命名（Challenge、proved）容易被读成“paper challenge 已证”，但 STATE.md:2401 自己都标 target_accepted=false。

### 2.5 目标文件中的 Challenge

    -- coord/targets/Challenge.lean:11-13
    def Challenge : Prop :=
      ∀ S : SourceInitialThetaData l,
        LeanFormal.IUT.N8Closure.PaperP6Target2.PaperP6Target S

    -- coord/targets/TargetsCheck.lean:16-17
    theorem challenge_proved : Challenge (l := l) :=
      fun S => LeanFormal.IUT.N8Closure.PaperP6Target2.paperP6Target_actual S

    -- coord/targets/ChallengeC6Aligned.lean:10-12
    def ChallengeC6Aligned : Prop :=
      ∀ S : SourceInitialThetaData l,
        LeanFormal.IUT.N8Closure.PaperP6C6AlignedTarget.PaperP6C6AlignedTarget S

    -- coord/targets/TargetsCheckC6Aligned.lean:14-15
    theorem challengeC6Aligned_proved : ChallengeC6Aligned (l := l) :=
      fun S => LeanFormal.IUT.N8Closure.PaperP6C6AlignedTarget.paperP6C6AlignedTarget_actual S

这两个 Challenge 的输入是 SourceInitialThetaData；q 侧是 qUnit（ClauseB 在一个选定 bad F-place 的 q），Θ 侧是 C6 正对数体积。它们不是第 4 节的 PaperLevel312。

## 3. 逐项对比

声明 | 输入 | q 侧 | Θ 侧 | 结论 | 额外假设 | 是否 paper 3.12
---|---|---|---|---|---|---
s2030_paper312_inequality | SourceNativeInitialThetaData | 固定 S1487Cand.q，与 T 无关 | -a0(T)，S1902 hull | -\|log q\| ≤ -a0 | 无（bad finite 由 ClauseB 证） | 形状/符号正确，但 q 错、证明靠 a0≤1；否
paperP6Target_actual / challenge_proved | SourceInitialThetaData | qUnit（一个 bad place） | +thetaLogVolume（C6 hull mass log） | log q ≤ +log mass | 无 | 右端正量；更弱且自动成立；否
challengeC6Aligned_proved | SourceInitialThetaData | C6 normalizedLogVolume(qPilotRegion) | C6 normalizedLogVolume(c6Hull) | qLog ≤ normalizedTheta + 两个 C6 等式 | 无 | C6 正量对齐；否
S2040ThetaLink312.paper312_inequality | OriginalInput + S2038PaperOActual + S2040ThetaLink312 | O.qPilotLogVolume（= log Opaper.q） | P.signedHullLogVolume（= log(q^(1/(2l)))） | -\|log q\| ≤ H | L : S2040ThetaLink312（含 qLogId + hull_normalization） | 形状正确，但 Θ 是 q 的实标量模型；conditional；否
S2040ActualThetaLink.paper312_inequality | 同上 | 同上 | 同上 | 同上 | logVolumeComparison 字段 = 结论 | 目标假设；否
PaperLevel312（第 4 节规格） | 待定的 paper 输入 | 同一输入的 paper q-pilot | 同一输入的 paper -\|log Θ\| | Q ≤ H 且 H 有限 | 仅论文合格条件 | 是（唯一形状）；当前无声明

## 4. 唯一的 paper-level 陈述

### 4.1 形状

唯一可称为 paper-level 3.12 的陈述是：

对同一份合格初始 Θ-数据 I，令 Q(I) = -|log q(I)|、H(I) = -|log Θ(I)| 为 I 自身的 q-pilot 与 Θ-pilot 读数；则 Q(I) ≤ H(I)，且 H(I) 有限。

用 Lean 规格写（不是当前可编译声明）：

    -- PaperOriginalInput = 经审计的 paper 输入（SourceInitialThetaData 或
    -- 其忠实 refinement，且已从它构造出 O-layer q-pilot 与 paper hull）。
    -- paperQPilotObjectOf 与 paperSignedHullOf 是缺失构造；没有它们，
    -- 本段只是规格，不是可编译声明。

    def PaperLevel312 (l : PrimeGeFive) : Prop :=
      ∀ I : PaperOriginalInput l V,
        (paperQPilotObjectOf I).qPilotLogVolume ≤
          (paperSignedHullOf I).signedHullLogVolume ∧
        (paperSignedHullOf I).ambient.logVolume
          (paperSignedHullOf I).ambient.hull < ⊤

要点：

- Q(I) 来自 paperQPilotObjectOf I；其值是 I.qPilotSignedLogVolume = -|log I.oneColumnQAtZero|（ThetaLinkLogKummerActual.lean:54-77）。这是论文的一列 q[1u]，不是 S2030 的固定 S1487Cand.q，也不是 P6 的单 bad-place qUnit。
- signedHullLogVolume 是 PaperSignedHull.signedHullLogVolume（PaperSignedHull.lean:80-81），其值是 -(ambient hull log volume).toReal；这是原文的 -|log Θ|，不是 +thetaLogVolume。
- 有限性是 ambient.logVolume ambient.hull < ⊤，不是 (x : WithTop ℝ) < ⊤ 的 Real 强制；后者恒真。
- 两侧必须来自同一份 I；不能在 q 侧用固定候选、Θ 侧用另一个输入。

### 4.2 当前可类型检查的 native 形式（仅作 CANDIDATE）

在 SourceNativeInitialThetaData 层，可以用现有的 NativeC3.nativeQActual 与 s2030D 写出同一输入的形式：

    -- 类型检查上应成立；本审计未编译。
    def PaperLevel312Native (l : PrimeGeFive) : Prop :=
      ∀ X : LeanFormal.IUT.N8Closure.NativeInput.N8NativeInput l,
        -|Real.log ‖(LeanFormal.IUT.N8Closure.NativeC3.nativeQActual X).q‖| ≤
          OrigXiFSignedThetaHullLogVolume
            (s2030D X.S (s2030_native_bad_set_finite X.S))

它相对 S2030 只改了一件事：把固定的 S1487Cand.q 换成 X.S 自己的 nativeQActual。但它仍不是 paper-level：

- 输入是 N8NativeInput（SourceNativeInitialThetaData + NativeLattice），多了 lattice；
- 输入是 native T 层，不是 SourceInitialThetaData/OriginalInput 的 paper 层；
- NativeC3.nativeQActual 目前以 N8NativeInput 为参数（NativeC3.lean:80-82），虽然 q 的构造只用到 X.S.clauseB，但要成为 T-only 读数需要一个小重构；
- 它没有证明 a0(T) ≤ |log q(T)|；S2030 的 a0≤1 证明不能直接复用，因为 |log q(T)| 可能 < 1。

因此 PaperLevel312Native 只能作为 CANDIDATE/回归检查，不能作为 LOCKED paper-level 目标；除非输入类型审计最终决定 native T 就是 paper 输入的忠实 refinement，并关闭 G0。

### 4.3 为什么不能从现有声明中“选一个”

- S2030 的 q 不在 T 里；它没有证明 a0(T) ≤ |log q(T)|，只证明了 a0(T) ≤ 1 < |log q_fixed|。把 S1487Cand.q 换成 T 的 q 会使证明失效；这不是改名的机械操作。
- P6/C6 的 Θ 是正的 C6 对数体积，方向与原文相反；它们不是原文的弱版本。
- S2040 的 Θ 是 q^(1/(2l)) 实标量，且 hull_normalization 是字段；换掉它会回到“paper hull 构造”缺口，而不是补一个证明。
- OriginalInput 的 initial : SourceDefinition31Data 是 contract shell（PAPER-TARGET-LOCK.md:68-73）；PAPER-TARGET-LOCK 明确不能把它当 paper 输入。因此 I.qPilotSignedLogVolume 虽然是 paper 形状，其输入仍不合格。

## 5. 六条禁止步骤对照

以下“是”表示该声明/路线落入该条禁止模式，不能作为 paper-level 证明；“可能”表示形式上不一定字面命中，但效果上等价或高风险；“否”表示未发现。

### 5.1 S2030

# | 禁止步骤 | 判定 | 证据
---|---|---|---
1 | 不得从 P6Comparison/C9/C4/C5/直接 scalar map 得 Q ≤ Θ | 是 | s2030_paper312_inequality 就是 -\|log q\| ≤ H；证明是 s2030_neg_abs_log_q_le_neg_average_of_average_le_one 的 linarith（:166-172）加 a0≤1（S1915:387），没有任何 Θ-link/Eta 比较。它不是从所列模块出发，但仍是“直接 pilot comparison”的同一形状。
2 | 不得把 q、Θ、hull、log-shell 的值放进同一个 Real 比较 | 是 | 左端 Real.log，右端 OrigXiFSignedThetaHullLogVolume 是 -(ENNReal.toReal)（OrigXiF:174-176）；linarith 直接在 ℝ 上比较。没有 Rval→Rss 的构造映射，没有单位/积分结构。
3 | 不得在 EtaQ = EtaAnab S 前证 degree/hull/normalized-log-volume 不等式 | 是 | S2030 没有 EtaQ/EtaAnab；直接证 hull inequality。
4 | 不得用退化 readout（reference=region、Θ=0、Values={0}、JRange=univ） | 可能（效果上） | 不是字面 Θ=0；但证明只用 a0 ≥ 0/a0 ≤ 1，对任意 a0≤1 都成立，H 的具体值不参与。对 closedForm≤0 的 T，a0=0，H=0，确实是退化分支。
5 | 不得把 Ind1/2/3 编码成自由 Real offset/arbitrary common-line adjustment | 否（字面） | 没有 Ind1/2/3，也没有自由 offset；q 是固定候选，hull 是实际 S1902 构造。但“固定 q”本身是外部选择，不是 T 的 q。
6 | 不得用 imported axiom/arbitrary donor/True-empty interface | 否 | 公理 trio；S1902 hull 是实际构造；S1487Cand 是具体候选；无 arbitrary carrier。SourceNativeInitialThetaData 的 ClauseA-F 是实际字段（SourceDefinition31Quantifiers.lean:889-1558），不是 True 槽。

### 5.2 S2040-312

# | 禁止步骤 | 判定 | 证据
---|---|---|---
1 | 不得直接 pilot comparison | 是 | paper312_inequality 是 Q ≤ H；S2040ThetaLink312 的 qPilotLogIdentification 与 hull_normalization 直接给出两端读数；rootStackTheta = q^(1/(2l))（:242-245）。没有 EtaComparison；Θ-link 被替换成实标量根。
2 | 不得 common-Real-line collapse | 是 | qPilotLogVolume、signedHullLogVolume 都是 ℝ；logDegreeQ/Theta : ... →* Multiplicative Real（:260-263）；最终不等式在 ℝ。ambient groups 是任意类型，没有到真实 value group 的构造映射。
3 | 不得在 Eta 等式前做 hull/degree 不等式 | 是 | 没有 EtaQ/EtaAnab；hull_normalization 是字段，不是由实际 hull 计算的。
4 | 不得退化 readout | 可能/高 | hull_normalization : P.signedHullLogVolume = Real.log rootStackTheta 把 H 定义成 q 的函数；rootStackTheta 是 s2040Theta 的实标量。不是字面 Θ=0，但 Θ 读数不是独立 hull 读数，效果接近 reference=region。
5 | 不得自由 Real adjustment | 是 | s2040Theta 是 q^(1/(2l)) 的自由实标量；rootStackTheta 是 Real 字段，仅由 rootStackTheta_eq 钉到该公式；logDegreeQ/Theta 是任意 monoid hom；没有 Ind1/2/3 数据。
6 | 不得 arbitrary donor/True interface | 是（arbitrary carrier） | S2040UnitsMuLink.U/V : Type（:200-212）、S2040ThetaLinkDisplacement.ambientQ/ambientTheta : Type（:247-251）都是任意类型，只带 Group/CommGroup 和 hom 字段；没有绑定到 paper O^×/O^×μ/ambient value group。没有 axiom，但“arbitrary carrier”这一条命中。

旧 S2040ActualThetaLinkActual 另有一条更直接的违规：

- logVolumeComparison 字段就是 O.qPilotLogVolume ≤ P.signedHullLogVolume（:46-57），paper312_inequality 是它的投影（:73-75）。这是目标假设，字面落入第 1 条；qPilotLinkCompatibility/omuLinkCompatibility 是任意 Prop 字段，也落入第 6 条的 True/empty interface 风险。

### 5.3 P6 / C6Aligned（补充，不是用户点名但同类）

# | 判定 | 证据
---|---|---
1 | 是 | paper_log_norm_le_thetaLogVolume 是 Q ≤ Theta，直接由 C6 的 regionLogVolume_nonpos 与 thetaLogVolume_nonneg 得到；没有 Θ-link。
2 | 是 | qLog 与 thetaLog 都是 ℝ；le_trans 直接在 ℝ 上比较。
3 | 是 | 没有 EtaQ/EtaAnab；hull inequality 先证。
4 | 可能（高） | theta_finite 是 WithTop.coe_lt_top，恒真；不等式是“负数 ≤ 非负数”；+log(mass) 是正幅度，不是原文的 -\|log Θ\|。
5 | 否 | 没有 Ind/free Real offset；C6 读数是实际归一化体积。
6 | 否（无 arbitrary carrier/axiom） | 但输入 SourceInitialThetaData 的 ClauseA 含 opaque Prop 字段（SourceInitialThetaData.lean:1326-1356），属于输入语义未审计的风险，不是本条的形式命中。

## 6. 风险清单

1. 命名风险（最高）：paperP6Target_actual、challenge_proved、challengeC6Aligned_proved 的名字含 paper/Challenge/proved，容易被下游当作 paper-level 3.12。它们实际是 C6/one-factor 辅助或正量对齐。建议在 STATE、ROADMAP、queue 中加“不得作为 3.12 引用”的列表。

2. 目标漂移风险：若把 P6/C6 锁成 3.12，原文的 |log Θ| ≤ |log q| 会被替换成 -|log q| ≤ +log(mass)（等价于 |log q| ≥ -|log Θ|，由符号自动成立），3.12 的数学内容消失。

3. 证明复用风险：S2030 的 a0 ≤ 1 + |log q_fixed| > 1 不能平移到 q(T)；|log q(T)| 可能小于 1。把 S1487Cand.q 换掉后，现有证明不成立，必须重新证 a0(T) ≤ |log q(T)|。

4. S2040 模型风险：S2040FirstMissing 没有 inhabitant；若未来用 s2040Theta 的实标量根去填，就是自由 Real 模型，落入第 5 条。S2040ThetaLinkDisplacement 的 ambientQ/ambientTheta 是任意类型，不能声称是 paper O^×/O^×μ。

5. 有限性空洞风险：P6 的 theta_finite 是 WithTop.coe_lt_top，恒真；S2030/OrigXiF 的 OrigXiFThetaHullLogVolume_lt_top 也由 hull_logVolume_eq_procession 的 ofReal 直接得到（OrigXiF:197-201）。当前形式不能表达“H 起初可为 +∞，后证有限”。若目标包含有限性，必须从可能为 ⊤ 的 ENNReal hull volume 出发，证明 < ⊤。

6. 输入三难：

- SourceDefinition31Data 是 contract shell（PAPER-TARGET-LOCK.md:68-73），但 OriginalInput.initial 正是它（SourceOriginalInput.lean:41-46）；
- SourceInitialThetaData 是 paper-shaped，但 ClauseA 含 opaque Prop 槽（SourceInitialThetaData.lean:1326-1356），且没有到 paper O/hull 的构造；
- SourceNativeInitialThetaData 有实际 clauses 与 S1902/S1940 链，但它是 native T 层，和 SourceInitialThetaData 没有现成桥（G0；O2-PAPER-DEFINITIONS.md:18-21）；XI_F_ORIGINAL_ROUTE.md:73 明确“不把 SourceDefinition31Data 换成 native T”。

在这三者之间未做选择/桥之前，无法写出同一输入上的 paper-level 3.12。

7. 单 bad-place/one-factor 风险：P6/C6 的 q 是 ClauseB 在一个选定 bad F-place 的 q；原文 q-pilot 是一列 q[1u]（S2040 使用 I.oneColumnQAtZero）。one-place 读数不能直接称为 paper q-pilot；独立 review 也标了 locality qualification（PAPER-P6-INDEPENDENT-REVIEW.md:66-69）。

8. C6 对齐的循环风险：normalizedTheta = C6.normalizedLogVolume(c6Hull) 与 qLog = C6.normalizedLogVolume(qPilotRegion) 是把两端都对齐到 C6 读数；它证明的是 C6 内部一致性，不是 paper q/Θ 的对象识别。normalizedTheta_eq_c6NormalizedLogVolume 的证明展开后是 rfl（PaperNormalizedLogBridge.lean:94-102），不能当作 source semantics 的独立证据。

9. 旧 review 的盲点：PAPER-P6-INDEPENDENT-REVIEW.md 的 PARTIAL 结论核对了 Q/Theta 的 actuality 与 Values provenance，但没有对照 O2 的 signed -|log Θ| 约定；因此不能把该 review 当作“P6 已是 3.12”的证据。本审计补上了这个 sign/direction 检查。

10. S2030 的“strict”误导：s2030_paper312_strict 的严格性来自 |log q_fixed| > 1 ≥ a0，不是来自 paper 的 Θ-link；不要把它当作原文严格不等式的证据。

## 7. 建议分类

分类定义：

- LOCKED：只表示陈述被锁定为唯一 paper-level 目标；不表示有证明或 target_accepted。
- CANDIDATE：可能是目标形状或可复用校准，但当前不能作为 paper-level 验收。
- NOT paper-level：不能作为 3.12 的陈述或证明。

对象 | 分类 | 理由
---|---|---
s2030_paper312_inequality / s2030_paper312_package | NOT paper-level（保留为 [ACTUAL, weaker] 标量校准） | q 固定 S1487Cand，不依赖 T；证明靠 a0≤1 与 \|log q\|>1；没有 Θ-link；不能给出 a0(T) ≤ \|log q(T)\|。
paperP6Target_actual / challenge_proved | NOT paper-level（C6/one-factor 辅助） | Θ 侧是正的 C6 hull log-volume；不等式是“负数 ≤ 非负数”；右端正量，比原文更弱且自动成立；theta_finite 恒真。
challengeC6Aligned_proved | NOT paper-level（C6 对齐辅助） | 三项都是 C6 正归一化体积；两个等式是 C6 对齐/定义展开；不是 paper hull 的对象识别。
S2040ThetaLink312.paper312_inequality | CANDIDATE（仅形状；当前形式 NOT） | 两端都是负数、方向正确；但 Θ = q^(1/(2l)) 实标量，hull_normalization 是字段，S2040FirstMissing 无 inhabitant；落入禁止步骤 1/2/3/5/6。
S2040ActualThetaLink.paper312_inequality | NOT paper-level | logVolumeComparison 字段就是结论；目标假设。
PaperLevel312（第 4 节规格） | LOCKED（仅陈述形状；当前无声明/无证明） | 唯一同时满足“同一输入、q 来自输入、Θ 是 paper signed hull、方向正确、有限性非平凡”的形状。锁定前必须先定输入与 paperSignedHullOf。
PaperLevel312Native（4.2 的可编译候选） | CANDIDATE | 同一 native 输入的 q/Θ 形式；但输入多了 lattice、属于 T 层；未证明一般 q 的不等式；只可作回归/桥接候选。

建议的最终状态：target_accepted = false；kernel_closed = false（3.12 目标未闭）；没有任何现有声明标为 LOCKED 的 paper-level 3.12。唯一可锁的是 PaperLevel312 的陈述形状，且必须先解决输入三难与 paperSignedHullOf。

## 8. 建议的下一步（不改变目标，仅审计建议）

1. 先定输入，不要先证不等式。在 SourceInitialThetaData（paper-shaped）与 SourceNativeInitialThetaData（actual clauses/native T）之间做一次正式审计，决定哪一个是 PaperInitialThetaData；若选 paper 型，先补 G0 source binding，禁止直接把 native T 当 paper source（XI_F_ORIGINAL_ROUTE.md:73）。

2. 构造 paperSignedHullOf：从同一份输入构造 PaperSignedHull（或 OrigXiFPaperSignedHullData），并把 hull_logVolume_eq_average 作为要证的 source obligation，而不是字段假设。没有这个构造，PaperLevel312 只是规格。

3. 定义同名 q 读数：用 I.oneColumnQAtZero/I.qPilotSignedLogVolume 的 paper 版本；不要复用 S1487Cand.q，也不要把 P6 的单 bad-place qUnit 直接当 q-pilot。

4. 新写 coord/targets/PaperLevel312.lean（不在本次审计中创建）：只放陈述与 Challenge/comparator，不放 proof；#print axioms 在陈述编译后再跑。不要修改现有 Challenge/ChallengeC6Aligned。

5. 在 ROADMAP/STATE/queue 加“不得作为 3.12 引用”清单：S2030、P6、C6Aligned、旧 S2040；S2040-312 标注 conditional schema。

6. 对 S2040FirstMissing 做逐字段禁止步骤审查；在输入未定时，禁止用 s2040Theta 填 rootStackTheta/hull_normalization；若保留该模型，必须标为 model/negative control，而不是 paper O-layer。

7. 有限性单独验收：要求从 ENNReal 的 hull volume 证明 < ⊤，不接受 (x : WithTop ℝ) < ⊤；P6 的 theta_finite 不能计入。

8. 复核 prior reviews：PAPER-P6-INDEPENDENT-REVIEW.md 的 PARTIAL 结论仍有效于其范围（Q/Theta actuality、Values provenance），但不覆盖 sign/direction；在引用处加注本审计的结论。

## 9. 验证状态（本审计）

- statement_compiles：未运行。本文没有新增/修改 Lean 声明；第 4 节的 PaperLevel312 是规格，PaperLevel312Native 未编译。
- proof_body_checked：未运行。
- kernel_closed：未复验。引用的现有日志/STATE 记录：S2030 S2030build.log 全部 [propext, Classical.choice, Quot.sound]，无 sorryAx；S2040-312 报告记录 EXIT=0、axioms trio（coord/reports/S2040-actual-theta-link.md:92-98）；P6 coord/targets/AxiomAudit.txt:3-7 记录 trio；C6Aligned coord/STATE.md:2401 记录 EXIT=0、trio，但 coord/targets/ 没有留存的 C6Aligned 日志。
- target_accepted：否。
- 未运行：lake build、lake env lean、comparator、全 Project 构建、独立语义审查。
- 未改动：任何 .lean、coord/targets/*、PAPER-TARGET-LOCK.md、ROADMAP、STATE、queue、AUDIT_LEDGER.md。

## 附录 A：精确声明索引

声明 | 文件:行
---|---
SourceNativeInitialThetaData | LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean:1681-1689
s2030_paper312_inequality | tmp/sheaf/xif/paper/S2030Direct312Actual.lean:363-367
s2030D | 同上 :303-308
s2030_neg_abs_log_q_le_neg_average_of_average_le_one | 同上 :166-172
s1915A0 | tmp/sheaf/xif/paper/S1915ThetaHullA0Actual.lean:120-121
s1915_a0_le_one | 同上 :387-389
OrigXiFSignedThetaHullLogVolume | tmp/sheaf/xif/paper/OrigXiFPaperSignedHullActual.lean:174-176
OrigXiFThetaHullLogVolume_lt_top | 同上 :197-201
OrigXiFSignedThetaHullLogVolume_eq_neg_average | 同上 :218-222
s2040Theta | tmp/sheaf/xif/paper/S2040ActualThetaLink312.lean:100-101
S2040ThetaLinkDisplacement | 同上 :229-276
S2040ThetaLink312 | 同上 :343-359
S2040ThetaLink312.paper312_inequality | 同上 :386-389
S2040FirstMissing | 同上 :445-453
S2040ActualThetaLink.logVolumeComparison | tmp/sheaf/xif/paper/S2040ActualThetaLinkActual.lean:46-57
S2040ActualThetaLink.paper312_inequality | 同上 :73-75
qPilotSignedLogVolume | tmp/sheaf/xif/paper/ThetaLinkLogKummerActual.lean:76-77
PaperP6Target | tmp/sheaf/n8/closure/PaperP6Target.lean:16-21
paperP6Target_actual | 同上 :23-28
PaperP6C6AlignedTarget | tmp/sheaf/n8/closure/PaperP6C6AlignedTarget.lean:34-44
paperP6C6AlignedTarget_actual | 同上 :46-50
Challenge / challenge_proved | coord/targets/Challenge.lean:11-13、TargetsCheck.lean:16-17
ChallengeC6Aligned / challengeC6Aligned_proved | coord/targets/ChallengeC6Aligned.lean:10-12、TargetsCheckC6Aligned.lean:14-15
PaperSignedHull.signedHullLogVolume | tmp/sheaf/xif/PaperSignedHull.lean:78-81
OriginalInput | LeanFormal/IUT/IUTIII/Theorem311/SourceOriginalInput.lean:41-46
