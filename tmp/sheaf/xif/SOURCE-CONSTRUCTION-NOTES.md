# xi-f 原文构造笔记（2026-10-28）

## 0. 用户最新指令（必须遵守）

> 去看看原文，以及相关的文章，去构造对象，而不是在这里说对象没有构造，然后就给我 idle。

> 做笔记记录下来吧，不然等下忘了又给我 idle 了。

结论：

- 不允许“对象没有，所以 idle”。
- 先读原文和 related papers，找出对象定义，再在 Lean 里构造 actual object / actual data / actual proof。
- 只有读完原文、确认当前 source 数据确实不足时，才允许 blocked；并且要写出原文位置、缺的数学数据、为什么现有定义推不出。
- 不允许用 wrapper/alias/重复定理/空结构冒充构造。
- agent 仍然 WRITE-ONLY：不调用 lake/lean，不自己等编译；写文件后 append tmp/xif_compile_queue.txt，由中央 watchdog 统一编译。

## 1. 原文文本位置（已抽取）

原始 PDF：

- tmp/external/promachina-iut-lean/docs/papers/mochizuki-iut-i.pdf
- tmp/external/promachina-iut-lean/docs/papers/mochizuki-iut-ii.pdf
- tmp/external/promachina-iut-lean/docs/papers/mochizuki-iut-iii.pdf
- tmp/external/promachina-iut-lean/docs/papers/mochizuki-iut-iv.pdf
- tmp/external/promachina-iut-lean/docs/papers/dupuy-hilado-corollary-312-initial-theta-indeterminacies.pdf
- tmp/external/promachina-iut-lean/docs/papers/higuchi-formal-negative-result-step-xi.pdf
- tmp/external/promachina-iut-lean/docs/papers/hoshi-introduction-to-iut.pdf
- tmp/external/promachina-iut-lean/docs/papers/pajo-scale-free-common-container-comparisons.pdf

已抽取纯文本（带 PAGE 标记）：

- tmp/source-extract/iut1.txt
- tmp/source-extract/iut2.txt
- tmp/source-extract/iut3.txt
- tmp/source-extract/iut4.txt
- tmp/source-extract/cor312.txt
- tmp/source-extract/higuchi.txt
- tmp/source-extract/hoshi.txt
- tmp/source-extract/pajo.txt

## 2. IUT III 中的核心对象（原文位置）

### 2.1 q-pilot object

原文：IUT III §3，p.15-19（iut3.txt 第 880-1080 行附近）。

定义要点：

- 在 global realified Frobenioid 中，由 q_v（v ∈ V_bad）的零 locus 决定的 arithmetic divisor。
- 称为 q-pilot object。
- log-volume 记为 −|log(q)| ∈ R，且 |log q| > 0。
- 在 Θ±ellNF-Hodge theater 的 (1,0) 上考虑。
- 通过 log-shell、log-link、Θ×μ LGP-link 与 multiradial representation 关联。

Lean 目标：

- 找出现有 qPilot 相关文件（QPilotObjectActual / QPilotActual / NativeQNorm 等）。
- 构造 actual q-pilot arithmetic divisor / realified Frobenioid 对象。
- 构造 actual q-pilot log-volume，并证明等于论文形式 −|log q|（不是假设）。

### 2.2 Θ-pilot object

原文：IUT III §3，p.15-19。

定义要点：

- 由 theta values {q_j^2}_{j=1..l*} 的零 locus 决定的 arithmetic divisor。
- 称为 Θ-pilot object。
- 其 holomorphic hull 的 log-volume 记为 −|log(Θ)| ∈ R ∪ {+∞}。
- 与 q-pilot 通过 Θ×μ LGP-link / multiradial representation 比较。

Lean 目标：

- 构造 actual Θ-pilot divisor。
- 构造 actual holomorphic hull 的 log-volume。
- 建立 q-pilot 与 Θ-pilot 在共同 container 中的实际关系，而不是只写 interface。

### 2.3 multiradial representation / Ind1, Ind2, Ind3

原文：IUT III Theorem 3.11，p.19-25 附近；Cor 3.12。

内容：

- (a) tensor packets of log-shells
- (b) splitting monoids of LGP-monoids acting on (a)
- (c) copies of F_mod^× labeled by j ∈ F_l^× acting on (a)
- 商掉 (Ind1) procession automorphisms、(Ind2) F⊣×μ-prime-strip automorphisms、(Ind3) log-Kummer correspondence indeterminacy。

Lean 目标：

- 构造 actual Ind1/Ind2/Ind3 作用/商/参数集。
- 构造 actual multiradial representation 的 final form。
- 不允许用 True/PUnit/任意 action 充当。

### 2.4 log-Kummer correspondence

原文：IUT III §3（p.18-25），Theorem 3.11/Cor 3.12；另见 IUT III §1-2。

Lean 目标：

- 构造 actual log-Kummer correspondence 对象/作用。
- 接到 q-pilot/Θ-pilot 的实际 log-shell 数据。
- 不能只保留 MissingLogKummer 字段。

### 2.5 Θ×μ LGP-link / Theta-link

原文：IUT III §1-2（p.1-15）；IUT IV §1。

Lean 目标：

- 构造 actual Θ×μ LGP-link / Theta-link comparison。
- 构造 value group (−)⊩▶ 和 unit group (−)⊣×μ 两侧的数据及 gluing isomorphism。
- 现有 ThetaLink 文件若是 interface，要补 actual data，不是再加 wrapper。

## 3. IUT IV 中的 log-volume 对象

原文：IUT IV §1-2，Theorem 1.10 附近。

对象：

- procession-normalized mono-analytic log-volume
- holomorphic hull 的 log-volume
- log-shell / tensor packet 的 log-volume 估计

Lean 目标：

- 构造 actual procession-normalized log-volume 对象。
- 构造 normalization（canonical unit reference / normalized weights）。
- 接到 q-pilot/Θ-pilot 的 actual log-volume，而不是只留 interface。

## 4. xi-f bridge 的原文/二手文献

原文：

- IUT III Cor 3.12，Step (xi-e) → Step (xi-f)，p.183 附近。
- Step (xi-e)：holomorphic hull + log-volume 后，输出 side 是 R≤−|log(Θ)| 的可能 log-volume 集合。
- Step (xi-f)：输出数据可能性的构造构成 input pilot-object log-volume 的构造，得到 −|log(q)| ∈ R≤−|log(Θ)|。

二手：

- higuchi-formal-negative-result-step-xi.pdf：把 xi-f 形式化为 bridge statement L ∈ R≤u。
- dupuy-hilado-corollary-312-initial-theta-indeterminacies.pdf：Cor 3.12 的初始 theta indeterminacy 讨论。

Lean 目标：

- 构造 actual common container、input realization、output possibilities、hull operator、log-volume map。
- 证明 actual inclusion，不是只写 MissingXiFBridge。

## 5. 当前 agent 分工（原文 → 对象）

| agent | 原文任务 | 目标对象 |
|---|---|---|
| kummer | IUT III §3 q-pilot | actual q-pilot arithmetic divisor + log-volume |
| logdescent | IUT III §3 Θ-pilot | actual Θ-pilot divisor + hull/log-volume |
| multiradial | IUT III Theorem 3.11 | actual Ind1/Ind2/Ind3 + multiradial representation |
| iplsheapt | IUT III log-Kummer / IPL/SHE/APT | actual log-Kummer correspondence + SHE/IPL/APT data |
| volumedet | IUT IV §1-2 | actual procession-normalized log-volume |
| qside | IUT III q-pilot log-volume | actual q-pilot log-volume = −|log q| |
| primespine | IUT III Step(xi-e/f), Cor 3.12 | actual hull/log-volume + xi-f inclusion |
| transport | IUT III §1-2 | actual Θ×μ LGP-link / Theta-link comparison |

## 6. 每个 agent 的固定流程（防 idle）

1. 先读对应原文段落（iut3/iut4/相关论文），记录页码/行号。
2. 找现有 Lean 定义/文件，列出 paper object → Lean target 的对应。
3. 构造 actual object/data/proof；能写多少写多少，不写 wrapper。
4. 写文件后 append tmp/xif_compile_queue.txt。
5. 报告：原文位置、新构造的 Lean 声明、消费者、仍缺什么（如果 blocked）。
6. 只有读完原文、确认 source 不足才 blocked；不能一句“缺对象”就停。
7. 不调用 lake/lean；中央 watchdog 编译。

## 7. 当前实际缺口（按原文对象）

- actual q-pilot arithmetic divisor / realified Frobenioid object
- actual Θ-pilot arithmetic divisor
- actual holomorphic hull 的 log-volume
- actual multiradial representation / Ind1/Ind2/Ind3 作用
- actual log-Kummer correspondence
- actual Θ×μ LGP-link / Theta-link comparison
- actual procession-normalized log-volume
- actual xi-f common container / hull / inclusion
- actual relative trace uniformity / normed space（若原文需要）
- actual NativeCoverTotalSpace / literal IQ carrier（若原文对象需要）

## 8. 状态记录

- 2026-10-28：用户要求读原文构造对象，不许 idle。已抽取 IUT I-IV + Cor312 + Higuchi + Hoshi + Pajo 文本；已按上表派 8 个 agent。
- 中央 watchdog：agent 不本地编译；watchdog 4 workers；status: tmp/xif_watchdog_STATUS.md。
- target_accepted=false；goal active。

## 9. 实际进展（2026-10-28）

- qside 读 IUT III §3 后构造并 append：
  - tmp/sheaf/xif/paper/QPilotLogVolumeFromSource.lean
  - SHA256 7B78716C80C92D8416FB617158EC1B4360C3E2F90162623C3121A9ACAFF2D893
  - actual q-pilot zero locus: qPilotZeroLocus C3 = {C3.q.q} in Completion C3.place.val
  - QPilotLogVolumeObject with actual zeroLocus / logVolume / logMagnitude
  - qPilotLogVolume_eq_log_norm
  - qPilotLogVolume_eq_neg_magnitude
  - qPilotLogMagnitude_eq_neg_log_norm
  - sourceQ_ne_zero_and_norm_lt_one
  - qPilotObject_logVolume_link
- 说明：这是 local completion 上的 actual q-pilot zero locus/log-volume 构造；global realified Frobenioid 版本的 arithmetic divisor 仍需继续按 IUT III 原文构造。
- primespine 读原文后核对：IUT III Step(xi-d/e/f) 与 Higuchi；当前实际 xi-f 缺口是数值桥 P.procession.average ≤ |log q|，以及 hcontains/hnormal/q-log-volume 对象相等；不写重复 wrapper。
- 下一步：继续按 IUT III/IV 原文构造 global q-pilot divisor、Θ-pilot divisor、multiradial representation、log-Kummer correspondence、procession-normalized log-volume；不要只报 missing。

- volumedet 读 IUT IV §1 Theorem 1.10 + IUT III Prop 3.9 后构造并 append：tmp/sheaf/xif/paper/ProcessionNormalizedLogVolumeActual.lean（156 行，SHA256 6f20f62d920b65cd0c2069fb7d49ca9389dbc3b70ead45af07cd979b78c2df0e）。
  Actual construction: ProcessionNormalizedMonoAnalyticLogVolume from actual SignedHullLogActual packet/procession; WeightedValues, local packet log-volumes, procession_values, nonneg local values, weight total one, nonneg weights; ofSignedHull; value is actual weighted average; signedValue = -value.
  Proved: weightTotal_eq_one, value_eq_weighted_sum, value_nonneg, signedValue_nonpos, signedValue_eq_neg, ofSignedHull_value.
  Exact missing remains separate Haar/hull-to-theta comparison paperProcessionNormalizationComparison (already recorded in PaperProcessionNormalization.lean).

- volumedet 原文核对（重要负结果）：IUT III Cor 3.12（iut3.txt 10499-10535, p.173-174）只断言 -|log(Theta)| >= -|log(q)|，没有给出 canonical C6 Haar hull log-volume 与 theta packet/procession average 的等式；Prop 3.9（6955-7040, p.115-117）只定义 packet/procession normalization 为胶囊平均；IUT IV Thm 1.10 只给 upper bound。因此项目内 lemma paperProcessionNormalizationComparison（haarLogVolume = thetaLogVolume/card）是项目内部比较，不是原文定义/等式。
  结论：不能把该等式伪造为 actual comparison；exact missing = actual identification of canonical C6 Haar log-volume with paper procession-normalized Theta hull value，或 actual paper carrier+Haar measure。已记录 blocked，不写 wrapper。
- 下一步改派 volumedet：按 IUT III §3 构造 global realified Frobenioid 上的 q-pilot arithmetic divisor（不是 local zero locus），与现有 qPilot/global 文件对照；能构造多少实际数据写多少。

## 10. 硬规则：对象先于不等式（2026-10-28 goal round 6）

用户补充：很多不等式“没有捷径”，不要试图在不构造原文对象的情况下判定；之前已经做过，这种情况不等式是不可判定的。

执行规则：
- 任何 ≤/≥/等式判定前，必须先构造原文对象：literal carrier、Haar measure、procession average、holomorphic hull、log-Kummer correspondence、Theta-link 等。
- 对象未构造时，不允许写“证明不等式”的 theorem；不允许把项目内部比较（如 paperProcessionNormalizationComparison）当作原文等式。
- 先写 actual object/data；不能构造才 blocked，并给原文页码+精确 missing。
- 不写 fake equality/wrapper。

当前已确认的负结果：IUT III Cor 3.12 只断言 -|log(Theta)| >= -|log(q)|，没有 Haar=hull 等式；IUT IV Thm 1.10 只给 upper bound。因此该等式不能伪造，必须先构造 literal IQ carrier/Haar measure。

任务重排：volumedet literal IQ carrier；qside/kummer global q-pilot；logdescent Θ-pilot；multiradial multiradial representation；iplsheapt log-Kummer；transport Theta-link actual；primespine holomorphic hull。

- iplsheapt 读 IUT III §3 log-Kummer 后构造并 append：tmp/sheaf/xif/paper/LogKummerCorrespondenceFromSource.lean（174 行）。
  actual: actualVerticalLink m := I.fLinkAt 1 m 1 0; actualUnitsActionAt; actualTimesMuActionAt; actualKummerArrow/card/actualOneColumnLogKummer; actualIPLData (actual lower links/kummer/evaluation links and conditional actualIPL arrows).
  exact missing: MissingKummerLayerFamily（actual SourceTimesMuKummerLayer family）和 MissingIPLData（Kummer x-mu layer + evaluation unit portion）。
  下一步：把 MissingKummerLayerFamily 本身作为原文对象构造出来（IUT III §1.5 Kummer theory），不能长期留作 missing。

- qside 原文核对（global q-pilot）：IUT III p.16 q-pilot = C^⊩mod 中 q_v (v∈V_bad) 零 locus 的 arithmetic divisor。当前 Lean 只记录 C^⊩mod 未构造（PrimeStripFrobenioidCards: Card CAT unconstructed）；NativeC3 只有单个 selected native q，不是全局 V_bad 族；IUTIVArithmeticDivisor 是 Finsupp 层，不能冒充。结论：先构造 global realified Frobenioid C^⊩mod（base category/divisor monoid/value functor/realified degree），再构造 q_v 族/zero-locus divisor。已记录 blocked，不写 fake。
- logdescent 读 IUT III Def 3.8/Cor 3.12 后构造并 append：tmp/sheaf/xif/paper/ThetaPilotObjectActual.lean（110 行，SHA256 F72A5B3E...）。
  actual: ThetaPilotImageHullAt v R n（imageSet = possibleThetaPilotImageSet，hull = sourceHolomorphicHull，image_subset_hull，hull_nonempty）；thetaPilotImageHullAt；qPilotPoint_mem_thetaPilotHull；thetaPilotImage_subset_hull。
  明确边界：这是 source value realization，不是 theta values {q_j^2} 零 locus 的 arithmetic divisor；项目缺 source theta functions/line bundle 及全局零除子。
  下一步：构造 actual theta function/line bundle/global zero divisor（IUT II 相关），不能把 value hull 冒充 Θ-pilot divisor。

- qside 构造并 append：tmp/sheaf/xif/paper/GlobalRealifiedFrobenioidActual.lean（129 行，SHA256 4799E7F0...）。
  actual: GlobalBaseCategory := SingleObj Unit; GlobalPrimeIndex := NumberFieldPlace Fmod; GlobalDivisorGroup := Finsupp ... Real; GlobalDivisorMonoid; globalPrimeWeight; globalDegreeFun/globalDegree; globalPrimeDivisor; GlobalRealifiedFrobenioidCarrier + instance. 只是 carrier/degree layer，未构造 full FrobenioidPresentation/FrobenioidAxioms，也未构造 global q_v family/q-pilot divisor on it。
- kummer 构造并 append：tmp/sheaf/xif/paper/QPilotGlobalDivisorOnCarrier.lean（122 行，SHA256 6b65ca1f...）。
  actual: qVCarrierBasePrime; qVZeroLocusPrimeDivisor; qVCarrierInput; qVZeroLocusCarrierFamily; qVZeroLocusCarrierGlobal [Fintype Bad].
  remaining: source bad finiteness, global arithmetic line bundle / C^boxplus_mod q-pilot realization. No inequality.

- volumedet 构造 literal IQ carrier（部分）：tmp/sheaf/xif/paper/LiteralIQCarrierConstructionActual.lean（144 行，SHA256 ddb968fb...）。
  actual: LiteralIQIndex = Fin(j+1) × C3.tensorIndex; LiteralIQAmbient = ArithmeticPacketTensor of actual C3 tensor places; LiteralIQCarrier = arithmeticIQCarrier (Q-span of arithmeticTensorLogRegion); literalIQUnitRegion; literalIQHaar = addHaar; literalIQLocalLogVolume; literalIQProcessionAverage. 
  边界：这是 actual completion-packet IQ construction，不是 literal D-/F-prime-strip capsule 的 realization；缺 D-/F-prime-strip capsule + log-shells + holomorphic hull/Kummer data。
- 下一步 primespine：在 LiteralIQCarrierConstructionActual 上构造 λ·O holomorphic hull / images ⊆ hull 的 actual 数据，先不判不等式。

- iplsheapt 更新：LogKummerCorrespondenceFromSource.lean（201 行）移除 MissingKummerLayerFamily。
  actual: ActualKummerGroup := SelfGroup (I.fPrimeStripAt 1 0); actualCoreSelfLayer/Evaluation（actual kappa-orbit units action）; actualKummerLayerOf via SourceTimesMuKummerLayer.conjugate along I.fLinkAt; actualVerticalKummerLayer; actualKummerArrow; actualVerticalKummerCard; actualOneColumnLogKummer（无 missing layer）; actualUnitsActionAt/actualTimesMuActionAt; actualEvaluationUnitOf; actualIPLData（无 MissingIPLData）。
  边界：这是 actual strip links/units actions 诱导的 reduced x-mu Kummer isomorphism，不是 paper 的完整非阿贝尔 Frobenioid Kummer isomorphism。
- logdescent 核对 IUT II/现存 Example36SourceThetaDivisor：analyticThetaValue、thetaRealValue、thetaQUnit、thetaUnit、thetaUnit_eq_qUnit_pow 实际存在；但 source theta line bundle/global section/theta divisor 仍缺，不写 wrapper。下一步尝试用 actual thetaUnit/thetaQUnit 填 qThetaValues 并从实际数据构造 zero locus。

- qside 构造并 append：tmp/sheaf/xif/paper/GlobalFrobenioidPresentationActual.lean（97 行，SHA256 9C7A2C1F...）。
  actual: globalBaseCat := Cat.of GlobalBaseCategory; globalBaseCat_eq; GlobalFrobenioidPresentationMissing（base category actual，remaining fields exact）；conditional globalFrobenioidPresentationOfMissing : FrobenioidPresentation; GlobalFrobenioidPresentationGap; frobenioidPresentation_nonempty_of_gap。
  missing exact fields: carrier category; isFSM; PreFrobenioid with DivisorialMonoidOn/structureFunctor to ElementaryFrobenioid; carrier/base connectedness; total epimorphicity; seven FrobenioidAxioms groups.
- kummer 构造并 append：tmp/sheaf/xif/paper/QPilotGlobalLineBundleActual.lean（145 行，SHA256 71e41c38...）。
  actual: qPilotGlobalIdeal (product over native V_bad of base Fmod prime ideals); qPilotGlobalLineBundle (inverse fractional ideal O(-D)); QPilotGlobalLineBundleRealization (q_v family, zero-locus prime divisor family, global divisor, global ideal, line bundle, lineBundle_eq).
  missing: source Fintype Bad; identification clause-B F-place q candidates with paper q_v Fmod parameters; (1,0) q-pilot F-prime-strip; log-Kummer representation on 1,circ U_Q; full C^⊩mod FrobenioidPresentation axioms/q-pilot realization.
- 下一步：qside 继续构造 PreFrobenioid/DivisorialMonoidOn/structureFunctor 的 actual 字段；kummer 构造 (1,0) q-pilot F-prime-strip 和 base q descent 的实际数据；volumedet 继续 D-/F-prime-strip capsule/log-shells。

- logdescent 更新：ThetaFunctionLineBundleActual.lean（172 行，SHA256 D91BFBC5...）用 actual thetaUnit/thetaQUnit 填充 qThetaValues，构造 ActualQThetaValueData（value j = thetaUnit t j.1, pow_eq = qUnit^(gaussExponent)）、actualQThetaValueZeroLocus，并证明 zeroLocus_empty。明确这不是 source theta divisor；remaining ThetaFunctionLineBundleMissing: curveLineBundle/thetaObject/thetaFunction/thetaGlobalSection/thetaZeroDivisorEq/qPilotDivisor/thetaLinkIdentification。
- iplsheapt：LogKummerCorrespondenceFromSource.lean 注释修好，中央 watchdog EXIT=0。
- qside：GlobalRealifiedFrobenioidActual.lean map_mul 证明修好（Finsupp.sum_add_index + ring），已入队。

- primespine 构造并 append：tmp/sheaf/xif/paper/LiteralIQHolomorphicHullActual.lean。
  actual: hullUnitRegion := literalIQUnitRegion; hullNonzeroScalings; literalIQScaledRegion lam O; literalIQCandidateHulls P; literalIQHolomorphicHull P（Remark 3.9.5 least intersection）; literalIQImage_subset_holomorphicHull; mem_literalIQCandidateHulls_iff。
  missing: MissingLiteralIQCapsuleLogShell; MissingLiteralIQHolomorphicHullData; LiteralIQHolomorphicHullMissing（D-/F-prime-strip capsule/log-shells、possible images n,∘U_{j,vQ}⊆LiteralIQAmbient、compactness、Kummer/log-Kummer data）。

- transport 构造并 append：tmp/sheaf/xif/paper/ThetaLinkKummerObjectsActual.lean（268 行，SHA256 999160E0...）。
  actual: xMuQuotientEquiv（FPrimeStripEquiv.isoMon -> torsion quotient）; xMuQuotientEquiv_equivariant; kappaLowerOfStripEquiv（TimesMuKummer.Isomorphism, invariantImage）; pairDatumOfStripEquiv（sourceUnits/actions/factors/kappaUpper/kappaLower）; layerOfStripEquiv; kummerArrowOfStripEquiv; evaluationUnitPortionOfStripEquiv; evaluationArrowOfStripEquiv; actualKummerArrowS00S01/actualEvaluationArrowS01S11 via I.linkAt.
  exact missing: PairGroup profinite topology (MissingPairTopology); common topological G on four corners; IPL factorization equality/KummerEvaluationSquare commute (Theorem 3.11(iii)(a)-(d)/Remark 3.11.1(iii)).
- volumedet 构造并 append：tmp/sheaf/xif/paper/PrimeStripLogShellActual.lean（116 行，SHA256 31e429d4...）。
  actual: ActualFPrimeStrip := I.primeStripAt 1 0; ActualDPrimeStrip := I.dPrimeStripAt 1 0; ActualDFPrimeStripCapsule; c3LogShellPlace; actualC3LogShellDatum; actualC3LogShell; actualC3LogShell_eq_integralLogShell。
  missing: PrimeStripC3PlaceComparison（indexEquiv V ≃ C3.tensorIndex + stripPlace : V -> FinitePlaceAtPrime Fmod C3.p + stripPlace_eq）。

- kummer 构造并 append：tmp/sheaf/xif/paper/QPilotFTimesMuPrimeStripActual.lean（113 行，SHA256 2f4f72f2...）。
  actual: qPilotFTimesMuPrimeStripAt10 I := SourceFTimesMuPrimeStrip.canonical (I.fPrimeStripAt 1 0); projections underlying F-prime-strip/timesMu; QVBaseDescentFamily (exact V_bad-indexed descent data); qVBaseFamily; MissingQVBaseDescentFamily.
  missing: identification with paper (1,0) q-pilot F^⊩▶×μ-prime-strip; V_bad base q descent family (extension completion -> base completion; repo only reverse completionMap); clause-B q candidates vs paper Fmod q_v; full F^⊩▶×μ prime-strip/global realified Frobenioid/log-Kummer on 1,∘U_Q.
- volumedet 构造并 append：tmp/sheaf/xif/paper/PrimeStripLogShellActual.lean（116 行，SHA256 31e429d4...）。
  actual: ActualFPrimeStrip/ActualDPrimeStrip/ActualDFPrimeStripCapsule; c3LogShellPlace; actualC3LogShellDatum; actualC3LogShell; equality with integralLogShell.
  missing: PrimeStripC3PlaceComparison (indexEquiv V ≃ C3.tensorIndex, stripPlace, pointwise agreement).

- volumedet 原文核对：IUT III Prop 3.2 给 D-prime-strip capsule/log-shells I(D_v)，但 source extract 无 V ≃ C3.tensorIndex 映射，无 stripPlace 与 C3.tensorPlaces 等式；Lean 中 I.primeStripAt 的 V 与 C3.tensorIndex 独立，卡数相等构造是任意，不可 paper-faithful。PrimeStripC3PlaceComparison 仍为 exact missing。
  改派：先构造不依赖 V≃C3.tensorIndex 的 actual C3 tensor packet of log-shells（用 actualC3LogShell + C3.tensorIndex/tensorPlaces/tensorTuple），这是 Prop 3.2(ii) 的 tensor packet 对象。

- primespine 构造并 append：tmp/sheaf/xif/paper/LiteralIQPossibleImagesActual.lean。
  actual: literalIQUnitRegion_compact（isCompact_arithmeticTensorLogRegion）; ThetaPilotImageIndex := ThetaPilotCarrier l × SignedLabel l.value; imageSetOfMap（从 donor map）; MissingLiteralIQThetaPilotImageMap / MissingLiteralIQImageCompactness / MissingLiteralIQImageIdentification / LiteralIQPossibleImagesMissing。
  missing: D-/F-prime-strip capsule/log-shell; Theta-pilot image map to literalIQUnitRegion; 1,∘U compactness; Kummer isomorphisms.

- transport 构造并 append：tmp/sheaf/xif/paper/ThetaLinkProfiniteTopologyActual.lean（180 行，SHA256 1994B8CC...）。
  actual: PairProfiniteGroup := profiniteCompletionOfGroup (GrpCat.of (PairGroup upper lower))（有限 index normal quotients inverse limit）; Group/TopologicalSpace/CompactSpace/TotallyDisconnectedSpace 实例; pairProfiniteEta; pairProfiniteFactorUpper/Lower; CommonThetaLinkGroup := completion of fourfold product (S00,S01,S10,S11) Pi groups; 其实例; commonThetaLinkEta; fourCornerToS00S01/S01S11/S10S11。
  missing: CommonThetaLinkGroup 上 actual SourceTimesMuKummerLayer / SourceEvaluationUnitPortion（G-equivariant Kummer iso + open subgroup invariant-image law）; KummerEvaluationSquare commutes; IPL factorization equality。

- volumedet 构造并 append：tmp/sheaf/xif/paper/C3LogShellTensorPacketActual.lean（127 行，SHA256 c8de2662...）。
  actual: C3LogShellFiber i = CommonPrimeCompletion (C3.tensorPlaces i (C3.tensorTuple i)); C3LogShellTensorBlock = ArithmeticTensorTupleBlock; actualC3LogShellTensorRegion = tensorIntegralRegion of actualC3LogShell; compactness from isCompact_integralLogShell; actualC3LogShellTensorIQ = Q-span; actualC3LogShellTensorHaar = addHaar; actualC3LogShellTensorLogVolume; ActualC3LogShellTensorPacket. 
  missing remains V≃C3.tensorIndex/stripPlace (PrimeStripC3PlaceComparison); tensor packet itself actual.

- transport 构造并 append：tmp/sheaf/xif/paper/ThetaLinkCommonKummerActual.lean（289 行，SHA256 35E4ACD6...）。
  actual: CommonG 四角 Pi 乘积 topologized by profinite completion; commonFactorS00/S01/S10/S11; factorLowerOfEquiv; xMuQuotientEquiv_equivariant_factors; kappaLowerOfFactors（TimesMuKummer.Isomorphism + open subgroup invariant-image）; pairDatumOfFactors; layerOfFactors; evalPortionOfFactors; actualUpperEvaluation/actualLeftKummer/actualRightKummer/actualLowerUnitPortion（actual I.linkAt）; actualKummerEvaluation via SourceKummerEvaluationSquare.ofThreeLegs。
  remaining: MissingIPLFactorization（actual inputLink = composite）；下一项直接构造该 equality，而不是只记录。

- logdescent 构造并 append：tmp/sheaf/xif/paper/ThetaLineBundleAnalyticActual.lean（114 行，SHA256 0F37787F...）。
  actual: AnalyticThetaLineBundle (base/total/projection/trivialization/thetaSection/zeroSection/zeroLocus); analyticThetaLineBundle (base=AnalyticThetaCarrier,total=carrier×ℂ,thetaSection t=(t,analyticThetaValue t),zeroSection); thetaSectionNeZeroSection（analyticThetaValue_ne_zero）; zeroLocus_empty; thetaSection_proj; section_fst。
  边界：actual analytic q-disc trivialized line bundle/theta section，不是 source curve/étale theta line bundle；下一步构造 automorphy factor/source line bundle。
- iplsheapt 构造并 append：tmp/sheaf/xif/paper/KummerEvaluationSquareActual.lean（83 行）。
  actualKummerEvaluationSquare; actualKummerEvaluationSquare_commutes; actualIPLOfSquare; actualIPLOfSquare_inputLink_eq_composite (inputLink=composite)。
- transport 更新并 append：ThetaLinkCommonKummerActual.lean（330 行，SHA256 9805910A...）。
  actualKummerS00S01/actualEvaluationS01S11/actualIPL; inputLink=(I.linkAt 1 0 1 1).primeStripEquiv; factorization via I.linkAt_trans/symm; actualKummerEvaluation_commutes。

- qside 构造并 append：tmp/sheaf/xif/paper/GlobalFrobenioidPresentationActual.lean（76 行，SHA256 EDFC5E5D...）。
  actual: globalFrobenioidPresentationActual := Example36.SourceModelBackend.numberFieldFrobenioidPresentation K (actual global model Frobenioid, III Example 3.6(ii)); globalFrobenioidBaseActual; globalFrobenioidCarrierActual; globalFrobenioidPreActual; globalFrobenioidDivisorMonoidActual (DivisorialMonoidOn BottomBase BottomFSM); globalFrobenioidStructureFunctorActual; globalFrobenioidAxiomsActual; connectedness/total epimorphicity; globalEffectiveDivisorMonoidActual. 不是 Missing wrapper。
  下一步：把 kummer 的 q_v zero-locus divisor 实际落到这个 presentation 的 divisor monoid 上，构造 q-pilot object。
