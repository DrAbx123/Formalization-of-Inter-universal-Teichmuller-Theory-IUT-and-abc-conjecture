# [ExpEst] Cor 5.2 显式不等式 → 仓库 Lean 形状对照（A488，只读审计）

生成: 2026-11-11 05:15 左右 snapshot。论文来源: papers/motizuki_corpus/text/Explicit estimates in IUTeich.txt（Cor 5.2: L1794-1894；Thm 5.3: L2203-2237；Thm 5.4: L2426-2443；Prop 2.2: L1078-1123；Thm 1.1/摘要: L60-134）。
方法: 只读核对文件/oleans/声明签名；未修改任何文件、未改队列、未碰 watchdog。

## 0. 状态快照（oleans）

| 资产 | 文件 | olean | 角色 |
|---|---|---|---|
| Cor312ToABCCards | LeanFormal/IUT/ABCBridge/Bridge/Cor312ToABCCards.lean | ✔ | 卡片/Thm5.4 形状/Prop2.2 obligation |
| ElementaryEstimates | LeanFormal/IUT/IUTIV/Estimates/ElementaryEstimates.lean | ✔ | Class A e1-e6 |
| Section1 | LeanFormal/IUT/IUTIV/Estimates/Section1.lean | ✔ | Prop 1.7 加权平均 |
| Section2 | LeanFormal/IUT/IUTIV/Estimates/Section2.lean | ✔ | Prop 2.1/1.6/Chebyshev 估计 |
| ArithmeticDivisorDegree | LeanFormal/IUT/IUTIV/Estimates/ArithmeticDivisorDegree.lean | ✔ | 归一化次数/算术除子层 |
| DifferentTowerEstimate / DifferentTameEquality / DifferentDegreeUpperBound | IUTIV/Estimates/ | ✔ | Prop 1.3 归一化 different 估计 |
| ExpEst00/01/02 + S3175 | tmp/sheaf/xif/paper/ | ✔ | ExpEst ledger/Class B paper-input 登记 |
| ChebyshevExplicit (LANA) | tmp/dsh-oct6-openai-math-survey-20261016/repos/lana/iut/iut-main/Iut/Implication/ChebyshevExplicit.lean | ✘(外部仓库,未入湖构建) | Chebyshev/PNT 显式上界（可移植参考） |
| ChebyshevSixfoldProbe | tmp/chebyshev-sixfold-20261017/ChebyshevSixfoldProbe.lean | ✘(superseded) | 旧 sixfold 证草稿（已被 Section2 覆盖） |
| Cor312ToABCCards.splitted | tmp/cor312-to-abc-cards-20261016/Cor312ToABCCards.splitted.lean | ✘ | 树文件的拆分副本（历史） |

## 1. Cor 5.2 逐项映射（论文条目 → Lean 形状 → 已有证明/缺口）

| # | Cor 5.2 条目（行号） | 仓库 Lean 现状（file:decl / 无） | 已有证明/登记 | 缺口 |
|---|---|---|---|---|
| 1 | X=P1_Q, D={0,1,∞}, λ-line/Legendre 形式, (Mell)_Q, U_X=X\D (L1794-1802) | ABCBridge/Geometry/Legendre{JFunctionDivisor,ParameterIsomorphisms,ProjectiveMap}.lean（green）；IUTIV/Estimates/ArithmeticDivisorDegree.lean: IUTIVPlace, IUTIVArithmeticDivisor（green） | Legendre/曲线层与算术除子层已有；moduli stack (Mell)_Q、U_X(Q) 点集未定义 | (Mell)_Q、U_X(Q)、U_X(Q)≤d、U_X(Q)mcx 无 typed |
| 2 | κ∈(0,1], K_V(Q)^arc(κ) compactly bounded (Def 1.13, L1803-1806) | 无 | — | 无 typed（紧性基建有，但 K_V/K 层无） |
| 3 | log(q∀(−)): 归一化 q-参数除子的度 (L1809-1815) | 部分: ArithmeticDivisorDegree.degLinearMap/ndegLinearMap/ndeg_apply（green）；ABCBridge Height/logHeight₁、arithmeticWeight | 归一化次数层已有 | q-除子对象及其 log-deg 函数无 typed |
| 4 | U_X(Q)≤d, U_X(Q)mcx, mono-complex field (Def 1.2, L1816-1819) | Mathlib 有 NumberField/IsTotallyComplex；仓库无 U_X 子集定义 | — | 无 typed |
| 5 | δ := 2^12·3^3·5·d = 552960·d (L1820) | 无（LANA Iut/Tower/RamIdx.lean: two_le_log_552960 只涉及 log 552960 不等式的另一用途） | — | G1: δ 与 552960 常数无 Lean 定义 |
| 6 | κ_log := 5·10^-13 − 6.01·10^-15·log κ (L1821-1824) | 无 | — | G1: κ_log 无 Lean 定义 |
| 7 | h_d(ε) 分段: 3.4e30·ε^(-166/81) (d=1); 6e31·ε^(-174/85) (d=2); 3.4e30·ε^(-166/81)·d^5 (d≥3) (L1825-1837) | 无（Cor312ToABCCards.explicitEstimatesThm54ExpConstant 只含 Thm5.4 的 exp(1.7e30·ε^(-166/81))，不是 h_d） | — | G1: h_d 无 Lean 定义 |
| 8 | 有限例外集 Exc_{κ,d,ε} / Exc^mcx_{d,ε}，且 log(q∀) ≤ max{κ_log, h_d(ε)} (L1837-1848) | 无 typed；仅在 Cor312ToABCCards 卡片字符串中出现（step-1/2 cards） | — | G1: 例外集与界无 Lean 定义 |
| 9 | E_F/F_mod/F_tpd(tripodal)/(3·5)-torsion, F=F_mod(√-1,E[2·3·5]) (L1849-1875) | 无 typed（"tripodal" 仅出现在 Cor312ToABCCards/Section1/Section2 的说明文字） | — | G4: 字段塔与 3·5-torsion 条件无 Lean 定义 |
| 10 | (C1): (10^15·d ≤) log(q∀)^(1/2) ≤ l ≤ 1.464·δ·log(q∀)^(1/2)·log(1.45·δ·log(q∀)) (L1883-1888) | 无 typed；Cor312ToABCCards step-1 card 字符串转述（l ≥ 10^15 等）；树侧只有 SourceNativeInitialThetaData/PrimeGeFive 的 l≥5 约束 | — | G5: 常数 10^15、1.464、1.45、δ 的组合界无 Lean |
| 11 | (C2): (1/6)·log(q∀) ≤ (1+ε)·(log-diff_X(x_E)+log-cond_D(x_E)) (L1889-1894) | 部分对象层: DifferentTowerEstimate.iutIVProp13i_normalizedDifferent_ge、DifferentTameEquality.iutIVProp13i_normalizedDifferent_eq_of_tame、DifferentDegreeUpperBound.iutIVProp13ii_normalizedDifferent_le（green）；log-diff_X/log-cond_D 函数本身未定义 | 归一化 different 的显式估计已有一部分 | G6: log-diff_X/log-cond_D 及 (C2) 不等式无 typed |
| 12 | Prop 2.2 (i): x ≥ 5e20 ⇒ π(x) ≤ 1.022·x/log x (L1092-1095) | ExpEst02ElementaryEstimatesActual.ExpEstPNTUpperPaperInput（Class B 登记，形如 n ≤ 4·p_n/(3·log p_n)，常数比论文弱）；LANA ChebyshevExplicit.primeCountingHyp_holds: π ≤ 3x/(2·log x)（外部，未入湖构建） | 树侧有更弱但已证: Section2.iutIVProp16_primeCounting_le_four_thirds_eventually（π ≤ 4η/(3log η)） | G9: 1.022 常数未证（Class B） |
| 13 | Prop 2.2 (ii): x ≥ 10^15 ⇒ |θ(x)−x| ≤ 0.00071·x；且对有限素集 A 存在 p∉A, p ≤ 1.00072·(θ_A+10^15) (L1096-1107) | ExpEst02.ExpEstChebyshevThetaPaperInput（仅 θ ≤ C·η 的弱形式登记）；Section2 已证: iutIVProp21ii_theta_ge_two_thirds_eventually、iutIVProp21ii_theta_le_four_thirds_eventually、iutIVProp21ii_theta_two_sided_eventually、theta_sixfold_window_le、theta_le_thirteen_tenths_mul_add、iutIVProp21ii_exists_prime_notMem_le_two_mul | 有已证但常数 2/3、4/3、13/10（非 0.00071 级） | G9: 0.00071/1.00072 常数未证（Class B） |
| 14 | Thm 5.3(i): (1/6)h_non(j(E_{a,b,c})) ≤ max{(1/d)(1+ε)log(Δ_L·rad_L), (1/6)h_d(ε)} (L2225-2232) | 无 typed；cor312ToABCChainStepExcToBDBoundCard 以字符串记录（machineStatus 列 missing） | — | G7: h_non、H_L、Δ_L、rad_L、h_d(ε) 与 Thm5.3 语句均无 Lean |
| 15 | Thm 5.3(ii): H_L ≤ 2^{5d/2}·max{exp(d·h_d(ε)/4), (Δ_L·rad_L)^{3(1+ε)/2}} (L2233-2237) | 同上（card step-2 字符串） | — | G7 同上 |
| 16 | Thm 5.4: |abc| ≤ 24·max{exp(1.7e30·ε^(-166/81)), rad(abc)^{3(1+ε)}} ≤ 24·exp(...)·rad^{3(1+ε)} (L2426-2443) | **typed statement 已有**: Cor312ToABCCards.explicitEstimatesThm54Shape（Prop，无证明）；explicitEstimatesThm54ExpConstant / explicitEstimatesThm54MaxBound（常数/边界定义，green）；explicitEstimatesThm54ShapeCard（card, pending） | typed shape 与论文逐符号一致（含 |abc|=(a*b*c).natAbs, rad(abc)=radical，双不等式链） | G8: proof 无；Claims 5.4A-C、cube step 无 |
| 17 | Thm 5.1 / Thm 1.1（Cor 3.12 输入、log-q 界）(L60-134, L1630-1739) | Cor312ToABCCards.cor312ToABCChainStepCor312ToC2Card 字符串；树侧 Cor 3.12 链的 typed 结果（Cor312Conclusion 组装）存在（如 ShehddFourTriangleAssemblyActual 等 green） | Cor312 组装 rung 有 typed 结果（本卡 step-1 的 IUT III 侧） | log(q∀) 上界与 C_Θ 常数层无 typed |

## 2. 已证可复用资产（green，建议 mainline/stepxi 直接引用）

- Class A 初等估计（ElementaryEstimates.lean, green）: iutIVThm110_e1_arithmeticMean (L76), _e2_arithmeticMeanSquares (L88), _e3_card_GL2_modPrime (L101), _e4_card_GL2_smallPrimes (L121), _e5_adjoin_sqrtNegOne_finrank_le_two (L128), _e6_logBounds (L146), sum_Icc_one_cast (L51), sum_Icc_one_sq_cast (L63)。
- Chebyshev/PNT 型已证（Section2.lean, green）: iutIVProp21i_log_le_self (L111); iutIVProp21ii_theta_ge_two_thirds_eventually (L124) 与 iutIVProp21ii_theta_two_sided_eventually (L393)（常数忠实 (2/3)x ≤ θ ≤ (4/3)x）; theta_sixfold_window_le (L325); theta_le_thirteen_tenths_mul_add (L353); iutIVProp21ii_theta_le_four_thirds_eventually (L386); iutIVProp16_primeCounting_le_four_thirds_eventually (L409); iutIVProp16_index_le_four_thirds_nthPrime (L436); iutIVProp21ii_prime_notMem_of_theta_lower (L190); iutIVProp21ii_exists_prime_notMem_le_two_mul (L225)。
- 归一化次数/算术除子（ArithmeticDivisorDegree.lean, green）: IUTIVPlace, IUTIVArithmeticDivisor, weight (L79), localDegree (L97), degLinearMap (L109), ndegLinearMap (L129), ndeg_apply (L135), eDegree (L166), eDegreeUnnormalized (L172); 配套 StepVDivisorAverage.eDegreeUnnormalized_eq_weightedAverage (L46)。
- 归一化 different 估计（green）: DifferentTowerEstimate.iutIVProp13i_normalizedDifferent_ge (L92); DifferentTameEquality.iutIVProp13i_normalizedDifferent_eq_of_tame (L170); DifferentDegreeUpperBound.iutIVProp13ii_normalizedDifferent_le (L184); ArchimedeanTensorMetric（复数 tensor 范数/内积层，green）。
- 加权平均族（green）: Section1.iutIVProp17 (L199) 与 iutIVProp17_weightedTupleSum/_betaTupleSum/_middle/_value (L125-186); StepVDistinguishedSlotAverage.weightedAverage_le_of_distinguishedBound (L87); StepVProcessionAverage.weightedAverage_le_collectionBound (L190)。
- ABC 接口层（green）: ABCBridge/Bridge/IUTToABC.lean: abcConjecture_iff_abcArithmeticWeightHeightBound; ABCBridge/Arithmetic/ABCHeightArithmeticWeightComparison.lean: ABCHeightWeightAdditiveBoundV2, abcHeightArithmeticWeightComparison; Cor312ToABCCards.cor312ToABCTargetShape_iff_abcConjecture (green, cor312ToABCTargetShape 与 ABCConjecture 的等价)。

## 3. 登记型/无证明资产（不能计为已证）

- Cor312ToABCCards.lean（green 编译，但内容为卡片/字符串）: cor312ToABCChainStepCor312ToC2Card (L80, pending), cor312ToABCChainStepExcToBDBoundCard (L127, pending), cor312ToABCChainStepMonoComplexToSzpiroCard (L175, pending), cor312ToABCChainStepInterfaceToABCCard (L209, interface), explicitEstimatesThm54ShapeCard (L288, pending); explicitEstimatesProp22Obligation (L359, pending: 只登记 Prop 2.2 常数，明确写 no explicit PNT bound formalized)。
- ExpEst00NamingActual.s3135ExpEstNaming（interface）; ExpEst01StatementLedgerActual.s3135ExpEstStatementLedger（interface, Class A/B 清单）; ExpEst02ElementaryEstimatesActual: s3135ExpEstClassAIndex (8 条), s3135ExpEstClassBIndex (3 条), ExpEstPNTUpperPaperInput / ExpEstPrimeReciprocalSumPaperInput / ExpEstChebyshevThetaPaperInput（Class B paper-input 定义，无证明；且常数形式比论文 Prop 2.2 弱，勿当作论文形式化）; S3175ExpEstAuditActual.S3175ExpEstAudit（audit 记录）。
- LANA ChebyshevExplicit.lean（外部仓库, olean=false, 未入本湖构建）: ChebyshevHyp (L53), ChebyshevUpperHyp (L59), PrimeCountingHyp (L64), chebyshevBound_of_upper (L198), chebyshevBoundExplicit (L207), chebyshevHyp_holds (L220), primeCountingHyp_of_theta_le (L229), primeCountingHyp_holds (L255), two_thirds_mul_le_theta (L94, x≥10^12 显式下界), log_four_lt (L163)。可移植参考，但常数 3/2、log4 级，非 1.022/0.00071。

## 4. 缺口清单（G1-G9，按 Cor 5.2 顺序）

- **G1** δ、κ_log、h_d(ε)、Exc 集合及 log(q∀) ≤ max{κ_log,h_d} 界：无 Lean 定义（仅卡片字符串）。
- **G2** log(q∀(−)) 的除子/度对象：归一化 deg/ndeg 层已有（ArithmeticDivisorDegree），缺 q-参数除子特化。
- **G3** (Mell)_Q、U_X、U_X(Q)≤d、U_X(Q)mcx、κ-compact K_V：无 typed。
- **G4** F_mod/F_tpd(tripodal)/(3·5)-torsion 字段塔：无 typed。
- **G5** (C1) 的 10^15/1.464/1.45/δ 组合界：无 Lean。
- **G6** log-diff_X/log-cond_D 及 (C2) 不等式：object 层只有 different 估计与 ndeg，缺 U_X 上函数定义与不等式。
- **G7** Thm 5.3(i)/(ii) 的 typed 语句与对象 h_non/H_L/Δ_L/rad_L/h_tor_non：全部缺。
- **G8** Thm 5.4 的证明（Claims 5.4A-C、Q-specialization、cube step）：缺；typed shape 已有但 no proof。
- **G9** Prop 2.2 的 1.022 / 0.00071 / 1.00072 显式常数：未证（Class B）；现有已证 Chebyshev 界只到 2/3、4/3、13/10，LANA 外部到 3/2（π）与 log4（θ 上界）。

## 5. 重复/失效资产

- tmp/chebyshev-sixfold-20261017/ChebyshevSixfoldProbe.lean: 旧 sixfold/1.3x/4/3 证明草稿，内容已被树文件 Section2.lean 覆盖（Section2 green, 该 probe 无 olean 且不在队列）→ 不重复使用，canonical=Section2。
- tmp/cor312-to-abc-cards-20261016/Cor312ToABCCards.splitted.lean 与 probe_shapes.lean: 树文件 Cor312ToABCCards.lean 的拆分/探针副本（均无 olean）→ canonical=树文件。
- ExpEst02 的三个 PaperInput 定义是比论文 Prop 2.2 更弱的抽象形式（4p/3log p、θ≤Cη、Σ≤4η/3log η），不得在文档/报告中称为 Prop 2.2 的形式化。

## 6. 给 mainline / stepxi 的建议（不新增文件）

- stepxi（Stage5 数值）：可直接复用 Section2 + ElementaryEstimates 的已证估计作为“弱常数”工具层；若要论文 1.022/0.00071 常数，需新增 explicit PNT/差估计（Class B，当前无 Lean；LANA ChebyshevExplicit 可移植但也要适配常数）。
- mainline（Cor312-to-ABC 卡片链）：卡片 step-1/2 的 machineStatus 已列出缺口；建议下一步把 (C2) 的 object 层拆成可构造小块：复用 ArithmeticDivisorDegree + Different* 估计，先定义 U_X 上的 log-diff/log-cond 与 q-除子 log-deg，再陈述 (C2)。
- 优先级：P1 定义 G1 常数/Exc 与 G6 对象层（可复用现有 green 资产）；P2 写 Thm 5.3 typed 语句（G7）；P3 证明 Thm 5.4（G8，最难，需 Claims 5.4A-C）；G9 独立（显式 PNT，Class B）。
- 复用清单（file:decl）见 §2；切勿把 §3 的登记型资产计为已证，也勿把 ChebyshevSixfoldProbe/splitted 副本当 canonical。

本记录为只读审计输出；未修改代码、未新增/修改队列条目、未碰 watchdog。

## 7. ExpEst02 / ExpEst01 与论文逐项对照（own-file，A489 扩展）

### 7.1 Class A（tree 已证，可直接复用）

| ExpEst ledger | 对应 Lean 声明/文件 | 论文对应 | 强度/常数 | 状态 |
|---|---|---|---|---|
| e1 arithmeticMean | ElementaryEstimates.iutIVThm110_e1_arithmeticMean（L76） | IUT IV Thm 1.10 证明内 (E1)（L1387-1392）；[ExpEst] §5 Thm 5.1 证明的类似初等核算 | (1/n)Σm = (n+1)/2，精确 | PROVED（green olean） |
| e2 arithmeticMeanSquares | iutIVThm110_e2_arithmeticMeanSquares（L88） | 同上 (E2)（L1393-1398） | (1/n)Σm² = (2n+1)(n+1)/6，精确 | PROVED |
| e3 card GL2 mod prime | iutIVThm110_e3_card_GL2_modPrime（L101） | (E3)（L1402-1403） | |GL2(F_p)| = p(p+1)(p−1)²，精确 | PROVED |
| e4 card GL2 small primes | iutIVThm110_e4_card_GL2_smallPrimes（L121） | (E4)（L1404-1405） | p=2,3,5 数值核算，精确 | PROVED |
| e5 adjoin sqrt(−1) | iutIVThm110_e5_adjoin_sqrtNegOne_finrank_le_two（L128） | (E5)（L1406） | [F(√−1):F] ≤ 2，精确 | PROVED |
| e6 log bounds | iutIVThm110_e6_logBounds（L146） | (E6)（L1407） | 0≤log2≤1, 1≤log3≤logπ≤log5≤2 | PROVED |
| sum lemmas | sum_Icc_one_cast（L51）, sum_Icc_one_sq_cast（L63） | (E1)/(E2) 求和工具 | 精确 | PROVED |

说明: 这些是 **IUT IV Thm 1.10 的初等估计**（[ExpEst] 论文 §5 证明中同型但不同文），不是 [ExpEst] 论文本身的命题；可复用为 Thm 5.1/5.3 的数值工具层，但不能称作 [ExpEst] 的形式化。

### 7.2 Class B（paper-input 登记）与论文 Prop 2.2 / IUT IV Prop 1.6 的关系

| ExpEst02 def | 声明形状 | 论文/树内对应 | 实际强度 | 当前可证性 | 审计结论 |
|---|---|---|---|---|---|
| ExpEstPNTUpperPaperInput (B1) | ∃n0, ∀n≥n0, n ≤ 4·p_n/(3·log p_n)（p: Nat→Nat 抽象素数枚举） | [ExpEst] Prop 2.2(i) 的弱形式；IUT IV Prop 1.6（Section1.lean:23；论文 L913-926） | 4/3 常数（弱于论文 1.022） | **已被树内 green 定理覆盖**: Section2.iutIVProp16_index_le_four_thirds_nthPrime : ∃n0, ∀n≥n0, (n+1:ℝ) ≤ 4·(nth Prime n)/(3·log(nth Prime n))；由 n ≤ n+1 得 B1（取 p = Nat.nth Nat.Prime） | 登记过时（stale Class B）：B1 已可由 green 定理直接推出；论文 1.022 常数仍缺。命名/形式差异: B1 用任意 p，需限定 p 为素数枚举才与论文对应 |
| ExpEstPrimeReciprocalSumPaperInput (B2) | ∃ηprm>0, ∀η≥ηprm, primeSum η ≤ 4η/(3·log η)（primeSum 抽象） | [ExpEst] Prop 2.2 弱形式 / IUT IV Prop 1.6 素数计数形；论文 L1098-1106（π/θ_A 与素数存在） | 4/3 常数（弱于论文 1.022） | **已被树内 green 定理覆盖**: Section2.iutIVProp16_primeCounting_le_four_thirds_eventually : ∃η0>0, ∀η≥η0, (Nat.primeCounting ⌊η⌋₊ : ℝ) ≤ 4η/(3 log η)；取 primeSum η := (Nat.primeCounting ⌊η⌋₊ : ℝ) 即 B2 | 登记过时；**命名与内容不符**: "reciprocal primes sum" 若取 Σ_{p≤η} 1/p 则界应为 log log η 型，4η/(3logη) 只对 π(η) 成立——owner 应澄清/改名 |
| ExpEstChebyshevThetaPaperInput (B3) | ∃η0 C>0, ∀η≥η0, θ(η) ≤ C·η（θ 抽象） | [ExpEst] Prop 2.2(ii) 的弱形式；IUT IV §2 Chebyshev θ 界（Section2.lean:16-19） | C 任意（弱于论文 |θ−x|≤0.00071x） | **已被树内 green 定理覆盖**: Section2.iutIVProp21ii_theta_le_four_thirds_eventually : ∃ξ≥5, ∀x≥ξ, Chebyshev.theta x ≤ 4/3·x（C=4/3, ξ=9000）；取 theta := Chebyshev.theta 即 B3 | 登记过时；论文 0.00071 常数仍缺 |

### 7.3 真正剩余的论文常数（[ExpEst] Prop 2.2）

- Prop 2.2(i): π(x) ≤ 1.022·x/log x（x ≥ 5·10^20）——未证（树内 4/3 弱形式已证；LANA ChebyshevExplicit 外部给 π ≤ 3x/(2log x)=1.5 级弱于 1.022? 1.5>1.022，仍更弱）。
- Prop 2.2(ii): |θ(x) − x| ≤ 0.00071·x（x ≥ 10^15）——未证（树内只有 (2/3)x ≤ θ ≤ (4/3)x 的粗界）。
- Prop 2.2 素数存在形式: p ≤ 1.00072·(θ_A + 10^15) 且 p ∉ A——未证（树内有 Section2.iutIVProp21ii_exists_prime_notMem_le_two_mul: p ≤ 2(θ_A + ξ) 型的弱版本）。

**审计建议（待 owner）**: ExpEst01/ExpEst02 的 ledger 文本（"not proved; Mathlib has PNT asymptotics only"）在 Section2 green 后已过时；B1/B2/B3 应从 Class B 降级为 "tree-covered weak forms"，真正 Class B 只剩 1.022/0.00071/1.00072 三个 sharp 常数。

## 8. Cor312ToABCCards 逐卡对照（own-file，A489 扩展）

| card | 源引用（as written） | 转录结论 | 与论文核对 | machineStatus 与现状核对 | typed 资产 | status |
|---|---|---|---|---|---|---|
| step-1 cor312ToABCChainStepCor312ToC2Card (L80) | Thm5.1 lines 1630-1662/1717/1718-1731/1733-1739; C2 lines 1889-1894; Def4.1 line 1318; IUTchIV Thm1.10 line 1255 | (1/6)log q ≤ (1+20 d_mod/l)(log d_Ftpd + log f_Ftpd) + 4.0881 e*_mod l ≤ (1+20 d_mod/l)(log d_F + log f_F) + 4.0881 e*_mod l | ✔ 与论文 L1733-1739 逐字一致（4.0881、20 d_mod/l、e*_mod） | present 列表: IQHullLogVolumeInterface/hull_logVolume_lt_top + Cor312ToABCBridgeInterface 条件组装 ✔；missing 列表: μ6-initial Θ-data/C_Θ 常数层/算术除子层——**部分过时**（ArithmeticDivisorDegree 已 green） | Cor312ToABCBridgeInterface（条件组装） | pending |
| step-2 cor312ToABCChainStepExcToBDBoundCard (L127) | Cor5.2 lines 1794-1894; Exc lines 1837-1855; C2 lines 1889-1894; Prop2.2 lines 1078-1123; Thm5.3 lines 2203-2237 语句(i) 2225-2232 证明锚 2238-2242; Remark1.10.1 lines 885-896 | (1/6)h_non(j(E_{a,b,c})) ≤ max{(1/d)(1+ε)log(Δ_L·rad_L), (1/6)h_d(ε)} ≤ (1/d)(1+ε)log(Δ_L·rad_L) + (1/6)h_d(ε) | ✔ 与论文 L2225-2232 一致；hypotheses 中 π(x)≤1.022x/logx (x≥5·10^20) 与 |θ−x|≤0.00071x (x≥10^15) 与论文 Prop 2.2 一致 | missing 列表: moduli stack/compactly bounded K_V/例外集/log-diff/log-cond/h_non/H_L/Δ_L/rad_L/显式 PNT——**显式 PNT 一项过时**（Section2 green 有 4/3 弱形式；sharp 常数仍缺） | 无 typed | pending |
| step-3 cor312ToABCChainStepMonoComplexToSzpiroCard (L175) | Thm5.4 lines 2426-2443; proof lines 2444-2513（Claims 5.4A-C 2445-2500; Q-特殊化 2503-2510; cube step 2511-2512） | |abc| = ||abc||_C ≤ 24·max{exp(1.7·10^30·ε^(−166/81)), rad(abc)^{3(1+ε)}} ≤ 24·exp(...)·rad(abc)^{3(1+ε)} | ✔ 与论文 L2432-2433 一致（常数、双不等式） | missing: h_non/h_tor_non、H_L/Δ_L/rad_L、Claims 5.4A-C、cube step ✔ 准确 | explicitEstimatesThm54Shape（statement-only） | pending |
| explicitEstimatesThm54ShapeCard (L288) | Thm5.4 lines 2426-2443; intro ThmB lines 189-201; ThmA(ii) lines 184-188 | 冻结 explicitEstimatesThm54Shape | ✔ typed 公式与论文逐符号一致（见 §8.1） | present: typed statement（no proof）✔；missing 同上 ✔ | explicitEstimatesThm54Shape/ExpConstant/MaxBound | pending |
| step-4 cor312ToABCChainStepInterfaceToABCCard (L209) | IUTToABC.lean:29-43 (abcConjecture_iff_abcLogConjecture), :57-79 (abcConjecture_iff_abcArithmeticWeightHeightBound) | cor312ToABCTargetShape ↔ ABCConjecture | ✔ 等价所述正确；行号近似（实际声明 L36/L64，区间包含声明行） | present: cor312ToABCTargetShape_iff_abcConjecture（reuse 已接受等价）✔；unchanged: cor312ToABCBridge obligation ✔ | IUTToABC.abcConjecture_iff_abcArithmeticWeightHeightBound | interface |

### 8.1 typed shape 与论文 Thm 5.4 的符号级核对

- Lean `explicitEstimatesThm54ExpConstant ε := Real.exp (1.7e30 * ε ^ (-(166/81:ℝ)))` ↔ 论文 exp(1.7·10^30·ε^(−166/81)) ✔（1.7e30 字面量精确；幂指数 166/81 与论文一致）。
- Lean `explicitEstimatesThm54MaxBound rad ε := 24 * max (exp...) ((rad:ℝ)^(3*(1+ε)))` ↔ 论文 24·max{exp(...), rad(abc)^{3(1+ε)}} ✔。
- Lean `explicitEstimatesThm54Shape`: ∀a b c:ℤ, 非零、pairwise IsCoprime、a+b+c=0、∀ε, 0<ε→ε≤1 → ((a*b*c).natAbs:ℝ) ≤ maxBound (radical ((a*b*c).natAbs)) ε ∧ maxBound ≤ 24*(exp ε * ((radical ...:ℝ)^(3*(1+ε)))) ↔ 论文 |abc| = ||abc||_C ≤ 24·max{...} ≤ 24·exp(...)·rad^{3(1+ε)} ✔（ℤ/natAbs/radical 翻译在 docstring 中已声明）。
- 结论: typed shape 忠实；缺 proof（Claims 5.4A-C、Q-specialization、cube step）与 h_non/H_L/Δ_L/rad_L/h_tor_non 对象。

### 8.2 card 文本过时项（审计发现，仅报告）

- `explicitEstimatesProp22Obligation` note 说 "no explicit PNT bound and no theta/Chebyshev layer exist in this repository"——**已被 Section2 green 证明推翻**（有 4/3 常数层的显式 Chebyshev/PNT 界）；应改为 "only weaker 4/3-constant forms exist; sharp 1.022/0.00071 constants absent"。
- step-1 machineStatus 的 "missing: arithmetic divisor/degree layer of [IUTchIV] Definition 1.9"——**部分过时**（ArithmeticDivisorDegree green 已有 deg/ndeg/eDegree/pullback）；缺的是 q-除子特化与 U_X 层。
- step-2 machineStatus 的 "missing: explicit PNT estimates"——同上，应改为 "only 4/3 weak forms present (Section2)"。
- 卡片本身的行号引用与结论转录未发现错误；cards registry 的 status（4 pending + 1 interface）与文件一致。

## 9. [ExpEst] 论文 §0–§5 → LANA 参考映射（reference-only，A489；不进 priority）

说明: LANA 在外部仓库 `tmp/dsh-oct6-openai-math-survey-20261016/repos/lana/`；已移植到 `tmp/sheaf/lana/<pkg>/...` 的仅 11 个包（1,046 条队列，watchdog 有空消化）；`iut` 与 `Iut4Sec1` 两个包**尚未移植**（184 条路径待补，lattice）。LANA 只作参考，不作为我们文件/优先级的依赖。

| 论文节 | 主要内容/主要结果 | LANA 对应文件/decls | 移植/编译状态 | 备注 |
|---|---|---|---|---|
| §0 Notations & Conventions (L390-444) | X=P1_Q, D={0,1,∞}, Legendre/λ-line, (Mell)_Q, U_X, heights/absolute values 约定 | genl (Genl.Curves.Theory: Ω, Curve, tripod_K, tripod_D, lam_transcendental); heights (Heights.Absolute/Basic 等); Iut/Tripod/Basic (Qbar, Pt, ptLE/ptEQ) | genl(8)/heights(56) 已移植并入队；Iut 未移植 | 参考: tripod/Pt 层与我们的 Legendre/点数层可对照 |
| §1 Heights (L445-1057) | toric heights Lemma 1.3; J(α) Lemma 1.5/1.6; Prop 1.8/1.9/1.10/1.12 高度比较; Lemma 1.11 线性化; Cor 1.14 h_non 上界 | genl (Genl.GeneralPosition.TheoremTwoOne/HeightTheory/BoundedDiscrepancy —— GenEll Thm 2.1); heights (Different/*, Curve/{CondDivisor,CondHeight,DivisorHeight,Northcott} 等); Iut/Tripod/{Height,LogCond,GeneralPosition,Northcott} | genl/heights 已移植入队；Iut/Tripod 未移植 | [ExpEst] §1 的核心是 GenEll The 2.1+高度比较；我们的 own 文件只有 Height.logHeight₁/算术除子层，未做这些比较 |
| §2 Auxiliary Numerical Results (L1058-1123) | Prop 2.1 j-invariants of arithmetic elliptic curves; Prop 2.2 explicit PNT (1.022 / 0.00071 / 1.00072) | Iut/Implication/ChebyshevExplicit (ChebyshevHyp/ChebyshevUpperHyp/PrimeCountingHyp/chebyshevBoundExplicit/primeCountingHyp_holds); Iut/Implication/{PrimeSelection,Invariants} | Iut 未移植（184 待补）；外部 ChebyshevExplicit 已 proved 但常数 log4/3/2 级，非论文 1.022 | 我们树内 Section2（4/3 常数）已覆盖 Prop 2.2 的弱形式；sharp 常数为真正缺口 |
| §3 μ6-Theory for [EtTh] (L1124-1311) | Lemma 3.1 单位根群作用; Prop 3.2 12 次单位根处 theta 值; Def 3.3/3.4/3.5 标准型 theta/评估点修改 | tate-curves-theta (78 files: Kummer/{ThetaValues,ThetaGerm}, QParameter/*, Converse/Tate*, Analysis/*); Iut/EtaleTheta (LANA IUT II 对应) | tate-curves-theta 已移植入队（79）；Iut/EtaleTheta 未移植 | 参考: 6-torsion/12th-root theta 值层；我们 own 仓库有 EtTh 相关资产（Mzk1EtTh*）但非 μ6 版本 |
| §4 μ6-Theory for [IUTchI-III] (L1312-1607) | Def 4.1 μ6-initial Θ-data; Thm 4.2（μ6 版 Cor 3.12 路线）; Remark 4.2.6 | Iut/Cor312/{Statement,Container,ContainerHull,HolomorphicHull,LogVolume,PacketPresentation,Procession,RationalPlace,LeftHandSide,RightHandSide}; Iut/Wall/{BPS,Constraints,Pilots,QPilotRegion,Scaling,Ind3,MultiContainer}; Iut/{HodgeTheater,Frobenioid,ThetaLink,LogLink,Tower,Torsion,Multiradial,Anabelian,Reconstruction} | Iut 包未移植（184 待补）；源文件在原仓库可用 | 参考: Cor312Variant/Container/Hull/LogVolume 与我们的 R3/R4 组装链可对照；LANA 的 Cor312Variant 是 hypothesis（assumed），不是证明 |
| §5 μ6-Theory for [IUTchIV] (L1608-2565) | Thm 5.1 log-volume estimates; Cor 5.2 构造 suitable μ6-initial Θ-data + (C1)(C2); Thm 5.3 effective ABC/Szpiro; Thm 5.4 effective Szpiro; Cor 5.8/5.9 FLT apps | Iut/Implication/{LogVolumeBound(globalVol_thetaHull_le/rhs_le),Theorem110(theorem110/assembly),Corollary22(Corollary22Inputs/ThetaDataExistence/c2),Corollary23(statementII_of_cor312),PrimeSelection(exists_prime_selection),Invariants(Theorem110Invariants)}; Iut/Tripod/{Main(abc_of_variant),ClassicalAbc(classicalABC_of_statementI),GeneralPosition,Height,LogCond}; Iut/Abc/{Classical,FormalConjectures,Target}; Iut/MainTheorem.classicalABC_of_variant | Iut 未移植；Iut4Sec1（6 文件）也未移植 | LANA formalization.yaml 明确: MainTheorem = Cor312Variant ⇒ classical ABC（经 IUT IV Thm1.10/Cor2.2/2.3 + GenEll Thm2.1），**不形式化 [ExpEst] 论文本身**；Cor 5.2 的显式常数层（δ/κlog/h_d/Exc）在 LANA 也未见到 typed |

补充: Iut4Sec1 包（6 文件: Combinatorics/{RangeAverages,WeightedAverage}、Global/{ArithmeticDivisor,Pullback}、LocalField/Basic、Real/LogError）对应 IUT IV §1 的自足数学（log-volume estimates），是 LANA 对我们以前 Def 1.9/Prop 1.1-1.4 层的完整版；未移植。LANA Tripod/{Height,LogCond,ClassicalAbc} 有 logDiff/logCond/logHeight 的成熟对象层，可作为我们 (C2) object 层的参考（reference-only）。

## 10. A489 结论与优先级（own-file 为主，LANA 仅参考）

1. **own 文件现状**: ExpEst02 Class A（e1-e6）全部 green；ExpEst02 Class B（B1/B2/B3）**登记过时**——三个形状均已被树内 Section2 green 定理覆盖（弱常数 4/3）；真正 Class B 只剩论文 sharp 常数 1.022/0.00071/1.00072。
2. **Cor312ToABCCards**: 5 卡的行号引用与结论转录正确；typed Thm5.4 shape 符号级忠实；但 machineStatus/Prop2.2 obligation 文本因 Section2/ArithmeticDivisorDegree 新 green 而部分过时，建议 owner 更新（不改代码前提下只需改字符串/obligation note）。
3. **真正缺口（own，按优先级）**: P1 typed Thm 5.3(i)/(ii) 与对象（h_non/H_L/Δ_L/rad_L/h_tor_non + h_d(ε)）；P2 Cor 5.2 的 δ/κlog/h_d/Exc 与 (C1)(C2) 对象（可参考 LANA Iut4Sec1/Tripod 与我们的 ArithmeticDivisorDegree/Different*）；P3 Thm 5.4 证明（Claims 5.4A-C、cube step）；P4 Prop 2.2 sharp 常数（Class B；LANA ChebyshevExplicit 也不含 1.022，需独立）。
4. **LANA 参考价值**: §1 heights/GenEll（genl）、§3 EtTh（tate-curves-theta）、§4 Cor312/Wall（iut）、§5 Theorem110/Corollary22/23/MainTheorem/Tripod（iut）、Iut4Sec1（IUT IV §1 完整版）；但 iut/Iut4Sec1 尚未移植（184 待补），已移植包按 A489 只排 watchdog 空闲消化，**不进 priority、不阻塞我们文件**。
5. 本扩展只读；未修改 ExpEst02/Cor312ToABCCards 或其它文件，未改队列、未碰 watchdog、未手动编译。
