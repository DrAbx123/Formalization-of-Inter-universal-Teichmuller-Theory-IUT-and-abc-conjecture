import { appendFileSync } from 'node:fs';
const ROOT='D:/lean';
const L=[];
const rows=[
['19','H5 O^x stabilization / hull<=image-volume','Hull09H5GapsActual::hull09_scalingUnits_subset_hull / hull09_hull_eq_closure / hull09DetTensorBookkeeping_exponent; CardHullRealGeometryReduction','paper:EXIT0','e-deep:E2.H5framing (PROVED); e-deep:E2.h5Gap (NAMED)','条件/命名'],
['20','H6 geometric core precise','未找到 Mzk1GeometricCorePrecise* 文件；相邻 Hull11H6Mzk1UpgradeActual / Hull11PreciseConsumerActual（EXIT0）','paper:EXIT0 (相邻)','e-deep:E1.absTopIII05Inputs (NAMED); foundation:HOLD.binding (NAMED)','缺口/命名'],
['21','H7/Ob9 two-sided arbitrary-iterate','Hull12Ob9BoundTransferActual::hull12_upperBound_transfer（one-sided）; Hull13TwoSidedBoundActual::hull13_twoSided_bound / HullH7Ob9TwoSidedInputs','paper:EXIT0','e-deep:E3.oneSided (PROVED); E3.twoSided (PROVED); E3.deepOb9 (NAMED)','条件/命名'],
['22','GenEll（一般椭圆）结果','paper GenEll00-GenEll17Actual（statement layer citable）；GenEll10b H6 wiring','paper:EXIT0','E-hull-h5-h7 相关节点（TREE_ASSET/CONDITIONAL）','部分'],
['23','Belyi / Lemma 2.x 输入','Mzk1 bottom B1-B5（CITABLE）; LayerAAlgebraicInductionActual::AlgebraicNestedInductionInput (NAMED)','paper:EXIT0+probe','B1-fold / B5-lemma23-moebius (PROVED); N2-alg-nested (NAMED)','已证(有理层)/命名(Qbar)'],
['24','IUT IV Theorem 1.10 display','S3171IUTIVSection1DisplayActual::thm110_final_display','paper:EXIT0','e-deep:E5.display (PROVED)','条件'],
['25','IUT IV Section 2 估计','IUTIV/Section2.lean; ArithmeticDivisorDegree.lean::deg_pullback; StepV*/Different*/Archimedean*','tree:olean_fresh','T4-iut4-arithmetic-degree (TREE_ASSET)','树资产'],
['26','Cor 3.12 target <=> S2717 upper gap','S2717Cor312FullTargetActual::S2717UpperGap / PaperCor312Full / S2717_full_iff_hupper','paper:no-EXIT0 (待重编)','e-deep:E5.s2717 (CONDITIONAL)','条件'],
['27','(b)/(c) 比较输入（undilated height/region）','Cor312ToABCBridgeInterface.lean::height_le_normalizedRegionVolume（named 字段）、regionVolume_le_normalizedWeight','tree:olean_fresh','e-deep:E5.comparisonGaps (NAMED); T1-cor312-abc-bridge (CONDITIONAL)','命名'],
['28','Theorem 3.11 source assembly','Theorem311/SourceTheorem311Assembly.lean::SourceTheorem311Layers / assemble / t1_recovered / t2 / t3 / output_recovered; paper Mzk1PaperTheorem311AssemblyStatementActual::SourceP1P2Bundle/H1H2Hypotheses/LGPCompatibility','tree:olean_fresh; paper:no-EXIT0 (statement 待重编)','iut-skeleton:Thm311 (CONDITIONAL); routes:theorem311_assembly (CONDITIONAL)','条件'],
['29','Cor 3.12 结论/合同陈述 (CTheta >= -1)','Corollary312/Comparison.lean::cor312Conclusion_of_contract; StepXI/Contract.lean::StepXIContract / q_positive_of_constructed_stepXI','tree:olean_fresh; index_fresh','iutiii:IUTIII.COR312.TARGET (CONDITIONAL); iut-skeleton:Cor312 (CONDITIONAL)','条件'],
['30','Cor 3.12 -> ABC bridge / height bound','Cor312ToABCBridgeInterface.lean::cor312ToABCBridge_abcConjecture / cor312ToABCBridge_heightBound / heightWeightBound_of_normalizedVolumeComparison','tree:olean_fresh','T1-cor312-abc-bridge (CONDITIONAL, 条件定理已证)','条件'],
['31','ABCFrontier / ABC 等价形式','ABCBridge/Bridge/ABCFrontier.lean::abcConjecture_of_frontier / abcFrontier_iff_abcConjecture; ABCBridge/Arithmetic/ABCHeightArithmeticWeightComparison.lean','tree:olean_fresh','T3-abc-frontier (CONDITIONAL; 部分 frontier 路线被 refute 记录)','条件/部分refuted'],
['32','ABCConjecture 最终目标','ABCBridge/Statement.lean::ABCConjecture','tree:olean_fresh','T0-abc-target (DEF)','定义'],
['33','Section 0 对象 (countably ordered/oriented graph/path pairs)','paper Mzk1Section0*Actual（约20 files, mixed EXIT0）','paper:EXIT0','iut-pre-abc:Section0.* / e-deep Section0 节点 (TREE_ASSET/PROVED/CONDITIONAL)','部分'],
['34','Sources 1995-2015（外部定理输入）','无 Lean 声明（外部定理）','—','iut-skeleton:Sources1995_2015 (NAMED)','命名(外部)'],
['35','Formalization Stage 1-5 / 四三角形','文档级（paper Formalization of IUT lines 116-125/443-621）；Lean 无直接对象','—','routes fragment 相关节点 (CONDITIONAL)','文档级']
];
for(const r of rows) L.push('| '+r.join(' | ')+' |');
L.push('');
L.push('## 3. 覆盖统计与结论');
L.push('');
L.push('- 审计对象: 35 个（IUT 3.12 陈述 + Theorem 3.11 装置 + 外部/深输入 + IUT IV/ABC 链）。');
L.push('- 有现有 Lean 资产可复用: 31 个（树 olean_fresh 或 paper EXIT0/CITABLE；其中 26 个有明确 Lean 声明名，5 个仅文件级）。');
L.push('- 有现有 DAG 节点可直接复用/挂边: 30 个（iut-skeleton / iut-pre-* / iutiii / e-deep / T0-T4 / B1-B5 等）；5 个无专用节点（#1 Theta-pilot 对象层、#10 标签识别、#11 q-参数、#20 H6 precise、#34 Sources1995 仅命名）。');
L.push('- 真缺口（对象级/无 Lean 声明）: 5 个 —— #10 标签识别 (IUT II Cor 4.10(i))、#1 Theta-pilot Def 3.8(i) 对象层、#11 q-参数 Def 3.1(b)、#20 H6 geometric core precise、#34 Sources1995-2015（外部命名，按设计不形式化）。');
L.push('- 深输入命名（已有节点但证明为 named）: AbsTopIII05 deep (#18)、H5 O^x (#19)、H7/Ob9 both-sided (#21)、EtTh02/EtTh11 deep (#16)、GenEll Thm2.1(ii)=>(i) consumer (#22)、(b)/(c) 比较 (#27)、AlgebraicNestedInductionInput (#23) —— 合计 7 条。');
L.push('');
L.push('## 4. fragment 语义重叠 / 去重建议');
L.push('');
L.push('- Cor 3.12 陈述: iut-skeleton:Cor312 / iut-pre-mainline:T3 / iut-pre-abc:IUT312.statement → 建议以 iutiii:IUTIII.COR312.TARGET（已有 tree 声明）为 canonical，其余改为引用边。');
L.push('- Theorem 3.11: iut-skeleton:Thm311 / iut-pre-mainline:T4 + D11 + L11 / routes:theorem311_assembly → canonical iut-skeleton:Thm311 或 tree SourceTheorem311Assembly 节点。');
L.push('- q-pilot: iut-skeleton:QPilot / iut-pre-abc:QPilot → 保留一个，另一个改为引用边。');
L.push('- H5: e-deep:E2.H5framing + e-deep:E2.h5Gap + mainline N8 部分重叠 → 保留 E2.* 为 canonical。');
L.push('- H7/Ob9: e-deep:E3.oneSided/twoSided/deepOb9 + mainline N8 → 保留 E3.*。');
L.push('- Hodge/Frobenioid/PrimeStrips/InitialTheta/LogShell/Kummer/ThetaLink/Section0: iut-skeleton 的 def 节点 vs iut-pre-abc 细粒度节点 → 建议 iut-skeleton 节点改为 statement 引用（挂边到 pre-abc 细节点），不重复定义。');
L.push('- T0-T6/D1-D21/L1-L12/N1-N10（iut-pre-mainline）与 iut-skeleton:TargetABC/Cor312/Thm311/Ind1-3/H5/H7Ob9/QPilot/IUT4Estimates 重叠 → skeleton 保留语义层、mainline 为分解层，用 edge 连接不重复声明。');
L.push('');
L.push('## 5. 证据质量与下一步（不建节点，仅建议）');
L.push('');
L.push('- iut-skeleton 全部边 evidence=planned → 复用/挂边前先填 observed_source（可用 dag/THEOREM-DAG.md 的 Lean 声明映射 + route index 的 file/decl 证据）。');
L.push('- iut-pre-abc / pre-stepxi 节点 declarations 基本为空 → 需从现有树/paper 声明填充（本 survey 第 2 节已给出候选文件::声明）。');
L.push('- iut-pre-mainline 快照为空（并发写窗口）→ 迁移完成后需重跑本审计统计。');
L.push('- 真缺口对象先复用现有 tree/paper 资产挂边；仅在缺对象层时新建节点（A470/A471），且新边标 evidence。');
L.push('');
L.push('## 6. 一句话结论');
L.push('');
L.push('覆盖 35 个 IUT 3.12 前置对象；31 个已有 Lean 资产可复用、30 个已有 DAG 节点可挂边复用；5 个真缺口（标签识别、Theta-pilot Def3.8(i) 对象层、q-参数 Def3.1(b)、H6 precise、Sources1995 外部命名），另有 7 条深输入 named 依赖；证据缺口集中在 iut-skeleton 全 planned 边与 pre-abc/pre-stepxi 空 declarations。');
L.push('');
appendFileSync(ROOT+'/coord/SURVEY-shehdd.md', L.join('\n')+'\n');
console.log('chunk4 ok');
