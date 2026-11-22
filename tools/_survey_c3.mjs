import { appendFileSync } from 'node:fs';
const ROOT='D:/lean';
const L=[];
L.push('## 2. 论文前置对象 -> 现有资产对照表');
L.push('');
L.push('图例: 证据列 tree:olean_fresh = LeanFormal 树 olean 存在且不旧; index_fresh = route index 标 OLEAN_FRESH; paper:EXIT0 = tmp/xif_guarded_results.log 最新 EXIT=0; +probe = 存在 probe 文件; no-EXIT0 = 最新非 EXIT0。状态列: 已证/条件/命名/树资产/定义/缺口。');
L.push('');
L.push('| # | 论文对象（原文位置） | 现有 Lean 文件::声明 | 证据 | 现有 DAG 节点 id | 状态 |');
L.push('|---|---|---|---|---|---|');
const rows=[
['1','Theta-pilot 对象 (IUT III Def 3.8(i))','SourceArithmeticThetaPilotBridge.lean (tree); paper FlUnitsThetaPilotActionActual / Mzk1ThetaPilotPacketInterfaceActual','tree:olean_fresh; paper:EXIT0','无专用 Def 3.8(i) 节点（相邻 iut-pre-abc:QPilot=GAP）','缺口(对象层)'],
['2','q-pilot 对象 (Def 3.8(i)) + q-参数','Corollary312/ArithmeticQPilot{LogVolume,BaseChange,GlobalNormalization}.lean; TateQPilotJComparison.lean','tree:olean_fresh; index_fresh(部分)','iut-pre-abc:QPilot (GAP); iut-skeleton:QPilot (CONDITIONAL)','条件/树资产'],
['3','Multiradial representation (Thm 3.11(i))','Theorem311/Output/MultiradialAlgorithm.lean::multiradialAlgorithm (+Reduction, GeneralRouteNormalForm)','tree:olean_fresh; index_fresh','iutiii:IUTIII.THM311.OUTPUT_ALGORITHM (TREE_ASSET); iut-skeleton:Thm311 (CONDITIONAL)','树资产'],
['4','Indeterminacy Ind1','Theorem311/Indeterminacy/Ind1.lean::ind1 (+Ind1Reduction, Ind1QuotientTransport)','tree:olean_fresh; index_fresh','iutiii:IUTIII.IND1 (TREE_ASSET)','树资产'],
['5','Indeterminacy Ind2','Ind2.lean::ind2','tree:olean_fresh; index_fresh','iutiii:IUTIII.IND2 (TREE_ASSET)','树资产'],
['6','Indeterminacy Ind3','Ind3.lean::ind3','tree:olean_fresh; index_fresh','iutiii:IUTIII.IND3 (TREE_ASSET)','树资产'],
['7','possible images 的 holomorphic hull (Rmk 3.9.5(i))','HolomorphicHull/SourceHullCompactnessReduction.lean::IQHullLogVolumeInterface; CardHullRealGeometryReduction.lean::sourceScalingUnits_subset_sourceHolomorphicHull / sourceHolomorphicHull_eq_closure','tree:olean_fresh; index_fresh','iutiii:IUTIII.HULL.CARD_GEOMETRY (TREE_ASSET)','树资产'],
['8','procession-normalized mono-analytic log-volume (Rmk 3.1.1/Prop 3.9)','HolomorphicHull/HullDeterminantLogVolumeReduction.lean::HullDeterminantLogVolumeFrozenSpec / hullDeterminantLogVolumeFrozenSpec_holds / packetLogVolume_eq_matrixLogDet','tree:olean_fresh; index_fresh','iutiii:IUTIII.HULL.DET_LOG_VOLUME (TREE_ASSET)','树资产'],
['9','Kummer isomorphisms (Thm 3.11(ii))','StepXI/SourceLogShellMuNQuotientCarrier.lean::muNQuotient / muNQuotientMap / muNQuotientMap_ker; SourceLogShellAbsTopIIIBridge.lean::SourceLogShellInvariantImageIdentification','tree:olean_fresh','iutiii:IUTIII.STEPXI.LOGSHELL_MUN (TREE_ASSET); e-deep:E1.logShellBridge (TREE_ASSET)','树资产'],
['10','标签 0 / <F_l^#> 的识别 (IUT II Cor 4.10(i))','未找到直接声明（库内关键字无命中）；最接近 SourceLogShellAbsTopIIIBridge.lean::SourceLogShellInvariantImageIdentification','tree:olean_fresh','无','缺口'],
['11','q-参数 at v in V_bad (IUT I Def 3.1(b))','SourceDefinition31* 树 (SourceDefinition31RootLemmas / DualContractAlignment 等); ArithmeticQPilotBaseChange.lean','tree:olean_fresh','iut-pre-abc:QPilot 子定义 (arithmeticDivisor); e-deep:iuti-source-def31-dual-alignment','部分/缺口'],
['12','Hodge theater (IUT I)','HodgeTheater/HodgeTheaterCore.lean; SourceHodgeTheaterFamily.lean::theater_injective/link_*','tree:olean_fresh','iut-pre-abc:HodgeTheater.core (DEF) / family (TREE_ASSET); e-deep:iuti-source-def31-dual-alignment (TREE_ASSET)','树资产'],
['13','Frobenioid Example 3.6 模型 (IUT II)','Frobenioid/Example36* (141 files), 例 Example36TateUniformization.lean::concreteFiveTateParameter','tree:olean_fresh','e-deep:E4.example36 (TREE_ASSET); iut-pre-abc:Frobenioid.Example36 (TREE_ASSET)','树资产'],
['14','F/D prime-strips','PrimeStripsConstruction.lean; PrimeStripFrobenioidCategorySkeleton.lean','tree:olean_fresh; index_fresh','iut-pre-abc:PrimeStrips.FD (TREE_ASSET)','树资产'],
['15','Initial Theta data / Definition 3.1 clusters','InitialTheta/SourceInitialThetaData.lean; SourceDefinition31RootLemmas.lean; SourceDefinition31DualContractAlignment.lean::sourceDefinition31Arithmetic_spec','tree:olean_fresh; index_fresh','iut-pre-abc:InitialTheta.data (TREE_ASSET); e-deep:iuti-source-def31-dual-alignment','树资产'],
['16','Etale theta (EtTh) 套件','IUTII/EtaleThetaQuotient 树; paper EtTh00-EtTh13Actual（statement layer EXIT0）','tree:olean_fresh; paper:EXIT0','e-deep:E4.etthConsumer (PROVED); e-deep:E4.etthGap (NAMED)','条件/命名'],
['17','Kummer K1/K2 packets','Theorem311/SourceK1K2* (约20 files); SourceK1K2CardReduction.lean','tree:olean_fresh; index_fresh','iut-skeleton:K1K2 (CONDITIONAL)','条件'],
['18','AbsTopIII 输入 (Hodge-Arakelov/theta hull, Prop 5.8)','paper AbsTopIII01-AbsTopIII14Actual（01/03/07/08/09 gate 表 CITABLE）; AbsTopIII05RefinedActual::Prop58iLocalFieldReconstruction / Prop58iiLogShellReconstruction','paper:EXIT0; 部分 CITABLE','e-deep:E1.absTopIII05Refined (PROVED); e-deep:E1.absTopIII05Inputs (NAMED)','部分/命名']
];
for(const r of rows) L.push('| '+r.join(' | ')+' |');
L.push('');
appendFileSync(ROOT+'/coord/SURVEY-shehdd.md', L.join('\n')+'\n');
console.log('chunk3 ok rows='+rows.length);
