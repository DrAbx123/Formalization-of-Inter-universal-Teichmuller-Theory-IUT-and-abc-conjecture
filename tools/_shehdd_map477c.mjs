import { readFileSync } from 'node:fs';
const ROOT='D:/lean';
const d=JSON.parse(readFileSync(ROOT+'/dag/declaration-dag.json','utf8'));
const idx=JSON.parse(readFileSync(ROOT+'/dag/generated/declarations-index.json','utf8')).declarations;
const norm=(nm)=>nm.includes('.')?nm.split('.').pop():nm;
const declFile=new Map();
for(const e of idx){ if(e.name&&e.file){ const k=norm(e.name); if(!declFile.has(k)) declFile.set(k,e.file); } }
const declToNodes=new Map(), fileToNodes=new Map();
const add=(m,k,v)=>{ if(!m.has(k)) m.set(k,[]); m.get(k).push(v); };
for(const n of d.nodes){
  const decs=n.declarations; if(decs){ const lists=Array.isArray(decs)?decs:Object.values(decs); for(const l of lists){ if(!Array.isArray(l)) continue; for(const nm of l){ if(typeof nm!=='string') continue; add(declToNodes,norm(nm),n.id); add(declToNodes,nm,n.id); } } }
  for(const f of (n.files||[])) add(fileToNodes,f,n.id);
}
const areas=[
 ['Cor3.12',['StepXIContract','Cor312Conclusion','cor312_of_constructed_stepXI','q_positive_of_constructed_stepXI','Cor312Route','cor312Conclusion_of_contract','qPilotLogVolume','tateJInvariantLogVolume','qPilotLogVolume_eq_log_prime','qPilotLogVolume_pos','tateJInvariant_norm_mul_q_norm_one','StepXIFiniteCertificate','HullDeterminantLogVolumeFrozenSpec','hullDeterminantLogVolumeFrozenSpec_holds','packetLogVolume_tensorPower','sourceHullVolume_eq_imageVolume_iff']],
 ['Thm3.11',['ind1QuotientLift','PossibleImage','lowerClosure','logShellRayPresentation_univ_iff','k1BoundaryOf_negLogVolumeRayPresentation','labelWeight','NonzeroFiniteLabel']],
 ['Kummer',['SourceLogShellDatum','logShell_eq_invScaledPreLogShell','IQSpan','SourceLogShellInvariantImageIdentification','sourceLocalLogShellDatum','absoluteKummerMap_eq_one_iff','nthPowerSubgroup','absoluteKummerMapQuotient_injective','kummerRatioHom','kummerMap_eq_one_iff','exists_root_algebraicClosure','fixed_by_absoluteGalois_mem_base','possibleImage_subset_of_generator_mem','sourceThetaPilotIQPacket']],
 ['Hodge/Theta',['FrobeniusPictureGraphAut','chainTranslation','graphAut_eq_translation','ThetaQDisplacement','hodgeTheaterLink_displacement','thetaPacket_eq','SourcePlacePartition','sectionMap_injective','oddTheta','oddTheta_shift','oddThetaFraction_eval_unconditional','oddTheta_ne_zero_at_i','gaussExponent','realThetaValue','gaussianSquareSum_formula','toFiniteLabel','representative_toFl']],
 ['ABC',['ABCFrontier','bridgeInterface_of_frontier','abcConjecture_of_frontier','abcFrontier_iff_abcConjecture','Cor312ToABCBridgeInterface','cor312ToABCBridge_abcConjecture','cor312ToABCBridge_heightBound','ABCFreyJProductHeightCriterion','abcConjecture_iff_freyJProductHeightCriterion','not_FrontierHeightWeightClause','not_ABCFrontierGapReduced','ABCHeightWeightAdditiveBoundV2','abcConjecture_iff_ABCHeightWeightAdditiveBoundV2','ABCLogConjecture','abcLogBound_exists_iff_rpow_exists','radical_eq_natRadical','abcInvariantPolynomial_coprime_left','abcInvariantCancellation_le_256','abcJInvariant_den_radical_bounds','abcOddBadPrimeSupport','mem_abcOddBadPrimeSupport_iff','freyAbcTateCandidateQ_norm_lt_one','freyAbcTateCandidateQ_norm_le_invNine','freyAbcTateCandidateQ_arithmeticCertificate','freyWeierstrassCurve_discriminant','rationalFreyWeierstrassCurve_j_height_bounds','canonical_equation_coefficients','tateJInvariant_norm','tateParameterUnit','tateParameterUnit_ne_one','CurveIndexedTateUniformization','AllNTorsionRational','galoisActionOnPoint','galoisActionOnLTorsionLinearEquivHom','unitLog','unitLog_mul','exists_log1p_preimage','integers_subset_integralLogShell','natRadical_pos','unitNormLogDegree','FinitePlaceQCandidate']],
 ['paper',['abcConjecture_iff_tauCeti','toOldWitness','Mzk1GeometricCoreWitnessPrecise','genEll15GeometricCoreStatement_of_precise']]
];
const rowsMap=[], catA=[], catB=[]; let total=0, mapped=0;
const perArea={};
for(const [area,names] of areas){
  perArea[area]={t:0,m:0,a:0,b:0};
  for(const nm of names){
    total++; perArea[area].t++;
    const nodes=declToNodes.get(nm)||[];
    if(nodes.length){ mapped++; perArea[area].m++; rowsMap.push(area+' | '+nm+' -> '+[...new Set(nodes)].slice(0,3).join(',')); continue; }
    const file=declFile.get(nm)||'?';
    const fnodes=fileToNodes.get(file)||[];
    if(fnodes.length){ perArea[area].a++; catA.push(area+' | '+nm+' | '+file+' | covered-by '+[...new Set(fnodes)].slice(0,2).join(',')); }
    else { perArea[area].b++; catB.push(area+' | '+nm+' | '+file); }
  }
}
console.log('TOTAL='+total+' MAPPED='+mapped+' CAT_A='+catA.length+' CAT_B='+catB.length);
for(const [a,v] of Object.entries(perArea)) console.log('AREA '+a+': mapped='+v.m+' fileCovered='+v.a+' unreferenced='+v.b+' /'+v.t);
console.log('--- CAT_B (资产文件未被任何 DAG 节点引用) ---'); for(const r of catB) console.log(r);
console.log('--- CAT_A (文件已被节点引用, 声明名未登记) ---'); for(const r of catA) console.log(r);
