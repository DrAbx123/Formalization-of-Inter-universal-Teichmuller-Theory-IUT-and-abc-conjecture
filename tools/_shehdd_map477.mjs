import { readFileSync } from 'node:fs';
const ROOT='D:/lean';
const d=JSON.parse(readFileSync(ROOT+'/dag/declaration-dag.json','utf8'));
const idx=JSON.parse(readFileSync(ROOT+'/dag/generated/declarations-index.json','utf8')).declarations;
// decl -> node ids from DAG declarations fields
const declToNodes=new Map();
for(const n of d.nodes){
  const decs=n.declarations; if(!decs) continue;
  const lists = Array.isArray(decs)?decs:Object.values(decs);
  for(const list of lists){ if(!Array.isArray(list)) continue; for(const nm of list){ if(typeof nm!=='string') continue; if(!declToNodes.has(nm)) declToNodes.set(nm,[]); declToNodes.get(nm).push(n.id); } }
}
const assets=[
 ['StepXIContract','Cor3.12'],['Cor312Conclusion','Cor3.12'],['cor312_of_constructed_stepXI','Cor3.12'],['q_positive_of_constructed_stepXI','Cor3.12'],['Cor312Route','Cor3.12'],['cor312Conclusion_of_contract','Cor3.12'],
 ['qPilotLogVolume','Cor3.12'],['tateJInvariantLogVolume','Cor3.12'],['qPilotLogVolume_eq_log_prime','Cor3.12'],['qPilotLogVolume_pos','Cor3.12'],['tateJInvariant_norm_mul_q_norm_one','Cor3.12'],
 ['StepXIFiniteCertificate','Cor3.12'],['HullDeterminantLogVolumeFrozenSpec','Cor3.12'],['hullDeterminantLogVolumeFrozenSpec_holds','Cor3.12'],['packetLogVolume_tensorPower','Cor3.12'],['sourceHullVolume_eq_imageVolume_iff','Cor3.12'],
 ['ind1QuotientLift','Thm3.11'],['PossibleImage','Thm3.11'],['lowerClosure','Thm3.11'],['logShellRayPresentation_univ_iff','Thm3.11'],['k1BoundaryOf_negLogVolumeRayPresentation','Thm3.11'],['labelWeight','Thm3.11'],['NonzeroFiniteLabel','Thm3.11'],
 ['SourceLogShellDatum','Kummer'],['logShell_eq_invScaledPreLogShell','Kummer'],['IQSpan','Kummer'],['SourceLogShellInvariantImageIdentification','Kummer'],['sourceLocalLogShellDatum','Kummer'],['absoluteKummerMap_eq_one_iff','Kummer'],['nthPowerSubgroup','Kummer'],['absoluteKummerMapQuotient_injective','Kummer'],['kummerRatioHom','Kummer'],['kummerMap_eq_one_iff','Kummer'],['exists_root_algebraicClosure','Kummer'],['fixed_by_absoluteGalois_mem_base','Kummer'],['possibleImage_subset_of_generator_mem','Kummer'],['sourceThetaPilotIQPacket','Kummer'],
 ['FrobeniusPictureGraphAut','Hodge/Theta'],['chainTranslation','Hodge/Theta'],['graphAut_eq_translation','Hodge/Theta'],['ThetaQDisplacement','Hodge/Theta'],['hodgeTheaterLink_displacement','Hodge/Theta'],['thetaPacket_eq','Hodge/Theta'],['SourcePlacePartition','Hodge/Theta'],['sectionMap_injective','Hodge/Theta'],['oddTheta','Hodge/Theta'],['oddTheta_shift','Hodge/Theta'],['oddThetaFraction_eval_unconditional','Hodge/Theta'],['oddTheta_ne_zero_at_i','Hodge/Theta'],['gaussExponent','Hodge/Theta'],['realThetaValue','Hodge/Theta'],['gaussianSquareSum_formula','Hodge/Theta'],['toFiniteLabel','Hodge/Theta'],['representative_toFl','Hodge/Theta'],
 ['ABCFrontier','ABC'],['bridgeInterface_of_frontier','ABC'],['abcConjecture_of_frontier','ABC'],['abcFrontier_iff_abcConjecture','ABC'],['Cor312ToABCBridgeInterface','ABC'],['cor312ToABCBridge_abcConjecture','ABC'],['cor312ToABCBridge_heightBound','ABC'],['ABCFreyJProductHeightCriterion','ABC'],['abcConjecture_iff_freyJProductHeightCriterion','ABC'],['not_FrontierHeightWeightClause','ABC'],['not_ABCFrontierGapReduced','ABC'],['ABCHeightWeightAdditiveBoundV2','ABC'],['abcConjecture_iff_ABCHeightWeightAdditiveBoundV2','ABC'],['ABCLogConjecture','ABC'],['abcLogBound_exists_iff_rpow_exists','ABC'],['radical_eq_natRadical','ABC'],['abcInvariantPolynomial_coprime_left','ABC'],['abcInvariantCancellation_le_256','ABC'],['abcJInvariant_den_radical_bounds','ABC'],['abcOddBadPrimeSupport','ABC'],['mem_abcOddBadPrimeSupport_iff','ABC'],['freyAbcTateCandidateQ_norm_lt_one','ABC'],['freyAbcTateCandidateQ_norm_le_invNine','ABC'],['freyAbcTateCandidateQ_arithmeticCertificate','ABC'],['freyWeierstrassCurve_discriminant','ABC'],['rationalFreyWeierstrassCurve_j_height_bounds','ABC'],['canonical_equation_coefficients','ABC'],['tateJInvariant_norm','ABC'],['tateParameterUnit','ABC'],['tateParameterUnit_ne_one','ABC'],['CurveIndexedTateUniformization','ABC'],['AllNTorsionRational','ABC'],['galoisActionOnPoint','ABC'],['galoisActionOnLTorsionLinearEquivHom','ABC'],['unitLog','ABC'],['unitLog_mul','ABC'],['exists_log1p_preimage','ABC'],['integers_subset_integralLogShell','ABC'],['natRadical_pos','ABC'],['unitNormLogDegree','ABC'],['FinitePlaceQCandidate','ABC'],
 ['abcConjecture_iff_tauCeti','paper'],['toOldWitness','paper'],['Mzk1GeometricCoreWitnessPrecise','paper'],['genEll15GeometricCoreStatement_of_precise','paper']
];
let mapped=0; const unmapped=[];
for(const [nm,area] of assets){
  const nodes=declToNodes.get(nm)||[];
  if(nodes.length) mapped++; else unmapped.push(area+' :: '+nm);
}
console.log('DAG total nodes='+d.nodes.length+' myarea-nodes='+d.nodes.filter(n=>n.id&&(n.id.startsWith('shehdd:')||n.id.startsWith('iutiii:')||n.id.startsWith('iut-pre-abc:')||n.id.startsWith('iut-skeleton:')||n.id.startsWith('e-deep:')||n.id.startsWith('mainline:')||n.id.startsWith('T'))).length);
console.log('ASSETS TOTAL='+assets.length+' MAPPED='+mapped+' UNMAPPED='+unmapped.length);
console.log('UNMAPPED LIST:'); for(const u of unmapped) console.log('  - '+u);
// per-area stats
const byArea={}; for(const [nm,area] of assets){ const nodes=declToNodes.get(nm)||[]; byArea[area]=byArea[area]||{t:0,m:0}; byArea[area].t++; if(nodes.length) byArea[area].m++; }
for(const [a,v] of Object.entries(byArea)) console.log('AREA '+a+': '+v.m+'/'+v.t+' mapped');
// which DAG nodes reference my-area files
const mineFiles=['tmp/sheaf/xif/paper/Shehdd','LeanFormal/IUT/IUTIII/Corollary312','LeanFormal/IUT/IUTII/Kummer','LeanFormal/IUT/ABCBridge/Geometry','LeanFormal/IUT/ABCBridge/Arithmetic'];
let ref=0; const refNodes=[];
for(const n of d.nodes){ const fs=(n.files||[]).join('|'); if(mineFiles.some(m=>fs.includes(m))){ ref++; if(refNodes.length<10) refNodes.push(n.id); } }
console.log('DAG nodes referencing my-area files='+ref+' e.g. '+refNodes.join(', '));
