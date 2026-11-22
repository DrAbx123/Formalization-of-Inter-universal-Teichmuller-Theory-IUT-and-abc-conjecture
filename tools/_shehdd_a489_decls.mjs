import { readFileSync, existsSync, readdirSync } from 'node:fs';
const ROOT='D:/lean';
const base=ROOT+'/tmp/dsh-oct6-openai-math-survey-20261016/repos/lana/iut/iut-main';
const groups={
 'Iut4Sec1':['Real/LogError','Global/ArithmeticDivisor','Global/Pullback','LocalField/Basic','Combinatorics/WeightedAverage','Combinatorics/RangeAverages'],
 'Implication':['Theorem110','LogVolumeBound','Corollary22','Corollary23','PrimeSelection','Invariants'],
 'Tripod':['Basic','Main','Height','LogCond','ClassicalAbc','GeneralPosition','Providers','Northcott'],
 'Cor312':['Statement','Container','ContainerHull','HolomorphicHull','LogVolume','PacketPresentation','Procession','RationalPlace','LeftHandSide','RightHandSide'],
 'Abc':['Classical','FormalConjectures','Target','P24Table'],
 'Wall':['BPS','Constraints','Pilots','QPilotRegion','Scaling','Ind3','MultiContainer'],
 'MainTheorem':['MainTheorem']
};
for(const [g,files] of Object.entries(groups)){
  console.log('===== '+g);
  for(const f of files){
    const p=base+'/'+(g==='Iut4Sec1'?'Iut4Sec1/':(g==='MainTheorem'?'Iut/':'Iut/'+g+'/'))+f+'.lean';
    if(!existsSync(p)){ console.log('  '+f+' MISSING'); continue; }
    const t=readFileSync(p,'utf8').split('\n');
    const names=[];
    for(let i=0;i<t.length;i++){ if(/^(theorem|def|structure|abbrev|lemma) /.test(t[i])) names.push(t[i].trim().split(/\s/)[1]); }
    console.log('  '+f+' ('+names.length+'): '+names.slice(0,14).join(', '));
  }
}
