import { readFileSync, existsSync, statSync, readdirSync } from 'node:fs';
const ROOT='D:/lean';
const dag=JSON.parse(readFileSync(ROOT+'/dag/declaration-dag.json','utf8'));
const idx=JSON.parse(readFileSync(ROOT+'/coord/repo-route-index-data.json','utf8'));
const lines=readFileSync(ROOT+'/tmp/xif_guarded_results.log','utf8').split('\n');
const latest=(rel)=>{ for(let i=lines.length-1;i>=0;i--){ if(lines[i].includes('FILE='+rel)) return lines[i]; } return null; };
const paperFiles=new Set(readdirSync(ROOT+'/tmp/sheaf/xif/paper'));
const evidence=(f)=>{
  const src=ROOT+'/'+f; if(!existsSync(src)) return 'MISSING';
  if(f.startsWith('LeanFormal/')){
    const ole=ROOT+'/.lake/build/lib/lean/'+f.replace(/\.lean$/,'.olean');
    const fresh=existsSync(ole)&&statSync(ole).mtimeMs>=statSync(src).mtimeMs;
    const row=(idx.rows||[]).find(r=>r.file===f);
    return 'tree:'+(fresh?'olean_fresh':'olean_stale')+(row&&row.citable==='OLEAN_FRESH'?'/index_fresh':'');
  } else {
    const base=f.split('/').pop().replace(/\.lean$/,'');
    const probe=paperFiles.has(base+'ProbeActual.lean')||paperFiles.has('_Probe'+base+'.lean')||paperFiles.has(base.replace(/Actual$/,'')+'ProbeActual.lean');
    const lr=latest(f); const ex=lr&&lr.includes('EXIT=0');
    return 'paper:'+(ex?'EXIT0':'no-EXIT0')+(probe?'+probe':'');
  }
};
const ids=['e-deep:E2.hullClosureLaws','iut-skeleton:QPilot','iut-pre-abc:QPilot','iutiii:IUTIII.THM311.OUTPUT_ALGORITHM','iutiii:IUTIII.IND1','iutiii:IUTIII.HULL.CARD_GEOMETRY','iutiii:IUTIII.HULL.DET_LOG_VOLUME','iutiii:IUTIII.STEPXI.LOGSHELL_MUN','iut-pre-abc:FrobeniusPicture.graph','iut-pre-abc:HodgeTheater.family','e-deep:E4.example36','iut-pre-abc:PrimeStrips.FD','e-deep:iuti-source-def31-dual-alignment','iut-pre-abc:InitialTheta.data','e-deep:E4.etthConsumer','iut-skeleton:K1K2','e-deep:E1.absTopIII05Refined','e-deep:E1.absTopIII05Inputs','e-deep:E2.H5framing','e-deep:E2.h5Gap','e-deep:E3.oneSided','e-deep:E3.twoSided','e-deep:E3.deepOb9','B1-fold','B5-lemma23-moebius','e-deep:E5.display','T4-iut4-arithmetic-degree','e-deep:E5.s2717','e-deep:E5.comparisonGaps','iut-skeleton:Thm311','routes:theorem311_assembly','iutiii:IUTIII.COR312.TARGET','T1-cor312-abc-bridge','T3-abc-frontier','T0-abc-target','iut-pre-abc:Section0.paths','iut-skeleton:Sources1995_2015'];
for(const id of ids){ const n=dag.nodes.find(x=>x.id===id); if(!n){ console.log(id+' MISSING-NODE'); continue; }
  const ev=(n.files||[]).map(f=>f.split('/').pop()+':'+evidence(f)).join(' | ');
  const decls=[]; const d=n.declarations; if(d&&!Array.isArray(d)){ for(const [f,ds] of Object.entries(d)) for(const x of ds) decls.push(f.split('/').pop()+':'+x); }
  console.log(id+' ['+n.status+'] ev={'+ev+'} decls={'+decls.slice(0,2).join('; ')+'}');
}
// check geometric core precise file
const hits=[];
for(const f of paperFiles){ if(/GeometricCorePrecise|PreciseGeom/.test(f)) hits.push(f); }
console.log('GeometricCorePrecise files='+hits.join(','));
